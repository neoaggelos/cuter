-module(cuter_taint_annotation).
-export([annotate_taint/1, annotate_taint/2, get_taint/1, get_taint_anno/1]).
-export_type([taint/0, symbol_table/0]).

-type taint() :: atom().
-type symbol_table() :: dict:dict().
-type module_defs() :: [{cerl:cerl(), cerl:cerl()}].

%% annotating function

-spec annotate_taint(cerl:cerl()) -> cerl:cerl().
annotate_taint(T) ->
  io:format("~p~n", [T]),
  Defs = cerl:module_defs(T),
  ST = dict:new(),
  NewDefs = annotate_taint_functions(Defs, ST),
  cerl:update_c_module(T, cerl:module_name(T), cerl:module_exports(T), cerl:module_attrs(T), NewDefs).

-spec annotate_taint_functions(module_defs(), symbol_table()) -> module_defs().
annotate_taint_functions(Funs, ST) ->
  {NewST, NewFuns, Change} = annotate_taint_functions(Funs, ST, [], false),
  case Change of
    true ->
      annotate_taint_functions(NewFuns, NewST);
    false ->
      NewFuns
  end.

-spec annotate_taint_functions(module_defs(), symbol_table(), module_defs(), atom()) -> {symbol_table(), module_defs(), atom()}.
annotate_taint_functions([], ST, Acc, Change) ->
  {ST, Acc, Change};
annotate_taint_functions([{Var, Fun}|T], ST, Acc, Change) ->
  {Annotated, C} = annotate_taint(Fun, ST),
  NewST = dict:store(cerl:var_name(Var), {get_taint(Annotated), 'fun'}, ST),
  annotate_taint_functions(T, NewST, [{Var, Annotated}|Acc], Change or C).
  
-spec update_ann(cerl:cerl(), taint()) -> cerl:cerl().
update_ann(T, Taint) ->
  Anno = cerl:get_ann(T),
  cerl:set_ann(T, update_ann(Anno, Taint, [], false)).

-spec update_ann([any()], taint(), [any()], atom()) -> [any()].
update_ann([], Taint, Acc, false) -> [{tainted, Taint}|Acc];
update_ann([], _, Acc, true) -> Acc; 
update_ann([{tainted, _}|T], Taint, Acc, _) -> update_ann(T, Taint, [{tainted, Taint}|Acc], true); 
update_ann([H|T], Taint, Acc, Found) -> update_ann(T, Taint, [H|Acc], Found).
  
-spec put_vars(symbol_table(), [{taint(), atom()}], [cerl:cerl()]) -> symbol_table().
put_vars(Vars, Flags, SM) ->
  lists:foldl(fun({Var, Flag}, B) -> dict:store(cerl:var_name(Var), Flag, B) end, SM, lists:zip(Vars, Flags)).

-spec annotate_taint(cerl:cerl(), symbol_table()) -> {cerl:cerl(), atom()}.
annotate_taint(Tree, SM) ->
  CurTaint = get_taint(Tree),
  case cerl:type(Tree) of
%    alias ->
    'apply' ->
      Op = cerl:apply_op(Tree),
      {Op1, C1} = case cerl:type(Op) of
		   var ->
		     case dict:find(cerl:var_name(Op), SM) of
		       {ok, {Value, 'fun'}} ->
			 {update_ann(Op, Value), Value =/= CurTaint};
		       _ ->
			 {update_ann(Op, true), true =/= CurTaint}
		     end;
		   _ ->
		      io:format("unhandled op")
		 end,
      {Args, C2} = annotate_taint_all(cerl:apply_args(Tree), SM),
      NewTaint = get_taint(Op1) or get_all_taint(Args),
      {cerl:update_c_apply(update_ann(Tree, NewTaint), Op1, Args), C1 or C2};
%    binary ->
%    bitstr ->
    call ->
      Mod = cerl:call_module(Tree),
      Name = cerl:call_name(Tree),
      {NewAnn, C1} = case cerl:is_literal(Mod) andalso cerl:is_literal(Mod) of
		      true ->
			case dict:find({Mod, Name}, SM) of
			  {ok, {Value, 'fun'}} ->
			    {Value, Value =/= CurTaint};
			  _ ->
			    {true, true =/= CurTaint}
			end;
		      _ -> throw("Unsupported call")
      end,
      {Args, C2} = annotate_taint_all(cerl:call_args(Tree), SM),
      NewTaint = NewAnn or get_all_taint(Args),
      {cerl:update_c_call(update_ann(Tree, NewTaint), Mod, Name, Args), C1 or C2};
    'case' ->
      {Arg, C1} = annotate_taint(cerl:case_arg(Tree), SM),
      {Clauses, C2} = annotate_taint_all(cerl:case_clauses(Tree), SM),
      NewTaint = get_taint(Arg) or get_all_taint(Clauses),
      {cerl:update_c_case(update_ann(Tree, NewTaint), Arg, Clauses), C1 or C2};
%    'catch' ->
    clause ->
      VarPats = [A || A <- cerl:clause_pats(Tree), cerl:type(A) == var],
      SM1 = put_vars(VarPats, [{false, var} || _ <- VarPats], SM),
      {Pats, C1} = annotate_taint_all(cerl:clause_pats(Tree), SM1),
      {Guard, C2} = annotate_taint(cerl:clause_guard(Tree), SM1),
      {Body, C3} = annotate_taint(cerl:clause_body(Tree), SM1),
      NewTaint = get_taint(Body) or get_all_taint(Pats) or get_taint(Guard),
      {cerl:update_c_clause(update_ann(Tree, NewTaint), Pats, Guard, Body), C1 or C2 or C3};
%    cons ->
    'fun' ->
      SM1 = put_vars(cerl:fun_vars(Tree), [{false, var} || _ <- cerl:fun_vars(Tree)], SM),
      {Vars, C1} = annotate_taint_all(cerl:fun_vars(Tree), SM1),
      {Body, C2} = annotate_taint(cerl:fun_body(Tree), SM1),
      NewTaint = get_taint(Body) or get_all_taint(Vars),
      {cerl:update_c_fun(update_ann(Tree, NewTaint), Vars, Body), C1 or C2};
    'let' ->
      {Arg, C2} = annotate_taint(cerl:let_arg(Tree), SM),
      SM1 = put_vars(cerl:let_vars(Tree), get_arg_taints(Arg), SM),
      {Vars, C1} = annotate_taint_all(cerl:let_vars(Tree), SM1),
      {Body, C3} = annotate_taint(cerl:let_body(Tree), SM1),
      NewTaint = get_all_taint(Vars) or get_taint(Arg) or get_taint(Body),
      {cerl:update_c_let(update_ann(Tree, NewTaint), Vars, Arg, Body), C1 or C2 or C3};
    letrec ->
      Combine = fun(X, Y) -> {annotate_taint(X, SM), annotate_taint(Y, SM)} end,
      Defs1 = [Combine(N, D) || {N, D} <- cerl:letrec_defs(Tree)],
      Defs = [{element(1, N), element(1, D)} || {N, D} <- Defs1],
      C1 = lists:foldl(fun (A,B) -> A or B end, false, [element(2, N) or element(2, D) || {N, D} <- Defs1]),
      {Body, C2} = annotate_taint(cerl:letrec_body(Tree), SM),
      NewTaint = lists:foldl(fun (A, B) -> A or B end, false, [get_taint(N) or get_taint(D) || {N, D} <- Defs]) or get_taint(Body),
      {cerl:update_c_letrec(update_ann(Tree, NewTaint), Defs, Body), C1 or C2};
    literal ->
      {update_ann(Tree, false), true == CurTaint};
    primop ->
      {update_ann(Tree, true), false == CurTaint};
%    'receive' ->
%    seq ->
%    'try' ->
%    tuple ->
%    values ->
    var ->
      case dict:find(cerl:var_name(Tree), SM) of
	{ok, {Value, _}} ->
	  {update_ann(Tree, Value), Value =/= CurTaint};
	error ->
	  {update_ann(Tree, true), true =/= CurTaint}
      end
  end.

-spec get_arg_taints(cerl:cerl()) -> [{taint(), atom()}].
get_arg_taints(Arg) ->
  [{get_taint(Arg), var}].

-spec annotate_taint_all([cerl:cerl()], symbol_table()) -> {[cerl:cerl()], atom()}.
annotate_taint_all(Trees, SM) ->
  X = [annotate_taint(T, SM) || T <- Trees],
  {[element(1, Y) || Y <- X], lists:foldl(fun(A, B) -> B or element(2, A) end, false, X)}.

-spec get_taint(cerl:cerl()) -> atom().
get_taint(Tree) ->
  Anno = cerl:get_ann(Tree),
  get_taint_anno(Anno).

-spec get_taint_anno([]) -> taint().
get_taint_anno(Anno) ->
  Sf = fun(A, B) ->
	   case A of
	     {tainted, T} -> B or T;
	     _ -> B
	   end
       end,
  lists:foldl(Sf, false, Anno).

-spec get_all_taint([cerl:cerl()]) -> atom().
get_all_taint(Trees) ->
  lists:foldl(fun(X,Y) -> X or Y end, false, [get_taint(T) || T <- Trees]).
