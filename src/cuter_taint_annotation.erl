-module(cuter_taint_annotation).
-export([annotate_taint/2, get_taint/1, get_taint_anno/1]).
-export_type([taint/0, symbol_table/0]).

-type taint() :: atom().
-type symbol_table() :: dict:dict().

%% annotating function

-spec update_ann(cerl:cerl(), taint(), taint()) -> cerl:cerl().
update_ann(T, Old, New) when Old == New -> T;
update_ann(T, _Old, New) ->
  Anno = cerl:get_ann(T),
  F = fun(A) ->
	  case A of
	    {tainted, _} -> {tainted, New};
	    _ -> A
	  end
      end,
  cerl:set_ann(T, lists:map(F, Anno)).

  
-spec put_vars(symbol_table(), [{taint(), atom()}], [cerl:cerl()]) -> symbol_table().
put_vars(Vars, Flags, SM) ->
  lists:foldl(fun({Var, Flag}, B) -> dict:store(cerl:var_name(Var), Flag, B) end, SM, lists:zip(Vars, Flags)).


-spec annotate_taint(cerl:cerl(), symbol_table()) -> {cerl:cerl(), atom()}.
annotate_taint(Tree, SM) ->
  CurTaint = get_taint(Tree),
  case cerl:type(Tree) of
%    alias ->
    'apply' ->
      {Op, C1} = case cerl:type(cerl:apply_op(Tree)) of
	    var ->
	      case dict:find(cerl:var_name(cerl:apply_op(Tree)), SM) of
		{ok, {Value, 'fun'}} ->
		  {update_ann(Tree, CurTaint, Value), Value == CurTaint};
		_ ->
		  {update_ann(Tree, CurTaint, true), true == CurTaint}
	      end
	  end,
      {Args, C2} = annotate_taint_all(cerl:apply_args(Tree), SM),
      NewTaint = get_taint(Op) or get_all_taint(Args),
      {cerl:update_c_apply(update_ann(Tree, CurTaint, NewTaint), Op, Args), C1 or C2};
%    binary ->
%    bitstr ->
    call ->
      {Mod, C1} = annotate_taint(cerl:call_module(Tree), SM),
      {Name, C2} = annotate_taint(cerl:call_name(Tree), SM),
      {Args, C3} = annotate_taint_all(cerl:call_args(Tree), SM),
      NewTaint = get_taint(Mod) or get_taint(Name) or get_all_taint(Args),
      {cerl:update_c_call(update_ann(Tree, CurTaint, NewTaint), Mod, Name, Args), C1 or C2 or C3};
    'case' ->
      {Arg, C1} = annotate_taint(cerl:case_arg(Tree), SM),
      {Clauses, C2} = annotate_taint_all(cerl:case_clauses(Tree), SM),
      NewTaint = get_taint(Arg) or get_all_taint(Clauses),
      {cerl:update_c_case(update_ann(Tree, CurTaint, NewTaint), Arg, Clauses), C1 or C2};
%    'catch' ->
    clause ->
      VarPats = [A || A <- cerl:clause_pats(Tree), cerl:type(A) == var],
      SM1 = put_vars(VarPats, [{false, var} || _ <- VarPats], SM),
      {Pats, C1} = annotate_taint_all(cerl:clause_pats(Tree), SM1),
      {Guard, C2} = annotate_taint(cerl:clause_guard(Tree), SM1),
      {Body, C3} = annotate_taint(cerl:clause_body(Tree), SM1),
      NewTaint = get_taint(Body) or get_all_taint(Pats) or get_taint(Guard),
      {cerl:update_c_clause(update_ann(Tree, CurTaint, NewTaint), Pats, Guard, Body), C1 or C2 or C3};
%    cons ->
    'fun' ->
      SM1 = put_vars(cerl:fun_vars(Tree), [{false, var} || _ <- cerl:fun_vars(Tree)], SM),
      {Vars, C1} = annotate_taint_all(cerl:fun_vars(Tree), SM1),
      {Body, C2} = annotate_taint(cerl:fun_body(Tree), SM1),
      NewTaint = get_taint(Body) or get_all_taint(Vars),
      {cerl:update_c_fun(update_ann(Tree, CurTaint, NewTaint), Vars, Body), C1 or C2};
    'let' ->
      {Arg, C2} = annotate_taint(cerl:let_arg(Tree), SM),
      SM1 = put_vars(cerl:let_vars(Tree), get_arg_taints(Arg), SM),
      {Vars, C1} = annotate_taint_all(cerl:let_vars(Tree), SM1),
      {Body, C3} = annotate_taint(cerl:let_body(Tree), SM1),
      NewTaint = get_all_taint(Vars) or get_taint(Arg) or get_taint(Body),
      {cerl:update_c_let(update_ann(Tree, CurTaint, NewTaint), Vars, Arg, Body), C1 or C2 or C3};
    letrec ->
      Combine = fun(X, Y) -> {annotate_taint(X, SM), annotate_taint(Y, SM)} end,
      Defs1 = [Combine(N, D) || {N, D} <- cerl:letrec_defs(Tree)],
      Defs = [{element(1, N), element(1, D)} || {N, D} <- Defs1],
      C1 = lists:foldl(fun (A,B) -> A or B end, false, [element(2, N) or element(2, D) || {N, D} <- Defs1]),
      {Body, C2} = annotate_taint(cerl:letrec_body(Tree), SM),
      NewTaint = lists:foldl(fun (A, B) -> A or B end, false, [get_taint(N) or get_taint(D) || {N, D} <- Defs]) or get_taint(Body),
      {cerl:update_c_letrec(update_ann(Tree, CurTaint, NewTaint), Defs, Body), C1 or C2};
    literal ->
      {update_ann(Tree, CurTaint, false), false == CurTaint};
    primop ->
      {update_ann(Tree, CurTaint, true), true == CurTaint};
%    'receive' ->
%    seq ->
%    'try' ->
%    tuple ->
%    values ->
    var ->
      case dict:find(cerl:var_name(Tree), SM) of
	{ok, {Value, _}} ->
	  {update_ann(Tree, CurTaint, Value), Value == CurTaint};
	error ->
	  {update_ann(Tree, CurTaint, true), true == CurTaint}
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
