%% -*- erlang-indent-level: 2 -*-
%%------------------------------------------------------------------------------
-module(cuter_tests).

-include_lib("eunit/include/eunit.hrl").

-export([t0/1, t1/1, t2/2]).

-type descr() :: nonempty_string().

-spec test() -> 'ok' | {'error', term()}.  %% This should be provided by EUnit

%% Ensure it runs properly
-spec run_test() -> ok.
run_test() ->
  Depth = 3,
  Opts = cuter_options(),
  [{{lists, reverse, 1}, R}] = cuter:run(lists, reverse, [[]], Depth, Opts),
  ?assertEqual([], R).

-define(TIMEOUT_BUGS, 20000).

-spec bugs_test_() -> [{descr(), {'timeout', ?TIMEOUT_BUGS, {'setup', fun(), fun()}}}].
bugs_test_() ->
  Tests = [ {"Match to single value", {t0, [0], 1, [[42]]}}
          , {"Non-exhaustive pattern matching", {t1, [0], 17, [[42], [42.0]]}}
          , {"N-th element of a list to be an atom", {t2, [1, [1,2]], 25, fun check_t2/1}}
          ],
  [{"Shallow - " ++ Descr, {timeout, ?TIMEOUT_BUGS, {setup, fun() -> Data end, fun find_bugs/1}}} || {Descr, Data} <- Tests].

find_bugs({Fn, Inp, Depth, Bugs}) ->
  [{_Mfa, Found}] = cuter:run(?MODULE, Fn, Inp, Depth, cuter_options()),
  ToStr = fun(X) -> lists:flatten(io_lib:format("~w", [X])) end,
  case is_list(Bugs) of
    true ->
      [{ToStr(B), ?_assertEqual(true, lists:member(B, Found))} || B <- Bugs];
    false ->
      [?_assertEqual(true, Bugs(Found))]
  end.

-define(TIMEOUT_RMT, 40000).

-spec run_multiple_test_() -> {'timeout', ?TIMEOUT_RMT, fun(() -> nonempty_list())}.
run_multiple_test_() ->
  Fn = fun() ->
    Seeds = [
      {lists, nth, [3, [1,2,3]], 15},
      {lists, nthtail, [3, [1,2,3]], 15}
    ],
    Errors = cuter:run(Seeds, cuter_options()),
    Errors1 = filter_errors({lists, nth, 2}, Errors),
    Errors2 = filter_errors({lists, nthtail, 2}, Errors),
    LenChecks = [?assertEqual(5, length(Errors1)), ?assertEqual(5, length(Errors2))],
    ValChecks = [?assert(N > length(L)) || [N, L] <- Errors1 ++ Errors2],
    LenChecks ++ ValChecks
  end,
  {timeout, ?TIMEOUT_RMT, Fn}.

filter_errors(Mfa, Errors) ->
  case lists:keysearch(Mfa, 1, Errors) of
    false -> [];
    {value, {Mfa, Es}} -> Es
  end.

cuter_options() ->
  [{number_of_pollers, 1}, {number_of_solvers, 2}, disable_pmatch].

%% ------------------------------------------------------------------
%% Functions with bugs for testing
%% ------------------------------------------------------------------

-spec t0(integer()) -> ok.
t0(42) -> error(bug);
t0(X) -> X.

-spec t1(number()) -> ok.
t1(X) when X > 42 -> ok;
t1(X) when X < 42 -> ok.

-spec t2(pos_integer(), list()) -> ok.
t2(N, L) when N =< length(L) ->
  case lists:nth(N, L) of
    X when is_atom(X) -> error(bug);
    _ -> ok
  end;
t2(_, _) -> ok.

check_t2(Found) ->
  lists:any(fun([X, Y]) -> is_atom(lists:nth(X, Y)) end, Found).
