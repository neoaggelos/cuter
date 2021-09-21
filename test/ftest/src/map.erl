-module(map).
-export([simple/1, simple_squared/1, simple_extend/1, extend_empty/1]).

-spec simple(integer()) -> #{value => float()}.
simple(X) ->
    #{ value => 10 / (X + 4) }.

-spec simple_squared(integer()) -> #{value => float()}.
simple_squared(X) ->
    #{ value => 10 / (X*X - 4) }.

-spec simple_extend(integer()) -> #{value => float()}.
simple_extend(X) ->
    A = #{ a => X },
    A#{ value => 10 / (X*X - 4) }.

-spec extend_empty(integer()) -> #{value => float()}.
extend_empty(X) ->
    A = #{},
    A#{ value => 10 / (X*X - 4) }.
