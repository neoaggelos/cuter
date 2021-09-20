-module(map).
-export([simple/1, simple_squared/1]).

-spec simple(integer()) -> #{value => float()}.
simple(X) ->
    #{ value => 10 / (X + 4) }.

-spec simple_squared(integer()) -> #{value => float()}.
simple_squared(X) ->
    #{ value => 10 / (X*X - 4) }.
