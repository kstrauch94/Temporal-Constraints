
block(B) :- has(constant(B), type("block")).
loc(L) :- block(L).
loc(table).

init(on(B,L)) :- initialState(variable(("on", constant(B), constant(L))), value(variable(("on", constant(B), constant(L))), true)).

init(on(B,table)) :- initialState(variable(("ontable", constant(B))), value(variable(("ontable", constant(B))), true)).

goal(on(B,L)) :- goal(variable(("on", constant(B), constant(L))), value(variable(("on", constant(B), constant(L))), true)).

time(0..horizon)