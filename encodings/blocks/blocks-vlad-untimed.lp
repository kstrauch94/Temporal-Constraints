#const grippers=1.

time(0..horizon).

location(B) :- block(B).
location(table).


% GENERATE
{move(B,L,T) : block(B), location(L)} grippers :- time(T), T<horizon.

% DEFINE
% effect of moving a block
on(B,L,T+1) :- move(B,L,T), block(B), location(L), time(T), T<lasttime.

% inertia
on(B,L,T+1) :- on(B,L,T), not -on(B,L,T+1), location(L), block(B), time(T), T<lasttime.

% uniqueness of location
-on(B,L1,T) :- on(B,L,T), L!=L1, block(B), location(L), location(L1), time(T).

% TEST
% two blocks cannot be on top of the same block
%:- 2 {on(B1,B,T) : block(B1)}, block(B), time(T).
%:- on(B1,B,T), on(B2,B,T), B2 < B1, block(B2), block(B1), time(T). 

&constraint(0,horizon){+.on(B1,B); +.on(B2,B)} :- B2 < B1, block(B2), block(B1), block(B). 

% a block can’t be moved unless it is clear
%:- move(B,L,T), on(B1,B,T), block(B), block(B1), location(L), time(T), T<lasttime.

&constraint(0,horizon-1){+.move(B,L), +.on(B1,B)} :- block(B), block(B1), location(L).

% a block can’t be moved onto a block that is being moved also
%:- move(B,B1,T), move(B1,L,T), block(B), block(B1), location(L), time(T), T<lasttime.

&constraint(0,horizon-1){+.move(B,B1); +.move(B1,L)} :- block(B), block(B1), location(L).

&signature{++on(B,L)} :- block(B), location(L).
&signature{++move(B,L)} :- block(B), location(L).