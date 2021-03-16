time(T) :- timestep(T).
peg(a;b;c;d).

peg_disk(a,1).
peg_disk(b,2).
peg_disk(c,3).
peg_disk(d,4).

goal_on(D,P) :- ongoal(D,Peg), peg_disk(P,Peg).
goal_on(D,P) :- ongoal(D,D2), goal_on(D2,P).

init_on(D,P) :- on0(D,Peg), peg_disk(P,Peg).
init_on(D,P) :- on0(D,D2), init_on(D2,P).

rdisk(D) :- disk(D), D > 4.


on(D,P,0) :- init_on(D,P).

ngoal(T) :- on(D,P,T), not goal_on(D,P).
:- ngoal(Max), steps(Max).

1 { move(D,P,T) : rdisk(D), peg(P)} 1 :- ngoal(T-1), time(T), T>0.

move(D,T) :- move(D,P,T).

on(D,P,T) :- move(D,P,T).
on(D,P,T) :- on(D,P,T-1), not move(D,T), time(T), T>0.
blocked(D-1,P,T) :- on(D,P,T-1), time(T), T>0.
blocked(D-1,P,T) :- blocked(D,P,T), rdisk(D), time(T), T>0.

%:- move(D,P,T), blocked(D-1,P,T).
%:- move(D,T), on(D,P,T-1), blocked(D,P,T).

&constraint(1,Max){+.move(D,P); +.blocked(D2,P)} :- rdisk(D), peg(P), D2 = D-1, steps(Max).
&constraint(1,Max){+.move(D); +~on(D,P); +.blocked(D,P)} :- rdisk(D), peg(P), steps(Max).

&signature{++move(D,P)} :- rdisk(D), peg(P).
&signature{++blocked(D,P)}:- rdisk(D), peg(P).
&signature{++blocked(D,P)}:- D=D2-1,rdisk(D2), peg(P).

&signature{++move(D)} :- rdisk(D).
&signature{++on(D,P)} :- rdisk(D), peg(P).

:- rdisk(D), not 1 {on(D,P,T)} 1, time(T), T>0.

#show on/3.