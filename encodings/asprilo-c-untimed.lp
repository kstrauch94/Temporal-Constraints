timelimit(horizon).
time(0..horizon). 

%%
% Actions
%%

action(action(move(0,-1))).
action(action(move(0,1))).
action(action(move(1,0))).
action(action(move(-1,0))).
action(action(pickup)).
action(action(putdown)).


%%
% Initial state
%%
holds(at(robot(R),node(X,Y)),0) :- init(object(robot,R),value(at,(X,Y))).
holds(at(shelf(S),node(X,Y)),0) :- init(object(shelf,S),value(at,(X,Y))).


% check product amounts and see that there is enough to fulfill order
productamt(P,C) :- C = #sum{A,S : init(object(product,P),value(on,(S,A)))}, product(product(P)).
orderedamt(P,C) :- C = #sum{A,O : init(object(order,O),value(line,(P,A)))}, product(product(P)).
notenough(P) :- productamt(P,A), orderedamt(P,A2), A2 > A.

% There is not enough product to fulfill orders
:- notenough(P).

% generate actions
{ do(R,A,T) : action(A) } 1 :- robot(R), time(T).
:- do(R,A,T), not possible(R,A,T), time(T).

% helpers
moved(R,T) :- do(R,action(move(DX,DY)),T), time(T).

%%%%%%%% Inertia
holds(F,T) :- holds(F,T-1), not abnormal(F,T), time(T).


%%%%%%%% Possibles
possible(R,action(move(DX,DY)),T) :- holds(at(R,node(X,Y)),T), node(X+DX,Y+DY), action(action(move(DX,DY))), robot(R), time(T).

possible(R,action(pickup),T) :- holds(at(R,node(X,Y)),T), holds(at(S,node(X,Y)),T), not holds(carry(R,S),T), robot(R), shelf(S), time(T).

possible(R,action(putdown),T) :- holds(carry(R,S),T), robot(R), shelf(S).

%%%%%%% Dynamic Effects

holds(at(R,node(X+DX,Y+DY)),T) :- holds(at(R,node(X,Y)),T-1), do(R,action(move(DX,DY)),T-1), node(X+DX,Y+DY), time(T).

holds(at(S,node(X,Y)),T) :- holds(at(R,node(X,Y)),T), holds(carry(R,S),T), time(T).

holds(carry(R,S),T) :- holds(at(R,node(X,Y)),T-1), holds(at(S,node(X,Y)),T-1), do(R,action(pickup),T-1), robot(R), shelf(S), time(T).

%%%%%%% Inertia Effects

abnormal(at(R,node(X,Y)),T) :- node(X,Y), moved(R,T-1), time(T).

abnormal(at(S,node(X,Y)),T) :- node(X,Y), holds(carry(R,S),T-1), moved(R,T-1), time(T).

abnormal(carry(R,S),T) :- holds(carry(R,S),T-1), do(R,action(putdown),T-1), time(T).

%%%%%%% Static Laws


:- highway(X,Y), not node(X,Y).
% can not place shelf on a highway
%:- holds(at(R,node(X,Y)),T), do(R,action(putdown),T), highway(X,Y), time(T).
&constraint(1,horizon){ +.holds(at(R,node(X,Y))); +.do(R,action(putdown))} :- highway(X,Y), robot(R).

% robots cant do nothing for more than 1 timestep if they are in a highway
%init(at(robot(R),node(X,Y))) :- init(object(robot,R), value(at, (X,Y))).
%:- highway(X,Y), holds(at(R,node(X,Y)),T), not moved(R,T-1), not moved(R,T), not init(at(R,node(X,Y))), robot(R), time(T),T>0.



% no 2+ robots/shelfs in the same spot
:- node(X,Y), time(T), 2{holds(at(R,node(X,Y)),T) : robot(R)}.
:- node(X,Y), time(T), 2{holds(at(S,node(X,Y)),T) : shelf(S)}.

% robot/shelf can only be in 1 node
:- robot(R), time(T), 2{holds(at(R,node(X,Y)),T) : node(X,Y)}.
:- shelf(S), time(T), 2{holds(at(S,node(X,Y)),T) : node(X,Y)}.



% robots cant swap places
%:- holds(at(robot(R1),node(X1,Y1)),T), holds(at(robot(R2),node(X2,Y2)),T),
%    holds(at(robot(R1),node(X2,Y2)),T-1), holds(at(robot(R2),node(X1,Y1)),T-1),
%    R1 > R2, |X2-X1|+|Y2-Y1|==1, time(T), T>0, T < 3.
%:-&constraint(1,horizon){ +.holds(at(robot(R1),node(X1,Y1))); +.holds(at(robot(R2),node(X2,Y2))); +~holds(at(robot(R1),node(X2,Y2))); +~holds(at(robot(R2),node(X1,Y1))) },
%  R1 > R2, |X2-X1|+|Y2-Y1|==1, time(T), T>0, node(X1,Y1), node(X2,Y2),
%  robot(robot(R1)), robot(robot(R2)).


%:- holds(at(R1,node(X1,Y1)),T), holds(at(R2,node(X1,Y1-1)),T), do(R1,action(move(0,-1)),T), do(R2,action(move(0,1)),T), R1 != R2, time(T).
%:- holds(at(R1,node(X1,Y1)),T), holds(at(R2,node(X1-1,Y1)),T), do(R1,action(move(-1,0)),T), do(R2,action(move(1,0)),T), R1 != R2, time(T).

&constraint(1,horizon){+.holds(at(robot(R1),node(X1,Y1))); +.holds(at(robot(R2),node(X1,Y2)));
+.do(robot(R1),action(move(0,MY))); +.do(robot(R2),action(move(0,1)))} :-
 R1 > R2, node(X1,Y1), Y2=Y1-1, node(X1,Y2), robot(robot(R1)), robot(robot(R2)), MY=-1.

&constraint(1,horizon){+.holds(at(robot(R1),node(X1,Y1))); +.holds(at(robot(R2),node(X2,Y1)));
+.do(robot(R1),action(move(MX,0))); +.do(robot(R2),action(move(1,0)))} :-
 R1 > R2, node(X1,Y1), X2=X1-1, node(X2,Y1), robot(robot(R1)), robot(robot(R2)), MX=-1.

% a robot can only carry 1 shelf
:- robot(R), time(T), 2{holds(carry(R,S),T) : shelf(S)}.

%:- do(R,action(move(DX,DY)),T), do(R,action(move(-DX,-DY)),T-1), time(T), T>0.
&constraint(1,horizon){ +.do(R,action(move(DX,DY))); +~do(R,action(move(DX2,DY2))) } :- action(move(DX,DY)), DX2=-DX, DY2=-DY, robot(R).

%:- do(R,action(pickup),T), do(R,action(putdown),T-1), time(T), T>0.
&constraint(1,horizon){ +.do(R,action(pickup)); +~do(R,action(putdown)) } :- robot(R).

%:- do(R,action(putdown),T), do(R,action(pickup),T-1), time(T), T>0.
&constraint(1,horizon){ +.do(R,action(putdown)); +~do(R,action(pickup)) } :- robot(R).

on(product(P),shelf(S)) :- init(object(product,P),value(on,(S,A))).

holds(request(order(O),product(P),pickingStation(Pi)),0) :- init(object(order,O),value(line,(P,A))), init(object(order,O),value(pickingStation,Pi)).


noaction(R,T) :- not do(R,A,T) : action(A); robot(R), time(T).

delivered(R,O,P,Pi,T) :- holds(request(O,P,Pi),T), at(Pi,node(X,Y)), holds(at(R,node(X,Y)),T), holds(carry(R,S),T), on(P,S), noaction(R,T), time(T).
    
abnormal(request(O,P,Pi),T) :- delivered(R,O,P,Pi,T-1), time(T).


goal(T) :- not holds(request(_,_,_),T), time(T).
:- not goal(T), timelimit(T).

% dont do anything if goal was reached
:- goal(T), do(_,_,T).

% format the action into the input for the visualizer

occurs(R,action(move,(DX,DY)),T) :- do(R,action(move(DX,DY)),T).
occurs(R,action(pickup,()),T) :- do(R,action(pickup),T).
occurs(R,action(putdown,()),T) :- do(R,action(putdown),T).


occurs(R,action(deliver,(O,P,A)),T) :- do(R,action(deliver(O,P,A)),T).

occurs(R,action(deliver,(O,P)),T) :- do(R,action(deliver(O,P)),T).

occurs(R,action(deliver,(O,P)),T) :- delivered(R,O,P,_,T).

#show occurs/3.
node(X,Y) :- init(object(node,N),value(at,(X,Y))).

robot(robot(R)) :- init(object(robot,R),_).
shelf(shelf(S)) :- init(object(shelf,S),_).
order(order(O)) :- init(object(order,O),_).
product(product(P)) :- init(object(product,P),_).
pickingStation(pickingStation(P)) :- init(object(pickingStation,P),_).

at(pickingStation(P),node(X,Y)) :- init(object(pickingStation,P),value(at,(X,Y))).

highway(X,Y) :- init(object(highway,_),value(at,(X,Y))).

