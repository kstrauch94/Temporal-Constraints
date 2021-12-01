%
% Domain
%

%#const horizon = 30.
time(1..horizon).


%
% Preprocessing
%

mutex(G,X) :- mutexGroup(G), contains(G,X,V).
mutex(G)   :- mutexGroup(G), #count{X : mutex(G,X)} > 1.


%
% Initial situation
%

% open initial situation
holds(X,V,0) :- initialState(X,V).


%
% Transition
%

% generate (a SAT problem)
{     holds(X,V,T) } :- contains(X,V), time(T).
{ occurs(A,T) : action(A) }  :- time(T).

% at most one action
:- 2 { occurs(A,T) : action(A) }, time(T).

% effects
%:- occurs(A,T), postcondition(A,_,X,V), not holds(X,V,T), time(T).
&constraint(1,horizon,eff){+.occurs(A); -.holds(X,V)} :- postcondition(A,_,X,V).

% preconditions
%:- occurs(A,T),    precondition(A,X,V), not holds(X,V,T-1), time(T).
&constraint(1,horizon,pre){+.occurs(A); -~holds(X,V)} :- precondition(A,X,V).

% inertia
:- holds(X,V,T), not holds(X,V,T-1), time(T), T>0,
   not occurs(A,T) : postcondition(A,_,X,V).
%&constraint(1,horizon,inert){+.holds(X,V); -~holds(X,V); -.occurs(A) : postcondition(A,_,X,V) } :- contains(X,V).

&signature{++occurs(A)} :- action(A).
&signature{--holds(X,V)} :- contains(X,V).

%#show occurs/2.
% existence and uniqueness of value
:- not 1 { holds(X,V,T) } 1, variable(X), time(T).

% mutexes
:- 2 #sum { 1,X,V: holds(X,V,T), contains(G,X,V) }, mutex(G), time(T).

:- goal(X,V), not holds(X,V,horizon).