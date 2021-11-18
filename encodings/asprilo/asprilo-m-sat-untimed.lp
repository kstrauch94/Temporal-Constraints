#include "input.lp".
#include "goal-M.lp".
#include "output-M.lp".

%% action-m.lp
%#const horizon=1.
time(1..horizon).

direction((X,Y)) :- X=-1..1, Y=-1..1, |X+Y|=1.
nextto((X,Y),(DX,DY),(X',Y')) :- direction((DX,DY)), position((X,Y)), position((X',Y')),
                                 (X,Y)=(X'-DX,Y'-DY), (X',Y')=(X+DX,Y+DY).

{ move(R,D,T) : direction(D) } 1 :- isRobot(R), time(T).
1 {position(R,C,T) :  position(C)} 1 :- time(T), isRobot(R).

% - move/3 ----------------------------------------------------------------------
% :- move(R,D,T), position(R,C',T-1),     nextto(C',D,C).
%:- not position(R,C,T), move(R,D,T), position(R,C',T-1),     nextto(C',D,C).
&constraint(1,horizon){-.position(R,C); +.move(R,D); +~position(R,C')} :- isRobot(R), position(C), 
                                                                          position(C'), nextto(C',D,C).

%:- move(R,D,T), position(R,C ,T-1), not nextto(C ,D,_).
&constraint(1,horizon){+.move(R,D); +~position(R,C)} :- isRobot(R), position(C), direction(D), not nextto(C ,D,_).

% - inertia ---------------------------------------------------------------------
%position(R,C,T) :- position(R,C,T-1), not move(R,_,T), isRobot(R), time(T).
%:- not position(R,C,T), position(R,C,T-1), not move(R,_,T), isRobot(R), time(T).

&constraint(1,horizon){-.position(R,C); +~position(R,C); -.move(R,D) : direction(D)} :- isRobot(R), position(C).

% - edge collision --------------------------------------------------------------
moveto(C',C,T) :- nextto(C',D,C), position(R,C',T-1), move(R,D,T).
 %:- moveto(C',C,T), moveto(C,C',T),.

&constraint(1,horizon){+.moveto(C',C); +.moveto(C,C')} :-  C < C', nextto(C',D,C).

% - vertex collision ------------------------------------------------------------
 :- { position(R,C,T) : isRobot(R) }  > 1, position(C), time(T).

% - auxiliaries -----------------------------------------------------------------
 :- { position(R,C,T) } != 1, isRobot(R), time(T).    % REDUNDANT but PERFORMANT?


&signature{++position(R,C)} :- isRobot(R), position(C).
&signature{--position(R,C)} :- isRobot(R), position(C).

&signature{++move(R,D)} :- isRobot(R), direction(D).
&signature{--move(R,D)} :- isRobot(R), direction(D).

&signature{++moveto(C,C')} :- nextto(C',D,C).