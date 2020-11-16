
time(0..maxtime).

domain(1..maxdom).

a(2,0).
b(1,0).
c(1,0).
d(1,0).
e(1,0).
f(1,0).

1{a(D,T): domain(D) }1 :- time(T).
1{b(D,T): domain(D) }1 :- time(T).
1{c(D,T): domain(D) }1 :- time(T).
1{d(D,T): domain(D) }1 :- time(T).
1{e(D,T): domain(D) }1 :- time(T).
1{f(D,T): domain(D) }1 :- time(T).


%&constraint(0,maxtime){ +.a(D); +~a(D2) } :- D - D2 > 3, domain(D), domain(D2).
:- a(D,T), a(D2,T-1), D - D2 > 3, domain(D), domain(D2), time(T), time(T-1).

%&constraint(0,maxtime){ +.a(D); +~a(D2) } :- D < D2, domain(D), domain(D2).
:- a(D,T), a(D2,T-1), D < D2, domain(D), domain(D2), time(T), time(T-1).

%&constraint(0,maxtime){ +.a(D); +.b(D2) } :- D < D2, domain(D), domain(D2).
:- a(D,T), b(D2,T), D < D2, domain(D), domain(D2), time(T).

%&constraint(0,maxtime){ +.e(D); -.f(D2) } :- D < D2, domain(D), domain(D2).
:- e(D,T), not f(D2,T), D < D2, domain(D), domain(D2), time(T).

%&constraint(0,maxtime){ -.c(D); +.d(D2) } :- D < D2, domain(D), domain(D2).
:- not c(D,T), d(D2,T), D < D2, domain(D), domain(D2), time(T).

%&constraint(0,maxtime){ +~f(D); +.b(D2) } :- D < D2, domain(D), domain(D2).
:- f(D,T-1), b(D2,T), D < D2, domain(D), domain(D2), time(T), time(T-1).

%&constraint(0,maxtime){ +.a(D); +.d(D2) } :- D < D2, domain(D), domain(D2).
:- a(D,T), d(D2,T), D < D2, domain(D), domain(D2), time(T).

%&constraint(0,maxtime){ +~a(D); -.b(D) } :- D < D2, domain(D), domain(D2).
:- a(D,T-1), not b(D,T), D < D2, domain(D), domain(D2), time(T), time(T-1).


:- not a(maxdom,maxtime), b(maxdom-1,maxtime).
