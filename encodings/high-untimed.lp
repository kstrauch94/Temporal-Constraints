
time(1..maxtime).

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


:-&constraint(1,maxtime){ +.a(D); +~a(D2) }, D - D2 > 3, domain(D), domain(D2).

:-&constraint(1,maxtime){ +.a(D); +~a(D2) }, D < D2, domain(D), domain(D2).

:-&constraint(1,maxtime){ +.a(D); +.b(D2) }, D < D2, domain(D), domain(D2).

:-&constraint(1,maxtime){ +.b(D); +~b(D2); +.a(D3)  }, D3 > D + D2, domain(D), domain(D2), domain(D3).

:-&constraint(1,maxtime){ +.b(D); +~c(D2), +~d(D3), +~e(D4), +~f(D5) }, D - D2 > 3, D - D3 > 3, D - D4 > 3, D - D5 > 3, domain(D), domain(D2), domain(D3), domain(D4), domain(D5).

:-&constraint(1,maxtime){ +.a(D); +.b(D); +.c(D); +~d(D); +~e(D); +~f(D) }, domain(D).


:- not a(maxdom,maxtime), b(maxdom-1,maxtime).
