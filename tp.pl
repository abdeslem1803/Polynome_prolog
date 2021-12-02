islist([_]).
islist([_|T]) :- islist(T).
afficher(L):-simplifier(L,L1),afficher1(L1).
afficher1([[X,X1]]):- myWrite1(X,X1).
afficher1([[X,X1]|L]):-islist(L),afficher(L),myWrite(X,X1).
myWrite(0,_).
myWrite(1,1) :- write(' + '),write('x').
myWrite(X,1) :- X > 0,write(' + '),write(X),write('x').
myWrite(-1,1) :- write(' -x').
myWrite(X,1) :- X < 0,write(X),write('x').
myWrite(1,0) :- write(' + 1').
myWrite(-1,0) :- write(' - 1').
myWrite(1,P) :- write(' + '),iszero(P).
myWrite(X,P) :- X >0,write(' + '),write(X),iszero(P).
myWrite(-1,P) :- write(' - '),iszero(P).
myWrite(X,P) :- X <0,write(X),iszero(P).

myWrite1(0,_).
myWrite1(1,1) :- write('x').
myWrite1(-1,1) :- write(' -x').
myWrite1(X,1) :-write(X),write('x').
myWrite1(1,P) :- iszero(P).
myWrite1(-1,P) :-write(' -'),iszero(P).
myWrite1(X,P) :-write(X),iszero(P).
iszero(0).
iszero(P) :- write('x^'),write(P).
%simplifier nom de la fonction est simplifier
simplifier(L,L1):-simplifier_p(L,L2),simplifier_0(L2,L3),ordonner(L3,L1).
simplifier_0([[0,_]],[]).
simplifier_0([[X,Y]],[[X,Y]]).
simplifier_0([[0,_]|L],[L1]):-simplifier_0(L,L1).
simplifier_0([[X,Y]|L],[[X,Y]|L1]):-simplifier_0(L,L1).
simplifier_p([[X,Y]|L],P):- simplifier_p(L,L1),simplifier_plus([[X,Y]],L1,P).
simplifier_p([[X,Y]],[[X,Y]]).
simplifier_plus([[X,Y]],[[Z,Y]],[[T,Y]]):-T is X+Z.
simplifier_plus([[X,Y]],[[Z,H]],[[X,Y],[Z,H]]):- Y \= H.
simplifier_plus([[X,Y]],[[Z,Y]|L],L1):-T is X+Z ,simplifier_plus([[T,Y]],L,L1).
simplifier_plus([[X,Y]],[[Z,H]|L],[[Z,H]|L1]):- Y \=H ,simplifier_plus([[X,Y]],L,L1).
ordonner([X|Xs],Ys) :- ordonner(Xs,Zs),inserer(X,Zs,Ys).
ordonner([],[]).
inserer(X,[],[X]).
inserer(X,[Y|Ys],[Y|Zs]) :-greater(Y,X),inserer(X,Ys,Zs).
inserer(X,[Y|Ys],[X,Y|Ys]) :-greatereq(X,Y).
greater([_,N2],[_,N1]) :-N1 > N2.
greatereq([_,N2],[_,N1]) :-N1 >= N2.
%evaluation nom de la fonction est dérivation
ev3(X,Y,Z) :- ev(X,Y,1,Z),!.
ev(_,0,A,Z) :- Z is A.
ev(X,Y,A,Z) :- Y1 is Y - 1,A1 is A*X,ev(X,Y1,A1,Z).
evaluation([],_,0).
evaluation([[C,N]|Poly1],X,P):-evaluation(Poly1,X,P1),ev3(X,N,PP),P is (P1+C*PP).
%derivation
derivation(L,L1):-derivation1(L,L2),simplifier(L2,L1).
derevation1([[_,0]],[]).
derivation1([[X,Y]],[[Z,T]]):- Y > 0, Z is X*Y,T is Y-1.
derivation1([[_,0]|L],L1):-derivation(L,L1).
derivation1([[X,Y]|L],[[Z,T]|L1]):-Z is X*Y,T is Y-1,derivation(L,L1).
%somme
somme(L,N,T):-append(L,N,H),simplifier(H,T).
%soustraction
soustraction(L,N,T):- negation(N,H),somme(L,H,T).
negation([],[]).
negation([[X,Y]|L],[[T,Y]|L1]):- T is -1*X,negation(L,L1).
%produit
produit(L,L1,M):-mul_com(L,L1,M2),simplifier(M2,M).
mul_p([[X,Y]],[[Z,T]],[[H,P]]):- H is X*Z,P is Y+T.
mul_p([[X,Y]],[[Z,T]|L],[[H,P]|R]):- H is X*Z,P is Y+T,mul_p([[X,Y]],L,R).
mul_com([[X,Y]],L,P):-mul_p([[X,Y]],L,P).
mul_com([[X,Y]|L],L1,P):-mul_com(L,L1,H),mul_p([[X,Y]],L1,T),append(T,H,P).
%partie2
%priorites
-op(700, yfx, '*').
-op(650, yfx, '+').
-op(630, yfx, '-').
-op(620, fx, 'simp').
-op(620, fx, 'deri').
-op(600, xfx, 'est').
est(+(A,B),R):-somme(A,B,R).
est(-(A,B),R):-soustraction(A,B,R).
est(*(A,B),R):-produit(A,B,R).
simp(X,L):-simplifier(X,L).
deri(X,L):-derivation(X,L).
% je ne peux pas avoir plusier opération arithmétique dans une meme
% fonction de est par exemple est(P1+P2-P3)
