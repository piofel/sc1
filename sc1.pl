/* Lists Operations
********************/

member(X,[X|_]).
member(X,[_|Ys]) :- member(X,Ys).

member_check(X,[Y|Ys]) :- X\=Y, member(X,Ys), !.
member_check(X,[X|_]). 

nonmember(X,[Y|Ys]) :- X\=Y, nonmember(X,Ys), !.
nonmember(_,[]).

last(X,Xs) :- append(_,[X],Xs), !.

select_last(Xs,Ys) :- append(Ys,[_],Xs), !.

sublist(A,X,B,AXB) :- append(A,XB,AXB), append(X,B,XB).

substitute_sublist(S1,S2,L1,L2) :- sublist(A,S1,B,L1), append(A,S2,L3), append(L3,B,L2).

no_doubles(Xs,Ys) :- no_doubles(Xs,[],Ys).
no_doubles([X|Xs],Revs,Ys) :- member_check(X,Revs), no_doubles(Xs,Revs,Ys), !.
no_doubles([X|Xs],Revs,Ys) :- nonmember(X,Revs), append(Revs,[X],Revs1), no_doubles(Xs,Revs1,Ys), !.
no_doubles([],Ys,Ys).

flatten(Xs,Ys) :- flatten(Xs,[],Ys).
flatten([X|Xs],S,Ys) :- X=[_|_], flatten(X,[Xs|S],Ys), !.
flatten([X|Xs],S,[X|Ys]) :- X\=[_|_], X\=[], flatten(Xs,S,Ys), !.
flatten([X|Xs],S,Ys) :- X=[], flatten(Xs,S,Ys), !.
flatten([],[X|S],Ys) :- flatten(X,S,Ys), !.
flatten([],[],[]).

numbers_set(List,Numbers,NewList) :- numbers_set(List,[],[],Numbers,NewList).
numbers_set([L|Ls],TempN,TempL,N,NL) :- number(L), append(TempN,[L],TempN1), numbers_set(Ls,TempN1,TempL,N,NL), !.
numbers_set([L|Ls],TempN,TempL,N,NL) :- not(number(L)), append(TempL,[L],TempL1), numbers_set(Ls,TempN,TempL1,N,NL), !.
numbers_set([],N,L,N,L).

/* Generalized Multisets Operations
********************/

gms([[_,N]]) :- number(N), !.
gms([_|T]) :- gms(T).

gms_member(E,B,M) :- member([F,M],B), equal(E,F).

gms_non_member(E,B) :- not(gms_member(E,B,_)).

gms_member_with_multiplicity(E,B) :- E=[F,MF], number(MF), member([G,MG],B), MF=MG, equal(F,G), !.

equal_gms([],[]).
equal_gms(A,B) :- gms(A), gms(B), length(A,L), length(B,M), L=M, equal_gms(A,A,B).
equal_gms([A|As],T,B) :- gms_member_with_multiplicity(A,B), equal_gms(As,T,B), !.
equal_gms([],A,[B|Bs]) :- gms_member_with_multiplicity(B,A), equal_gms([],A,Bs), !.
equal_gms([],_,[]) :- !.

delete_absent_elements(B,S) :- E=[_,0], member(E,B), select(E,B,C), delete_absent_elements(C,S), !.
delete_absent_elements(B,B).

non_atomic_gms(G) :- gms_member(X,G,_), number(X).

merge_equal_elements(B,S) :- merge_equal_elements(B,[],S).
merge_equal_elements([E|Es],T,S) :- E=[A,MA], F=[B,MB], member(F,Es), gms_non_member(B,T), equal(A,B), select(F,Es,E1), M is MA+MB, append(T,[[A,M]],T1), merge_equal_elements(E1,T1,S), !.
merge_equal_elements([E|Es],T,S) :- E=[A,MA], F=[B,MB], member(F,T), equal(A,B), select(F,T,T1), M is MA+MB, append(T1,[[A,M]],T2), merge_equal_elements(Es,T2,S), !.
merge_equal_elements([E|Es],T,S) :- E=[A,_], gms_non_member(A,Es), gms_non_member(A,Es), append(T,[E],T1), merge_equal_elements(Es,T1,S), !.
merge_equal_elements([],S,S). 

simplify_multiplicities(B,S) :- simplify_multiplicities(B,[],S).
simplify_multiplicities([B|Bs],T,S) :- B=[E,M], simp(M,M1), append(T,[[E,M1]],T1), simplify_multiplicities(Bs,T1,S), !.
simplify_multiplicities([],S,S).

correct_gms(B,R) :- simplify_multiplicities(B,A), merge_equal_elements(A,C), delete_absent_elements(C,R).

put_into_gms(Element,Multiplicity,Bag,NewGms) :- append(Bag,[[Element,Multiplicity]],C), correct_gms(C,NewGms), !. 

select_from_gms(Element,Multiplicity,Bag,Complement) :- M is -Multiplicity, put_into_gms(Element,M,Bag,Complement), !.

decrease_gms(Element,Multiplicity,Bag,Complement) :- gms_member(Element,Bag,M), abs(M,A), A>=Multiplicity, M>0, select_from_gms(Element,Multiplicity,Bag,Complement), !.
decrease_gms(Element,Multiplicity,Bag,Complement) :- gms_member(Element,Bag,M), abs(M,A), A>=Multiplicity, M<0, put_into_gms(Element,Multiplicity,Bag,Complement), !.

gms_difference(B,[X|As],C) :- X=[E,M], select_from_gms(E,M,B,B1), gms_difference(B1,As,C), !. % B - A = C
gms_difference(C,[],C).

gms_sum(A,B,U) :- append(A,B,V), correct_gms(V,U).

gms_intersection(A,B,I) :- correct_gms(A,X), correct_gms(B,Y), gms_intersection(X,Y,[],I).
gms_intersection([A|As],B,T,I) :- A=[E,MA], gms_member(E,B,MB), min_abs([MA,MB],M), append(T,[[E,M]],T1), gms_intersection(As,B,T1,I), !.
gms_intersection([A|As],B,T,I) :- A=[E,_], gms_non_member(E,B), gms_intersection(As,B,T,I), !.
gms_intersection([],_,I,I).

e_gms_cartesian_product(ElementMultiplicity,Bag,Product) :- e_gms_cartesian_product(ElementMultiplicity,Bag,[],Product).
e_gms_cartesian_product(E,[B|Bs],T,P) :- E=[X,XM], B=[Y,YM], S=[[X,1],[Y,1]], correct_gms(S,S1), M is XM*YM, S2=[S1,M], append(T,[S2],T1), e_gms_cartesian_product(E,Bs,T1,P), !.
e_gms_cartesian_product(_,[],P,P).

gms_cartesian_product(Bag1,Bag2,Product) :- gms_cartesian_product(Bag1,Bag2,[],Product).
gms_cartesian_product([A|As],B,T,P) :- e_gms_cartesian_product(A,B,S), append(T,S,T1), gms_cartesian_product(As,B,T1,P), !.
gms_cartesian_product([],_,T,P) :- correct_gms(T,P).

multiply_multiplicity(Bag,Multiplier,NewBag) :- multiply_multiplicity(Bag,Multiplier,[],NewBag).
multiply_multiplicity([B|Bs],M,T,N) :- B=[E,L], K is L*M, append(T,[[E,K]],T1), multiply_multiplicity(Bs,M,T1,N), !.
multiply_multiplicity([],_,N,N).

equal(X,X) :- !.
equal(X,Y) :- equal_gms(X,Y), !.
equal(X,Y) :- X=..[FX,AX], Y=..[FY,AY], FX=FY, equal(AX,AY), !.

/* Arithmetic
********************/

min_abs(L,M) :- L=[H|T], abs(H,A), min_abs(T,A,H,M).
min_abs([E|Ls],A,T,M) :- abs(E,F), F>=A, min_abs(Ls,A,T,M), !.
min_abs([E|Ls],A,_,M) :- abs(E,F), F<A, min_abs(Ls,F,E,M), !.
min_abs([],_,M,M).

abs_and_sign(Number,AbsoluteValue,Sign) :-  Number>=0, Sign="positive", abs(Number,AbsoluteValue), !.
abs_and_sign(Number,AbsoluteValue,Sign) :-  Number<0, Sign="negative", abs(Number,AbsoluteValue), !.

/* Matrix Algebra
********************/

empty_matrix([H|T]) :- H=[], empty_matrix(T).
empty_matrix([]).

empty_matrix(Empty,NrOfRows) :- length(Empty,NrOfRows), empty_matrix(Empty).

zero_vector(Vector,Length) :- zero_vector([],0,Vector,Length).
zero_vector(T,C,V,L) :- C\=L, C1 is C+1, append(T,[0],T1), zero_vector(T1,C1,V,L), !.
zero_vector(V,C,V,L) :- C=L.

identity_3(I) :- I=[[1,0,0],[0,1,0],[0,0,1]].

transpose(A,B) :- transpose(A,[],B).
transpose(A,Temp,B) :- get_column(A,R), remove_column(A,A1), append(Temp,[R],Temp1), transpose(A1,Temp1,B), !.
transpose(A,B,B) :- empty_matrix(A).

get_row(A,RowNumber,Row) :- get_row(A,RowNumber,0,Row).
get_row([A|_],N,P,Row) :- P1 is P+1, P1=N, Row=A, !.
get_row([_|As],N,P,Row) :- P1 is P+1, P1\=N, get_row(As,N,P1,Row), !.

get_column(A,Col) :- get_column(A,[],Col), !. % gets the first column of a matrix [row1,row2,...]
get_column(A,Temp,Col) :- A=[R|T], R=[E|_], append(Temp,[E],Temp1), get_column(T,Temp1,Col), !.
get_column([],Col,Col) :- !.

get_column(A,ColNumber,Col) :- number(ColNumber), get_column(A,ColNumber,0,Col), !.
get_column(A,N,C,Col) :- C1 is C+1, C1=N, get_column(A,Col), !. 
get_column(A,N,C,Col) :- C1 is C+1, C1\=N, remove_column(A,A1), get_column(A1,N,C1,Col). 

remove_column(A,B) :- remove_column(A,[],B). % removes the first column of a matrix [row1,row2,...]
remove_column(A,Temp,B) :-  A=[R|T], R=[_|Rs], append(Temp,[Rs],Temp1), remove_column(T,Temp1,B).
remove_column([],B,B).

remove_last_column(A,B) :- remove_last_column(A,[],B). % removes the last column of a matrix [row1,row2,...]
remove_last_column(A,Temp,B) :-  A=[R|T], select_last(R,E), append(Temp,[E],Temp1), remove_last_column(T,Temp1,B), !.
remove_last_column([],B,B).

append_column(A,Col,B) :- append_column(A,Col,[],B). % appends column to the right of a matrix [row1,row2,...]
append_column(A,Col,Temp,B) :- A=[R|T], Col=[E|Col1], append(R,[E],R1), append(Temp,[R1],Temp1), append_column(T,Col1,Temp1,B).
append_column([],[],B,B).

vec_sub(Xs,Ys,Z) :- vec_sub(Xs,Ys,[],Z).
vec_sub([X|Xs],[Y|Ys],Temp,Z) :- simp(sum([[X,1],[Y,-1]]),D), append(Temp,[D],Temp1), vec_sub(Xs,Ys,Temp1,Z), !.
vec_sub([],[],Z,Z).

inner_product(Xs,Ys,Z) :- inner_product(Xs,Ys,0,Z). % vector inner product
inner_product([X|Xs],[Y|Ys],Temp,Z) :- simp(sum([[Temp,1],[prod([[X,1],[Y,1]]),1]]),T), inner_product(Xs,Ys,T,Z).
inner_product([],[],Z,Z).

matrix_vector_product(M,V,P) :- matrix_vector_product(M,V,[],P).
matrix_vector_product([R|Ms],V,Temp,P) :- inner_product(R,V,I), append(Temp,[I],Temp1), matrix_vector_product(Ms,V,Temp1,P), !.
matrix_vector_product([],_,P,P).

matrix_product(A,B,C) :- A=[R|_], length(R,N), empty_matrix(Temp,N), matrix_product(A,B,Temp,C).
matrix_product(A,B,Temp,C) :- get_column(B,K), remove_column(B,R), matrix_vector_product(A,K,P), append_column(Temp,P,Temp1), matrix_product(A,R,Temp1,C), !.
matrix_product(_,B,C,C) :- empty_matrix(B).

/* Expansion
********************/

expand_product(Product,Expansion) :- Product=prod(P), decrease_gms(sum(B),1,P,P1), expand_product(P1,B,Expansion).
expand_product(P,T,E) :- decrease_gms(sum(B),1,P,P1), gms_cartesian_product(T,B,T1), gmss_to_polinomial(T1,sum(T2)), expand_product(P1,T2,E), !.
expand_product(P,T,E) :- gms_non_member(sum(_),P), gms_cartesian_product(T,[[prod(P),1]],A), gmss_to_polinomial(A,E).

gmss_to_polinomial(G,S) :- gmss_to_polinomial(G,[],S).
gmss_to_polinomial([G|Gs],T,S) :- G=[P,M], append(T,[[prod(P),M]],T1), gmss_to_polinomial(Gs,T1,S), !.
gmss_to_polinomial([],S,sum(S)).

/* Simplification
********************/

non_simple(X,Y) :- simp(X,Y), X\=Y.

% Numbers
simp(N,S) :- number(N), number_chars(N,C), sublist(A,B,['.','0'],C), append(A,B,D) , number_chars(S,D), !.

% Sum
simp(sum([]),0) :- !.
simp(sum(X),Y) :- X=[[A,1]], simp(A,Y), !.
simp(sum(X),Y) :- gms_member(0,X,M), select_from_gms(0,M,X,C), simp(sum(C),Y), !.
simp(sum(X),Y) :- non_simple(X,Z), simp(sum(Z),Y), !.
simp(sum(X),Y) :- S=sum(W), gms_member(S,X,M), select_from_gms(S,M,X,C), multiply_multiplicity(W,M,K), append(C,K,L), correct_gms(L,N), simp(sum(N),Y), !.
simp(sum(X),Y) :- gms_member(A,X,M), number(A), gms_member(B,X,N), number(B), A\=B, select_from_gms(A,M,X,C), select_from_gms(B,N,C,D), E is A*M+B*N, put_into_gms(E,1,D,F), simp(sum(F),Y), !.

% Sum with trigonometric terms
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N>=1, gms_member(sin(A),P1,2), gms_member(cos(B),P2,2), equal(A,B), gms_difference(P1,[[sin(A),2]],D1), gms_difference(P2,[[cos(B),2]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,C), decrease_gms(prod(P2),1,C,D), put_into_gms(prod(D1),1,D,E), simp(sum(E),Y), !. % sin(x)^2 + cos(x)^2
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N=<(-1), not(equal_gms(P1,P2)), gms_member(cos(B),P2,2), gms_difference(P2,[[cos(B),2]],P1), decrease_gms(prod(P1),1,X,C), decrease_gms(prod(P2),1,C,D), G=prod([[prod(P1),1],[sin(B),2]]), put_into_gms(G,1,D,E), simp(sum(E),Y), !. % 1 - cos(x)^2
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N=<(-1), not(equal_gms(P1,P2)), gms_member(sin(B),P2,2), gms_difference(P2,[[sin(B),2]],P1), decrease_gms(prod(P1),1,X,C), decrease_gms(prod(P2),1,C,D), G=prod([[prod(P1),1],[cos(B),2]]), put_into_gms(G,1,D,E), simp(sum(E),Y), !. % 1 - sin(x)^2
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N>=1, gms_member(sin(A),P1,1), gms_member(cos(B),P2,1), equal(A,B), gms_member(cos(C),P1,1), gms_member(sin(D),P2,1), equal(C,D), gms_difference(P1,[[sin(A),1],[cos(C),1]],D1), gms_difference(P2,[[cos(B),1],[sin(D),1]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,E), decrease_gms(prod(P2),1,E,F), G=prod([[prod(D1),1],[sin(sum([[A,1],[D,1]])),1]]), put_into_gms(G,1,F,H), simp(sum(H),Y), !. % sin(a)cos(b) + cos(a)sin(b)
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N=<(-1), gms_member(sin(A),P1,1), gms_member(cos(B),P2,1), equal(A,B), gms_member(cos(C),P1,1), gms_member(sin(D),P2,1), equal(C,D), gms_difference(P1,[[sin(A),1],[cos(C),1]],D1), gms_difference(P2,[[cos(B),1],[sin(D),1]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,E), decrease_gms(prod(P2),1,E,F), G=prod([[prod(D1),1],[sin(sum([[A,1],[D,-1]])),1]]), put_into_gms(G,1,F,H), simp(sum(H),Y), !. % sin(a)cos(b) - cos(a)sin(b)
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M=<(-1), gms_member(prod(P2),X,N), N=<(-1), gms_member(sin(A),P1,1), gms_member(cos(B),P2,1), equal(A,B), gms_member(cos(C),P1,1), gms_member(sin(D),P2,1), equal(C,D), gms_difference(P1,[[sin(A),1],[cos(C),1]],D1), gms_difference(P2,[[cos(B),1],[sin(D),1]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,E), decrease_gms(prod(P2),1,E,F), G=prod([[prod(D1),1],[sin(sum([[A,1],[D,1]])),1]]), put_into_gms(G,-1,F,H), simp(sum(H),Y), !. % -sin(a)cos(b) - cos(a)sin(b)
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N>=1, gms_member(cos(A),P1,1), gms_member(cos(B),P1,1), not(equal(A,B)), gms_member(sin(C),P2,1), gms_member(sin(D),P2,1), not(equal(C,D)), equal(A,C), equal(B,D), gms_difference(P1,[[cos(A),1],[cos(B),1]],D1), gms_difference(P2,[[sin(C),1],[sin(D),1]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,E), decrease_gms(prod(P2),1,E,F), G=prod([[prod(D1),1],[cos(sum([[A,1],[B,-1]])),1]]), put_into_gms(G,1,F,H), simp(sum(H),Y), !. % cos(a)cos(b) + sin(a)sin(b)
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M>=1, gms_member(prod(P2),X,N), N=<(-1), gms_member(cos(A),P1,1), gms_member(cos(B),P1,1), not(equal(A,B)), gms_member(sin(C),P2,1), gms_member(sin(D),P2,1), not(equal(C,D)), equal(A,C), equal(B,D), gms_difference(P1,[[cos(A),1],[cos(B),1]],D1), gms_difference(P2,[[sin(C),1],[sin(D),1]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,E), decrease_gms(prod(P2),1,E,F), G=prod([[prod(D1),1],[cos(sum([[A,1],[B,1]])),1]]), put_into_gms(G,1,F,H), simp(sum(H),Y), !. % cos(a)cos(b) - sin(a)sin(b)
simp(sum(X),Y) :- gms_member(prod(P1),X,M), M=<(-1), gms_member(prod(P2),X,N), N=<(-1), gms_member(cos(A),P1,1), gms_member(cos(B),P1,1), not(equal(A,B)), gms_member(sin(C),P2,1), gms_member(sin(D),P2,1), not(equal(C,D)), equal(A,C), equal(B,D), gms_difference(P1,[[cos(A),1],[cos(B),1]],D1), gms_difference(P2,[[sin(C),1],[sin(D),1]],D2), equal_gms(D1,D2), decrease_gms(prod(P1),1,X,E), decrease_gms(prod(P2),1,E,F), G=prod([[prod(D1),1],[cos(sum([[A,1],[B,-1]])),1]]), put_into_gms(G,-1,F,H), simp(sum(H),Y), !. % -cos(a)cos(b) - sin(a)sin(b)

% Product
simp(prod([]),1) :- !.
simp(prod(X),0) :- gms_member(0,X,_), !.
simp(prod(X),Y) :- X=[[A,1]], simp(A,Y), !.
simp(prod(X),Y) :- gms_member(1,X,M), select_from_gms(1,M,X,C), simp(prod(C),Y), !.
simp(prod(X),Y) :- non_simple(X,Z), simp(prod(Z),Y), !.
simp(prod(X),Y) :- P=prod(W), gms_member(P,X,M), select_from_gms(P,M,X,C), multiply_multiplicity(W,M,K), append(C,K,L), correct_gms(L,N), simp(prod(N),Y), !.
simp(prod(X),Y) :- gms_member(A,X,M), number(A), gms_member(B,X,N), number(B), A\=B, select_from_gms(A,M,X,C), select_from_gms(B,N,C,D), E is A^M*B^N, put_into_gms(E,1,D,F), simp(prod(F),Y), !.
simp(prod(X),Y) :- P=sum(_), gms_member(P,X,_), expand_product(prod(X),E), simp(E,Y), !.

% Trigonometric
simp(sin(X),Y) :- number(X), sin(X,R), simp(R,Y), !. 
simp(cos(X),Y) :- number(X), cos(X,R), simp(R,Y), !. 
simp(sin(pi/2),1) :- !.
simp(cos(pi/2),0) :- !.
simp(sin(sum(X)),Y) :- X=[[E,M]], M<0, N is -M, simp(sum([[sin(sum([[E,N]])),-1]]),Y), !. 
simp(cos(sum(X)),Y) :- X=[[E,M]], M<0, N is -M, simp(cos(sum([[E,N]])),Y), !. 
simp(sin(X),sin(Y)) :- simp(X,Y), !.
simp(cos(X),cos(Y)) :- simp(X,Y), !.

% Generalized multisets
simp(B,S) :- gms_member(E,B,M), number(E), M<0, N is -M, F is -E, select_from_gms(E,M,B,C), put_into_gms(F,N,C,D), simplify_multiplicities(D,G), simp(G,S), !.
simp(B,S) :- correct_gms(B,C), B\=C, simp(C,S), !.
simp(B,S) :- C=[E,M], member(C,B), non_simple(E,F), select(C,B,D), append(D,[[F,M]],G), simp(G,S), !.

% Catch all
simp(X,X).

/* Factorization
********************/

factor_binomial(Term1,Term2,Product) :- Term1=prod(A), Term2=prod(B), gms_intersection(A,B,I), gms_difference(A,I,C), gms_difference(B,I,D), simp(prod([[prod(I),1],[sum([[prod(C),1],[prod(D),1]]),1]]),Product), !.

/* Differentiation
*************************/

% Vars & constants
deriv(v(X),time,v(dot(X))) :- !.
deriv(v(X),X,1) :- !. % x' -> 1
deriv(v(_),_,0) :- !. % dx/dy -> 0
deriv(c(_),_,0) :- !. % const' -> 0
deriv(X,_,0) :- number(X), !.

% Trigonometric
deriv(sin(X),D,Y) :- deriv(X,D,E), simp(prod([[E,1],[cos(X),1]]),Y), !.
deriv(cos(X),D,Y) :- deriv(X,D,E), simp(prod([[E,1],[sum([[sin(X),-1]]),1]]),Y), !.

% Sum
deriv(sum(X),D,Y) :- m_deriv(X,D,[],W), simp(sum(W),Y), !.

% Power
deriv(pow([X,Y]),D,Z) :- number(Y), deriv(X,D,E), M is Y-1, simp(prod([[E,1],[Y,1],[X,M]]),Z), !.	% (x^const)' -> const * x' * x^(const-1)

% Product
deriv(prod(X),D,Y) :- p_deriv(X,X,D,[],Y), !.

% Multiset derivative
deriv(M,D,Y) :- m_deriv(M,D,[],Y).

% List derivative
deriv(List,D,Y) :- l_deriv(List,D,[],Y), !.

% Gradient
gradient(Function,Variables,G) :- gradient(Function,Variables,[],G). % Variables is a list of the variables [var1, var2, ...].
gradient(Function,[Variable|Variables],Temp,G) :- deriv(Function,Variable,D), append(Temp,[D],Temp1), gradient(Function,Variables,Temp1,G), !.
gradient(_,[],G,G).

% Aux
l_deriv([X|Xs],D,Temp,Y) :- deriv(X,D,E), append(Temp,[E],Temp1), l_deriv(Xs,D,Temp1,Y), !.
l_deriv([],_,Y,Y).

m_deriv([M|Ms],D,T,Y) :- M=[E,N], deriv(E,D,F), append(T,[[F,N]],T1), m_deriv(Ms,D,T1,Y), !.
m_deriv([],_,Y,Y).

p_deriv([E|Es],X,D,T,Y) :- deriv(pow(E),D,prod(Z)), select(E,X,F), append(F,Z,G), correct_gms(G,H), append(T,[[prod(H),1]],T1), p_deriv(Es,X,D,T1,Y), !.
p_deriv([],_,_,T,Y) :- simp(sum(T),Y).

% Dotted symbols
insert_ddot(Variable,v(dot(dot(Variable)))) :- !.

insert_dot(Variable,v(dot(Variable))) :- atomic(Variable), !.

insert_dot(VariablesVector,V) :- insert_dot(VariablesVector,[],V).
insert_dot([Variable|Variables],Temp,V) :- append(Temp,[dot(Variable)],Temp1), insert_dot(Variables,Temp1,V), !.
insert_dot([],V,V).

/* Translator to Octave/Matlab
********************/

rewrite_m(X,Y) :- X\=[_|_], decompose_to_list(X,W), simp_list_form(W,Z), list_form_to_formula(Z,Y), !.
rewrite_m(X,Y) :- X=[_|_], rewrite_m(X,[],Y).

rewrite_m([X|Xs],T,Y) :- rewrite_m(X,A), append(T,[A],T1), rewrite_m(Xs,T1,Y), !.
rewrite_m([],Y,Y).

decompose_to_list(X,list_form([X])) :- atomic(X), !.

decompose_to_list(c(X),Y) :- decompose_to_list(X,Y), !.
decompose_to_list(v(X),Y) :- decompose_to_list(X,Y), !.

decompose_to_list(sin(X),Y) :- decompose_to_list(X,list_form(A)), append([sin,'('],A,B), append(B,[')'],C), simp_list_form(list_form(C),Y), !.
decompose_to_list(cos(X),Y) :- decompose_to_list(X,list_form(A)), append([cos,'('],A,B), append(B,[')'],C), simp_list_form(list_form(C),Y), !.

decompose_to_list(dot(X),list_form([Z])) :- rewrite_m(X,Y), string_concat("d",Y,N), string_to_atom(N,Z), !.

decompose_to_list(sum(X),list_form(Y)) :- sum_gms_to_list_form(X,[],list_form(L)), append(['('],L,K), append(K,[')'],Y), !.

decompose_to_list(prod(X),Y) :- prod_gms_to_list_form(X,[],Y), !.

sum_gms_to_list_form([X|Xs],T,L) :- X=[E,M], not(non_atomic_product(E)), decompose_to_list(E,list_form(F)),  append([+,M,*],F,G), append(T,G,T1), sum_gms_to_list_form(Xs,T1,L), !.
sum_gms_to_list_form([X|Xs],T,L) :- X=[E,M], non_atomic_product(E), simp(E,prod(F)), member([H,N],F), number(H), select([H,N],F,G), Q is M*H^N, simp(Q,I), decompose_to_list(prod(G),list_form(J)), append([+,I,*],J,K), append(T,K,T1), sum_gms_to_list_form(Xs,T1,L), !.
sum_gms_to_list_form([],L,list_form(L)).

prod_gms_to_list_form([X|Xs],T,L) :- X=[E,M], decompose_to_list(E,list_form(F)), append([*],F,G), append(G,[^,M],H), append(T,H,T1), prod_gms_to_list_form(Xs,T1,L), !.
prod_gms_to_list_form([],L,list_form(L)).

non_atomic_product(prod(X)) :- non_atomic_gms(X), !.

simp_list_form(list_form(L),K) :- L=[*|Ls], simp_list_form(list_form(Ls),K), !.
simp_list_form(list_form(L),K) :- L=[+|Ls], simp_list_form(list_form(Ls),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist(['(',+],['('],L,N), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist(['(',*],['('],L,N), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([+,-],[-],L,N), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([*,*],[*],L,N), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([+,*],[+],L,N), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([+,X],[X],L,N), number(X), X<0, simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([W,X,*,Y,Z],[W,U,Z],L,N), number(X), number(Y), W\=(^), Z\=(^), U is X*Y, simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([X,^,Y],[W],L,N), number(X), number(Y), W is X^Y, simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([X,'(',Y,')'],[X,Y],L,N), not(trig(X)), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([A,1,*],[A],L,N), A\=(^), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([B,-1,*,A],[B,-,A],L,N), B\=(^), simp_list_form(list_form(N),K), !.
simp_list_form(list_form(L),K) :- substitute_sublist([^,1],[],L,N), simp_list_form(list_form(N),K), !.
simp_list_form(X,X).

list_form_to_formula(L,F) :- list_form_to_formula(L,"",F).
list_form_to_formula(list_form([L|Ls]),T,F) :- string_concat(T,L,T1), list_form_to_formula(list_form(Ls),T1,F), !.
list_form_to_formula(list_form([]),S,S).

trig(sin).
trig(cos).

/* Results Storage
********************/

write_matrix(M,Name) :- name_m(M,Name,0,[],E), write_e(E), write(Name), write(" = "), write("["), length(M,L), write_m(M,Name,L,0).

write_vector(V,Name) :- name_r(V,Name,"",0,[],E), write_e(E), write(Name), write(" = "), write("["), length(V,L), write_v(V,Name,L,"",0,";"), write("];\n\n").

name_m([R|T],N,C,Temp,E) :- C1 is C+1, name_r(R,N,C1,0,[],RE), append(Temp,RE,T1), name_m(T,N,C1,T1,E), !.
name_m([],_,_,E,E).

name_r([E|T],N,RC,CC,ET,Es) :- CC1 is CC+1, string_concat(RC,CC1,EI), string_concat(N,EI,EN), rewrite_m(E,F), append(ET,[[EN,F]],ET1), name_r(T,N,RC,CC1,ET1,Es), !.
name_r([],_,_,_,H,H).

write_m([R|T],N,L,C) :- C1 is C+1, length(R,RL), write("["), write_v(R,N,RL,C1,0,","), write("]"), write_separator(";",C1,L), write_m(T,N,L,C1), !.
write_m([],_,_,_) :- write("];\n\n").

write_v([_|T],N,L,RC,CC,S) :- CC1 is CC+1, string_concat(RC,CC1,EI), string_concat(N,EI,EN), write(EN), write_separator(S,CC1,L), write_v(T,N,L,RC,CC1,S).
write_v([],_,_,_,_,_).

write_e([E|Es]) :- E=[EN,EF], write(EN), write(" = "), write(EF), write(";\n"), write_e(Es), !.
write_e([]) :- write("\n"). 

write_separator(Separator,Index,MaxIndex) :- Index\=MaxIndex, write(Separator), !. 
write_separator(_,Index,MaxIndex) :- Index=MaxIndex, !. 
