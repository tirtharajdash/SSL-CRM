
:- modeh(1,class(+mol,+class)).

:- modeb(*,symbond(+mol,+atomid,+atomid,#bondtype)).
% :- modeb(*,symbond(+mol,+atomid,-atomid,#bondtype)).
:- modeb(*,bond(+mol,-atomid_1,-atomid_2,#atomtype,#atomtype,#bondtype)).
 
:- modeb(*,atom(+mol,-atomid,#element)).

:- modeb(*,has_struc(+mol,-atomids,-length,#structype)).
% :- modeb(*,connected(+mol,#structype,-atomids,#structype,-atomids)).
:- modeb(*,connected(+mol,+atomids,+atomids)).
% :- modeb(*,fused(+mol,#structype,-atomids,#structype,-atomids)).
:- modeb(*,fused(+mol,+atomids,+atomids)).

:- modeb(1,gteq(+length,#length)).
:- modeb(1,lteq(+length,#length)).

:- modeb(1,(+atomid = +atomid)).
:- modeb(1,(+atomidids = +atomidids)).
:- modeb(1,(+length = +length)).



% :- determination(class/2,atom/3).
% :- determination(class/2,symbond/4).
% :- determination(class/2,bond/6).
:- determination(class/2,has_struc/4).
% :- determination(class/2,connected/5).
:- determination(class/2,connected/3).
% :- determination(class/2,fused/5).
:- determination(class/2,fused/3).
:- determination(class/2,lteq/2).
:- determination(class/2,gteq/2).
:- determination(class/2,'='/2).




:- set(i,3).
:- set(clauselength,3).
:- set(depth,1000).



atom(MolID,A1,T1):-
    bond(MolID,A1,_,AT1,_,_),
    map(AT1,T1).

atom(MolID,A2,T2):-
    bond(MolID,_,A2,_,AT2,_),
    map(AT2,T2).


compound_id(MolID):-
	mol(_,MolId).



has_struc(Mol,Atoms,Length,Type):-
	has_struc(Mol,_,Atoms,Length,Type).

has_struc(Mol,ring,Atoms,Length,Type):-
	ring(Mol,_,Atoms,Length,Type).
has_struc(Mol,fgroup,Atoms,Length,Type):-
	functional_group(Mol,Atoms,Length,Type).

fused(Mol,Type1,Struc1,Type2,Struc2):-
	has_struc(Mol,ring,Struc1,_,Type1),
	has_struc(Mol,ring,Struc2,_,Type2),
	Struc1 @> Struc2,
	exists_common(Struc1,Struc2).

fused(Mol,Struc1,Struc2):-
	Struc1 @> Struc2,
	exists_common(Struc1,Struc2).

exists_common(Struc1,Struc2):-
	once(intersection(Struc1,Struc2,Intersect)),
	length(Intersect,I),
	I >= 2.

connected(Mol,Type1,Struc1,Type2,Struc2):-
	has_struc(Mol,Struc1,_,Type1),
	has_struc(Mol,Struc2,_,Type2),
	Struc1 @> Struc2,
	\+ fused(Mol,Type1,Struc1,Type2,Struc2),
	member(Atom1,Struc1), member(Atom2,Struc2),
	once(symbond(Mol,Atom1,Atom2,_)).

connected(Mol,Struc1,Struc2):-
	Struc1 @> Struc2,
	\+ fused(Mol,Struc1,Struc2),
	member(Atom1,Struc1), member(Atom2,Struc2),
	once(symbond(Mol,Atom1,Atom2,_)).

% bond(Mol,AType1,A1,AType2,A2,BType):-
	% symbond(Mol,A1,A2,BType),
	% atom(Mol,A1,AType1),
	% atom(Mol,A2,AType2).

symbond(D,A1,A2,Type):-
    	bond(MolID,A1,A2,_,_,Type).
symbond(D,A1,A2,Type):-
    	bond(MolID,A2,A1,_,_,Type).


% other background predicates and utilities

gteq(X,Y):-
	number(X), number(Y), 
	X >= Y, !.
gteq(X,X):-
	number(X).

lteq(X,Y):-
	number(X), number(Y),
	X =< Y, !.
lteq(X,X):-
	number(X).

member(X,[X|_]).
member(X,[_|T]):-
	member(X,T).


has_lit(L,(L,L1),L1).
has_lit(L,(L0,L1),(L0,L2)):-
	!,
	has_lit(L,L1,L2).
has_lit(L,L,true).


intersection([],_,[]).
intersection([X|S1],S2,[X|S3]):-
	member(X,S2), !,
	intersection(S1,S2,S3).
intersection([_|S1],S2,S3):-
	intersection(S1,S2,S3).


:- [types].

:- [mols].
:- [atm_bond].
:- [two_dim].
:- [map].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% search constraints

prune((Head:-Body)):-
	has_lit(fused(Mol,Atomids1,Atomids2),Body,_),
	Atomids1 @>= Atomids2.
prune((Head:-Body)):-
	has_lit(connected(Mol,Atomids1,Atomids2),Body,_),
	Atomids1 @>= Atomids2.


prune((Head:-Body)):-
	has_lit(lteq(A1,B),Body,Left),
	has_lit(lteq(A2,C),Left,_),
	A1 == A2.

prune((Head:-Body)):-
	has_lit(gteq(A1,B),Body,Left),
	has_lit(gteq(A2,C),Left,_),
	A1 == A2.


prune((Head:-Body)):-
	has_lit(connected(Mol,_,Atomids1,_,Atomids2),Body,_),
	Atomids1 == Atomids2.

prune((Head:-Body)):-
	has_lit(fused(Mol,_,Atomids1,_,Atomids2),Body,_),
	Atomids1 == Atomids2.

