:- module(subtle, [lgg/3, reduce/2, subsumes/2, subsumes/3, equiv/2]).

:- use_module(library(lists)).
:- use_module(library(terms), [subsumes_chk/2, term_variables/2, variables_within_term/3]).
:- use_module(library(charsio)).

% NOTE: All clauses are represented as lists of literals.
%
% EXPORTED PREDICATES:
% lgg(+X,+Y,-Z) <=> Z is the lgg under theta-subsumption of X and Y
% reduce(+X,-Y) <=> Y is the reduced clause of X (shortest clause for which equiv(X,Y) holds)
% subsumes(+X,+Y) <=> X subsumes Y
% subsumes(+X,+Y,-S) <=> X subsumes Y and S is a substitution that proves this
% equiv(+X,+Y) <=> X subsumes Y and Y subsumes X


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PART 1 : computing the lgg of 2 clauses %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lgg(Clause1, Clause2, Result) :- 
	lggI(Clause1, Clause2, [], Clause3, _),   % compute lgg (without reduction)
	reduceClause(Clause3, Result).            % reduce resulting clause


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lgg computation step 1 (no reduction yet) %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% compute the lgg of each atom of first clause with each atom of second clause;
% include all defined lggs in the result
lggI([], Clause, Varlist, [], Varlist).
lggI([A|RClause], Clause2, Varlist, Clause3, NewVarlist) :-
	lggI2(A, Clause2, Varlist, AClause, Varlist2),
	append(AClause, Clause4, Clause3),
	lggI(RClause, Clause2, Varlist2, Clause4, NewVarlist).

% compare one atom with all atoms in second clause
lggI2(Atom, [], VL, [], VL).
lggI2(Atom, [A|Rest], Varlist, NewClause, NewVarlist) :-
	lggAtomI(Atom, A, Varlist, A2, VL2) 
	-> NewClause=[A2|R2], lggI2(Atom, Rest, VL2, R2, NewVarlist)
	; lggI2(Atom, Rest, Varlist, NewClause, NewVarlist).

% compute lgg of two atoms
lggAtomI(not X,not Y,Varlist,not Z,NewVarlist):-
	!,
	X =.. [PredX|ArgsX], 
	Y =.. [PredY|ArgsY],
	PredX = PredY,
	lggTermsI(ArgsX, ArgsY, Varlist, ArgsZ, NewVarlist),
	Z =.. [PredX | ArgsZ].
lggAtomI(X, Y, Varlist, Z, NewVarlist) :-  
	X =.. [PredX|ArgsX], 
	Y =.. [PredY|ArgsY],
	PredX = PredY,
	lggTermsI(ArgsX, ArgsY, Varlist, ArgsZ, NewVarlist),
	Z =.. [PredX | ArgsZ].

lggTermsI([], [], Varlist, [], Varlist).
lggTermsI([T1|Rest1], [T2|Rest2], Varlist, [T3|Rest3], NewVarlist) :-
	lggTermI(T1, T2, Varlist, T3, Varlist2),
	lggTermsI(Rest1, Rest2, Varlist2, Rest3, NewVarlist).

lggTermI(X, Y, Varlist, Z, Varlist2) :- 
	(var(X); var(Y)), 
	!,
	(X == Y -> Z=X, Varlist2 = Varlist;
	 membervar(var(X,Y,Z), Varlist) -> Varlist2=Varlist; 
	 Varlist2 = [var(X,Y,Z)|Varlist]).
lggTermI(X, Y, Varlist, Z, Varlist2) :-
	X =.. [FX|AX],   % FX = functor, AX = argument list
	Y =.. [FY|AY],
	FX = FY -> lggTermsI(AX, AY, Varlist, AZ, Varlist2), Z =.. [FX | AZ];
	membervar(var(X,Y,Z), Varlist) -> Varlist2=Varlist;
	Varlist2 = [var(X,Y,Z)|Varlist].

membervar(var(X,Y,Z), [var(A,B,C)|D]) :- X==A, Y==B, Z=C.
membervar(var(X,Y,Z), [_|D]) :- membervar(var(X,Y,Z), D).


%%%%%%%%%%%%%%%%%%%%%%%
% reduction of clause %
%%%%%%%%%%%%%%%%%%%%%%%

% implements â€˜uniqueness propagationâ€™, see ILP 2016 short paper
% + optimization proposed by Maloberti & Suzuki
% + quick removal of literals that subsume something and donâ€™t share variables with anything
% this version assumes the original clause is free of â€˜$VARâ€™(_) terms

reduceClause(C, RedC) :- 
	constructUnique(C, 0, [], Unique, Rest),
	dropLitsWithUniqueVars(Rest, [], Unique, Rest2), 
	redC(Rest2,Unique,RedC1),
	write_to_chars(RedC1,Charlist), read_from_chars(Charlist, RedC). %unnumbervars

constructUnique(C, N, PrevU, U, Rest) :- 
	findUnique(C, U1, Rest1), 
	(U1 = PrevU 
	 -> U=U1, Rest=Rest1
	 ; numbervars(U1, N, N1), constructUnique(C, N1, U1, U, Rest)
	).

findUnique([], [], []).
findUnique([A|B], Unique, Rest) :-
	getEquiv(A, B, Unifs, RestB, Sub), 
	(Sub=false
	-> Unique = [A|U], append(Unifs, R, Rest), findUnique(RestB, U, R)
	; append([A|Unifs], R, Rest), findUnique(RestB, Unique, R)).

% returns Sub=true iff A subsumes at least one atom, + returns all atoms that subsume A - those certainly aren't unique
getEquiv(A, [], [], [], false).
getEquiv(A, [B|C], Unifs, RestB, Sub) :-
	subsumes_chk(A,B)
	-> Sub=true, 
	   (subsumes_chk(B,A) -> Unifs=[B|U], RestB=RestC; Unifs=U, RestB=[B|RestC]),
	   getEquiv(A, C, U, RestC, _)
	; (subsumes_chk(B,A) -> Unifs=[B|U], RestB=RestC; Unifs=U, RestB=[B|RestC]), 
	  getEquiv(A, C, U, RestC, Sub).

dropLitsWithUniqueVars([], Earlier, Unique, Earlier).
dropLitsWithUniqueVars([A|Later], Earlier, Unique, Out) :-
	noSharedVars(A,Earlier), noSharedVars(A,Later), \+ \+ member(A, Unique)  
	-> dropLitsWithUniqueVars(Later, Earlier, Unique, Out)
	; dropLitsWithUniqueVars(Later, [A|Earlier], Unique, Out).

  noSharedVars(A, L) :- term_variables(A, VA), term_variables(L, VL), varsDisjoint(VA, VL).

  varsDisjoint([], _).
  varsDisjoint([A|B], L) :- \+ (member(X, L), X == A), varsDisjoint(B, L).


% Gottlobâ€™s method: check each literal once, to see if it can be removed
% + Maloberti & Suzukiâ€™s optimization: immediately remove all literals affected by the found substitution

redC([], Necessary, Necessary).
redC([A|B], Necessary, RedC) :-
	append(Necessary, B, All),
	(subsumes([A|All], All, Subst) 
		-> removeAffected(B, Subst, B2), redC(B2, Necessary, RedC) 
		; redC(B, [A|Necessary], RedC)).

removeAffected([], _, []).
removeAffected([Lit|Rest], Subst, Rest2) :- 
	affected(Lit, Subst) 
	-> removeAffected(Rest, Subst, Rest2)
	; Rest2=[Lit|Rest3], removeAffected(Rest, Subst, Rest3).

affected(Lit, Subst) :- term_variables(Lit, TV), member(X/Y, Subst), memberID(X, TV), !.

memberID(Var, [A|B]) :- Var==A -> true; memberID(Var, B).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PART 1 : theta-subsumption testing %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% method for testing whether C subsumes D: 
% first skolemize D and divide C into independent components
% then, for each independent component C:
% CONSTRUCT DB:
% for each literal Lit in C, 
% . construct a tuple of variables as they occur in Lit
% . try to match Lit with all literals in D, keep a list of all instantiations thus obtained (= VIL)
% . example:  [f(X,Y)] / [f(a,b), f(a,c), f(d,e)]  lists possible instantiations of tuple X,Y
% . if the variables in this tuple are a subset of those in another variable tuple, or vice versa: 
%   semi-join superset tuple with subset tuple, drop subset tuple
% . if the variables in this tuple overlap with those of another tuple: replace both by their semijoin with the other
% SIMPLIFY:
% for all pairs of tuples with overlapping variables: semi join their VILS; repeat until no change
% SEARCH:
% among all vartuples, choose the one with shortest VIL / most vars
% for each member of this VIL:
% . unify vartuple with it
% . filter other VILs: remove inconsistent members
% . if any VIL becomes empty, fail
% . if no free vars remain, succeed
% . otherwise, call SEARCH recursively

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% theta-subsumption and equivalence tests %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

equiv(X,Y) :- subsumes(X,Y,_), subsumes(Y,X,_).

subsumes(X, Y) :- subsumes(X, Y, _).

subsumes(X, Y, Sub) :- 
	copy_term(X, X2), term_variables(X, VarsX), term_variables(X2, VarsX2),
	copy_term(Y, Y2), term_variables(Y, VarsY), term_variables(Y2, VarsY2), 
	skolemize(Y2), makeCC(X2, CCList), processCC(CCList, Y2),  
	makeSubst(VarsX, VarsX2, Sub1),	makeSubst(VarsY2, VarsY, Sub2),	composeSubst(Sub1, Sub2, Sub).

    makeSubst([], [], []).
    makeSubst([Var|VRest], [Inst|IRest], Rest) :- Var==Inst, !, makeSubst(VRest, IRest, Rest).
    makeSubst([Var|VRest], [Inst|IRest], [Var/Inst|Rest]) :- makeSubst(VRest, IRest, Rest).

    % assumes I is always instantiated!  this is true where itâ€™s called in our code
    composeSubst([], _, []).
    composeSubst([V/I|Rest], Subs, NewSubst) :- 
		(member(I/J, Subs)  
			-> (J == V -> NewSubst=Rest2; NewSubst=[V/J|Rest2])
			; NewSubst=[V/I|Rest2]),
		composeSubst(Rest, Subs, Rest2).


%%%%%%%%%%%%%
% skolemize %
%%%%%%%%%%%%%

% skolemize using numbervars, but avoid use of $VAR(N) terms that already occur!

skolemize(C) :- nextNumber(C, N), numbervars(C, N, _).

    nextNumber(C, N) :- findall(X, inside('$VAR'(X), C), List), (max_list(List, Max) -> N is Max+1; N=0).

    inside(X, C) :- var(C), !, fail; C=X; C =.. [F|Args], insideList(X, Args).

    insideList(X, [A|B]) :- inside(X,A); insideList(X, B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% create independent components %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

makeCC([], []).
makeCC([A|B], [CC|Rest]) :- oneCC(B, [A], CC, Unlinked), makeCC(Unlinked, Rest).

    oneCC([], Prev, Prev, []) :- !.
    oneCC(Clause, Prev, CC, Rest) :-
	gatherLinkedLits(Clause, Prev, Linked, Unlinked), 
	(Linked = [] 
	 -> CC=Prev, Rest=Unlinked
	 ; append(Linked, Prev, NewPrev), oneCC(Unlinked, NewPrev, CC, Rest)).

    gatherLinkedLits([], Prev, [], []).
    gatherLinkedLits([A|Rest], Prev, Linked, Unlinked) :-
	gatherLinkedLits(Rest, Prev, L1, U1),
	(linked(A, Prev) -> Linked = [A|L1], Unlinked=U1; Linked=L1, Unlinked=[A|U1]).

    linked(A, List) :- 
	term_variables(A, Vars1), variables_within_term(Vars1, List, Shared), Shared \= [].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% solve each independent component independently %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

processCC([], _).
processCC([CC|Rest], GroundClause) :- 
	makeTable(CC, GroundClause, Table),   % makeTable can fail => no solutions
	simplifyTable(Table,STable),          % simplifyTable can fail => no solutions
	solve(STable), !,                     % solve can fail => no solutions
	processCC(Rest, GroundClause).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% create the table with all VILs %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

makeTable([], _, []).
makeTable([A|B], GrClause, [row(A2,IL2)|Rest]) :- 
	filter(A, GrClause, IL), 
	term_variables(A, Vars), 
	sort(Vars, SV), A2 =.. [f|SV],
	findall(A2, member(A, IL), InstL),
	sort(InstL, IL2),
	makeTable(B, GrClause, Rest).

filter(Lit, [], []).
filter(Lit, [A|B], C) :- Lit \= A -> filter(Lit, B, C); C=[A|C1], filter(Lit, B, C1).

%%%%%%%%%%%%%%%%%%%%%%
% simplify the table %
%%%%%%%%%%%%%%%%%%%%%%

simplifyTable(Table, NewTable) :-
	simpTab(Table, Table2), 
	(Table == Table2 -> NewTable=Table2; simplifyTable(Table2, NewTable)).

simpTab([], []).
simpTab([drop|Rest], NewTable) :- !, simpTab(Rest, NewTable).   % skip dropped rows
simpTab([Row|Rest], NewTable) :-
	checkRow(Row, Rest, Row2, Rest2), 
	(Row2==drop -> simpTab(Rest2, NewTable);
	 NewTable=[Row2|Rest3], simpTab(Rest2, Rest3)).

% semi join row with all other rows in the database
% if X subset of Xâ€™: stop semijoining X, since Xâ€™ will have same effect later on

checkRow(Row, [], Row, []) :- !.
checkRow(Row, [drop|Rest], NewRow, NewRest) :- !, checkRow(Row, Rest, NewRow, NewRest).  % skip dropped row
checkRow(Row, Rest, NewRow, NewRest) :-
	Rest=[Row2|Rest2],
	sjrow(Row, Row2, InterRow, NewRow2),   % drop,NewRow2; InterRow, drop; InterRow, NewRow2
	(InterRow==drop 
	-> NewRow=drop, NewRest=[NewRow2|Rest2]  % stop pruning with this row: will be caused by NewRow2
	; NewRest=[NewRow2|NewRest2], 
	  checkRow(InterRow, Rest2, NewRow, NewRest2)).

% if semi join finds an empty instantiation list, it should fail
sjrow(row(Vars1,Inst1), row(Vars2, Inst2), Row1, Row2) :-
	Vars1 == Vars2 -> intersect(Inst1, Inst2, Inst), /* Inst \= [], */ Row1=drop, Row2=row(Vars1, Inst); %  fails if [] %***
	Vars1 =.. [f|VarList1], Vars2 =.. [f|VarList2], 
	(intersect(VarList1, VarList2, []) -> Row1=row(Vars1,Inst1), Row2=row(Vars2,Inst2); % vars are disjoint: no change
	 findall(Vars1-NewInst2, (member(Vars1, Inst1), filter(Vars2, Inst2, NewInst2)), List),
	 extractInfo(List, NewInst1, NewInst2),
	 %NewInst1 \= [], NewInst2 \= [],  % fail if []Â found %***
	 (subset(VarList1, VarList2) -> Row1 = drop, Row2 = row(Vars2, NewInst2);
	  subset(VarList2, VarList1) -> Row1 = row(Vars1,NewInst1), Row2=drop;
	  Row1 = row(Vars1,NewInst1), Row2 = row(Vars2, NewInst2))).

extractInfo([], [], []).
extractInfo([I-IL|Rest], Inst1, Inst2) :-
	IL=[] -> extractInfo(Rest, Inst1, Inst2);
	Inst1 = [I|Inst1b], extractInfo(Rest, Inst1b, Inst2b), merge(IL, Inst2b, Inst2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% union, intersection and subset for sorted varlists %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

subset([], _).
subset([A|B], [C|D]) :- A==C -> subset(B,D); A @> C, subset([A|B],D).

merge([], L, L) :- !.
merge(L, [], L) :- !.
merge([A|B], [C|D], Result) :-
	A @< C -> Result=[A|Rest], merge(B, [C|D], Rest);
	A @> C -> Result=[C|Rest], merge([A|B], D, Rest);
	Result=[A|Rest], merge(B, D, Rest).

intersect([], L, []) :- !.
intersect(L, [], []) :- !.
intersect([A|B], [C|D], Result) :-
	A @< C -> intersect(B, [C|D], Result);
	A @> C -> intersect([A|B], D, Result);
	Result=[A|Rest], intersect(B, D, Rest).



%%%%%%%%%%%%%%%%%%%
% solve the table %
%%%%%%%%%%%%%%%%%%%

tableSize([], 0).
tableSize([row(_,I)|B], TS) :- length(I, Ln), tableSize(B, TS1), TS is Ln+TS1.

solve(Table) :- 
	getBest(Table, Best, RestTable),  
	%simplifyTable(Table, Stable), getBest(Stable, Best, RestTable),
	(Best = row(Lit, Instlist) -> member(Lit, Instlist), filterTable(RestTable, RT2), solve(RT2); true).

filterTable([],[]).
filterTable([row(Lit,Instlist)|Rest], [row(Lit,IL2)|Rest2]) :-
	filter(Lit, Instlist, IL2),
	IL2 \= [],
	filterTable(Rest, Rest2).

% getBest finds the highest quality row in the table and returns that row and the rest of the table
% returns â€œnoneâ€ if no variables remain => solution found
% fails if an empty instlist was found

getBest(Table, Best, RestTable) :- gb1(Table, none, 0, Best, RestTable).

gb1([], PrevBest, PrevQ, PrevBest, []).
gb1([row(Lit, Instlist)|Rest], PrevBest, PrevQ, Best, RestTable) :-
	quality(Lit, Instlist, Q),
	(Q > PrevQ 
         -> NewBest=row(Lit,Instlist), NewQ=Q, (PrevBest=none -> RestTable=RT; RestTable=[PrevBest|RT])
         ; NewBest=PrevBest, NewQ=PrevQ, RestTable=[row(Lit,Instlist)|RT]),
	gb1(Rest, NewBest, NewQ, Best, RT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% quality returns 0 if the tuple contains no vars,                        %
% fails if Instlist is empty,                                             %
% and returns a positive number otherwise (higher means better candidate) %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

quality(Lit, [], _) :- !, fail.
quality(Lit, Instlist, Q) :- 
	Lit =.. [F|Args], 
	freevars(Args, A), 
	(A=0 -> Q=0; length(Instlist, L), L>0, (L=1 -> Q=100000; Q is 5^A/L)).

    freevars([A|B], N) :- freevars(B, N1), (var(A) -> N is N1+1; N=N1).
    freevars([], 0).


