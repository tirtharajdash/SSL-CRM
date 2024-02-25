% :- [back].
:- [back1].

% illegal(A,B,C,D,C,E).
% illegal(A,B,C,D,E,D).
% illegal(A,B,C,D,E,F):- adj(A,E), adj(B,F).

% target(1,illegal(A,B,C,D,C,E)).
%	target(a1,(illegal(A,B,C,D,C,E):- file_in_between(A,B,C,D,C,E))).
% target(2,illegal(A,B,C,D,E,D)).
% target(3,(illegal(A,B,C,D,E,F):- adj(A,E), adj(B,F))).
% target(4,illegal(A,B,A,B,C,D)).
% target(5,(illegal(A,B,C,D,E,F):- adj(D,F), adj(B,F),A=E)).

test_instance(Instance):-
	target(Id,Clause),
	((Clause = (Instance:-Body)) -> call(Body);
		Clause = Instance),
	numbervars(Clause,0,_),
	(line(Line) ->
		write(Line), write(' '),
		write(target(Id,Clause)), write('.'), nl;
		write(target(Id,Clause)), write('.'), nl),
	fail.
test_instance(_).

:- dynamic(line/1).

test_instances(File):-
	open(File,read,Stream),
	retractall(line(_)),
	asserta(line(0)),
	repeat,
	read(Stream,Instance),
	retract(line(N0)),
	N1 is N0 + 1,
	asserta(line(N1)),
	(Instance = end_of_file -> close(Stream);
		test_instance(Instance),
		fail).
