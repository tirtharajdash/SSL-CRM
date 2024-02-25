:- source.

:- op(500,fy,#).

:- op(900,xfy,::).

:- [subtle].


:- dynamic mode/1.
:- dynamic determ/2.

:- dynamic cache/1.
:- dynamic type/2.
:- dynamic var_setting/2.

:- multifile prune/1.
:- multifile var_setting/2.

:- dynamic '$aleph_feature_count'/1.
:- dynamic '$aleph_feature_weight'/2.
:- dynamic '$aleph_feature'/5.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% simple depth-bounded theorem-prover for a Goal

prove(Depth,_,N-LitsSoFar,_):-
	N > Depth, !,
	fail.
prove(Depth,Goal,N-LitsSoFar,[]):-
	N =< Depth,		% at most Depth
	% N == Depth,		% exactly Depth
	proved(Goal,LitsSoFar).
prove(Depth,Goal,N-LitsSoFar,[Lit|Lits]):-
	N < Depth,
	determ(Goal,Lit),
	can_prove(Lit,LitsSoFar),
	\+ redundant_literal(Lit,LitsSoFar),
	N1 is N + 1,
	prove(Depth,Goal,N1-[Lit|LitsSoFar],Lits).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
gen_features(Depth,Epsilon,Prec,Support):-
	debug_write('Parameters:'), debug_write(Depth/Epsilon/Prec/Support),
	debug_write(nl),
	set_var(min_precision,Prec),
	set_var(min_support,Support),
	set_var(feature_count,0),
	meta_prove(pos,1,Depth,Epsilon),
	instantiate_templates,
	gen_features_from_instantiations,
	show_features.

gen_features_from_instantiations:-
	in_cache(instantiate_template(_,Lits)),
	list2clause(Lits,Clause),
	gen_feature(Clause),
	fail.
gen_features_from_instantiations:-
	var_setting(feature_count,F),
	assertz('$aleph_feature_count'(F)).


% meta-interpretive construction of templates
%	for simple clauses

meta_prove(Type,Id,Depth,Epsilon):-
	cache_mode_args,
	set_var(epsilon,Epsilon),
	example(Id,Pos,Example),
	get_templates(Depth,Example).
	% select_template(Example,Template),
	% get_clause_stats(Template,Clause,Stats),
	% update_cache(clause(stats([type-Type,id-Id|Stats]),Clause)),
	% fail.

instantiate_templates:-
	select_template([Head|Body]),
	ground_lits(Body),
	update_cache(instantiate_template(Head,[Head|Body])),
	debug_write('Instantiated Template: '), debug_write([Head|Body]), debug_write(nl),
	fail.
instantiate_templates.


ground_lits([]).
ground_lits([Lit|Lits]):-
	in_cache(const_args(Lit,Const)),
	ground_lit(Const,Lit),
	ground_lits(Lits).


ground_lit([],_).
ground_lit([Arg/Type|ArgTypes],Lit):-
	arg(Arg,Lit,Var),
	TypeCall =.. [Type,Var],
	TypeCall,
	ground_lit(ArgTypes,Lit).
	
	

select_template([Example|Lits]):-
	in_cache(template(Example,[Example|Lits])).
	
% meta_prove(Type,Id,Depth):-
	% (var_setting(min_weight,MinWt) -> true; MinWt = 0),
	% cache(clause(stats(Stats),_)),
	% get_weight(Stats,Wt),
	% Wt >= MinWt, !.

% assumes at most 1 output arg given by setting dependent var in
% back.pl
gen_feature(Clause):-
        (setting(dependent,PredictArg) -> true; PredictArg is 0),
        split_clause(Clause,Head,Body),
        Body \= true,
        functor(Head,Name,Arity),
        functor(Template,Name,Arity),
        copy_iargs(Arity,Head,Template,PredictArg),
        get_feature_class(PredictArg,Head,Body,Class),
        gen_feature((Template:-Body),[],Class), !.


get_feature_class(Argno,Head,Body,Class):-
        has_class(Argno,Head,Body,Class), !.
get_feature_class(_,_,_,_).

has_class(Argno,Head,_,Class):-
        arg(Argno,Head,Class),
        ground(Class), !.
has_class(Argno,Head,Body,Class):-
        arg(Argno,Head,DepVar),
        in((DepVar=Class),Body),
        ground(Class), !.

gen_feature(Feature,Label,Class):-
        nonvar(Feature), !,
        (var(Id) -> gen_featurenum(Id); true),
        split_clause(Feature,Template,Body),
        assertz('$aleph_feature'(Id,[],Class,Template,Body)),
        assertz('$aleph_feature_weight'(Id,1.0)).

 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mode-directed extraction of clause templates


get_templates(Depth,Example):-
	clean_up_templates,
	functor(Example,Name,Arity),
	functor(Head,Name,Arity),
	set_var(gen_template,true),
	get_template(Depth,Head,Template),
	\+ reject(Template),
	once(update_templates(Head,Template)),
	% update_cache(template(Head,Template)),
	fail.
get_templates(_,Head):-
	noset_var(gen_template).

update_templates(Head,[Head|Body]):-
	\+ contains_useless_lit(Head,Body), 
	debug_write('Template: '), debug_write([Head|Body]), debug_write(nl),
	update_cache(template(Head,[Head|Body])).

contains_useless_lit(Head,Body):-
	remove_useless_lits(Head,Body,Body1),
	Body \= Body1, !.

% update_templates(Head,[Head|BodyL]):-
	% list2goals(BodyL,Body),
	% optimise((Head:-Body),(Head:-Body1)),
	% goals2list(Body1,Body1L),
	% update_cache(template(Head,[Head|Body1L])).
	

get_template(Depth,Head,[Head|Template]):-
	get_mode(Head,_,Inputs,_,_),
	update_types(Inputs,Head),
	prove(Depth,Head,0-[Head],Template).

more_general_template(T1,T2):-
	preds_in_template(T1,P),
	preds_in_template(T2,P),
	subsumes(T1,T2),
	\+ subsumes(T2,T1).

equiv_template(T1,T2):-
	equiv(T1,T2).

preds_in_template(T,P):-
	preds_in_lits(T,P1),
	sort(P1,P).

preds_in_lits([],[]).
preds_in_lits([Lit|Lits],[Name/Arity|Ps]):-
	functor(Lit,Name,Arity),
	preds_in_lits(Lits,Ps).

reject(Lits):-
	\+ simple_clause(Lits).
reject(Lits):-
	list2clause(Lits,Clause),
	prune(Clause), !.

redundant_literal(Lit,Lits):-
	reverse(Lits,RLits),
	list2clause(RLits,Clause),
	redundant(Clause,Lit).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mode-directed checking of clauses

cache_mode_args:-
	retractall(cache(input_args(_,_))),
	retractall(cache(output_args(_,_))),
	retractall(cache(const_args(_,_))),
	mode(Mode),
	functor(Mode,Name,Arity),
	functor(Lit,Name,Arity),
	cache_args(Lit),
	fail.
cache_mode_args.

cache_args(Lit):-
	get_input_args(Lit,In),
	get_output_args(Lit,Out),
	get_constant_args(Lit,Const),
	add_cache(input_args(Lit,In)),
	add_cache(output_args(Lit,Out)),
	add_cache(const_args(Lit,Const)).
	

remove_useless_lits(Head,Lits,Lits1):-
	get_output_vars(Head,OVars),
	remove_useless(Lits,OVars,Lits1), !.

remove_useless(Lits,[],Lits):- !.
remove_useless([],_,[]):- !.
remove_useless(Lits,OVars,Lits1):-
	remove_unconnected_lits(Lits,OVars,Lits0),
	(Lits == Lits0 -> Lits1 = Lits;
		remove_useless(Lits0,OVars,Lits1)).

remove_unconnected_lits([],_,[]).
remove_unconnected_lits([Lit|Lits],HOVars,[Lit|Lits1]):-
	connected_lit(Lit,Lits,HOVars), !,
	remove_unconnected_lits(Lits,HOVars,Lits1).
remove_unconnected_lits([_|Lits],HOVars,Lits1):-
	remove_unconnected_lits(Lits,HOVars,Lits1).

connected_lit(Lit,Lits,HOVars):-
	get_output_vars(Lit,OVars),
	(check_intersects(OVars,HOVars) -> true;
			intersects_ivars(OVars,Lits)).

intersects_output_vars(Head,Goals):-
	get_output_vars(Head,OVars),
	goals2list(Goals,Lits),
	intersects_ovars(OVars,Lits).

simple_clause([Head|Lits]):-
	(var_setting(epsilon,Epsilon) -> true; Epsilon = 0),
	sink_literals(Lits,Sinks),
	length(Sinks,N),
	N =< (1 + Epsilon).

almost_simple_clause([Head|Lits]):-
	sink_literals(Lits,Sinks),
	length(Sinks,N),
	N =< 2.

sink_literals([],[]).
sink_literals([Lit|Lits],[Lit|Sinks]):-
	sink_literal(Lit,Lits), !, 
	sink_literals(Lits,Sinks).
sink_literals([_|Lits],Sinks):-
	sink_literals(Lits,Sinks).

sink_literal(Lit,_):-
	get_output_vars(Lit,[]), !.
sink_literal(Lit,Lits):-
	\+ connected_lit(Lit,Lits,[]).



get_output_vars(Lit,Vars):-
	(in_cache(output_args(Lit,Out))->
		true;
		get_output_args(Lit,Out),
		add_cache(output_args(Lit,Out))),
	get_vars(Out,Lit,Vars).

get_input_vars(Lit,Vars):-
	(in_cache(input_args(Lit,In))->
		true;
		get_input_args(Lit,In),
		add_cache(input_args(Lit,In))),
	get_vars(In,Lit,Vars).


get_output_args(Lit,Args):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	get_args(output,Arity,Mode,Args).

get_input_args(Lit,Args):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	get_args(input,Arity,Mode,Args).

get_constant_args(Lit,Args):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	get_args(constant,Arity,Mode,Args).

get_args(_,0,_,[]):- !.
get_args(Type,Arg,Mode,[Arg/T|ArgTypes]):-
	arg_type(Type,Arg/T,Mode), !,
	Arg0 is Arg - 1,
	get_args(Type,Arg0,Mode,ArgTypes).
get_args(Type,Arg,Mode,ArgTypes):-
	Arg0 is Arg - 1,
	get_args(Type,Arg0,Mode,ArgTypes).

arg_type(input,Arg/Type,Mode):-
	arg(Arg,Mode,+Type).
arg_type(output,Arg/Type,Mode):-
	arg(Arg,Mode,-Type).
arg_type(constant,Arg/Type,Mode):-
	arg(Arg,Mode,#Type).

get_vars([],_,[]):- !.
get_vars([Arg/_|Args],Lit,Vars):-
	arg(Arg,Lit,Term),
	vars_in_term([Term],[],V1),
	get_vars(Args,Lit,V2),
	conc(V1,V2,V),
	sort(V,Vars).
	
intersects_ovars(Vars,[L1|_]):-
	get_output_vars(L1,Vars1),
	check_intersects(Vars,Vars1), !.
intersects_ovars(Vars,[_|Lits]):-
	intersects_ovars(Vars,Lits).

intersects_ivars(Vars,[L1|_]):-
	get_input_vars(L1,Vars1),
	check_intersects(Vars,Vars1), !.
intersects_ivars(Vars,[_|Lits]):-
	intersects_ivars(Vars,Lits).

intersects_vars_in_term(Vars,Term):-
	vars_in_term([Term],[],Vars1),
	check_intersects(Vars,Vars1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mode-directed proof 

can_prove(Lit,LitsSoFar):-
	copy_term(Lit,LitCopy),
	get_mode(Lit,Mode,Inputs,_,_),
	check_types(Inputs,LitsSoFar),
	(var_setting(gen_template,true) ->
		call(mode(Mode));
		call(Lit)),
	\+ in(Lit,LitsSoFar),
	copy_outputs(LitCopy,Mode,Outputs),
	update_types(Outputs,LitCopy).

proved(Lit,LitsSoFar):-
	get_mode(Lit,_,Inputs,Outputs,_),
	check_types(Inputs,LitsSoFar),
	check_types(Outputs,LitsSoFar).



get_mode(Lit,Mode,Inputs,Outputs,Constants):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	split_args(Arity,Mode,Lit,Inputs,Outputs,Constants).


copy_outputs(Lit,Mode,Outputs):-
	functor(Mode,Name,Arity),
	copy_outputs(Arity,Mode,Lit,Outputs).

copy_outputs(0,_,_,[]):- !.
copy_outputs(Arg,Mode,Lit,O):-
	arg(Arg,Mode,ModeArg),
	arg(Arg,Lit,LitArg),
	NextArg is Arg - 1,
	split_mode(ModeArg,IO,Type),
	(IO = output ->
		arg(1,Type,LitArg),
		copy_outputs(NextArg,Mode,Lit,O1),
		O = [Type|O1];
		copy_outputs(NextArg,Mode,Lit,O)).

split_args(0,_,_,[],[],[]):- !.
split_args(Arg,Mode,Lit,I,O,C):-
	arg(Arg,Mode,ModeArg),
	arg(Arg,Lit,LitArg),
	NextArg is Arg - 1,
	split_mode(ModeArg,IO,Type),
	arg(1,Type,LitArg),
	(IO = output ->
		split_args(NextArg,Mode,Lit,I,O1,C),
		O = [Type|O1];
		(IO = input ->
			split_args(NextArg,Mode,Lit,I1,O,C),
			I = [Type|I1];
			split_args(NextArg,Mode,Lit,I,O,C1),
			C = [Type|C1])).

check_types([],_).
check_types([Type|ArgTypes],LitsSoFar):-
	type(Type,Lit),
	(var_setting(gen_template,true) ->
		mem(Lit,LitsSoFar);
		mem1(Lit,LitsSoFar)),
	check_types(ArgTypes,LitsSoFar).

update_types([],_).
update_types([ArgType|ArgTypes],Lit):-
	update_argtype(ArgType,Lit),
	update_types(ArgTypes,Lit).

update_argtype(Type,Lit):-
	type(Type,Lit), !.
update_argtype(Type,Lit):-
	asserta(type(Type,Lit)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mode-directed clause extraction from proof

trace_to_clause(Trace,Clause):-
	skolemize_term(Trace,SkTrace),
	match_modes(SkTrace,[],Lits),
	list2clause(Lits,Clause).

match_modes([],_,[]).
match_modes([Lit|Lits],VM,[Lit1|Lits1]):-
	exists_mode(Lit), !,
	select_mode(Lit,Mode),
	match_mode(Lit,VM,Mode,VM1),
	remove_types(Mode,Lit1),
	match_modes(Lits,VM1,Lits1).
match_modes([_|Lits],VM,Lits1):-
	match_modes(Lits,VM,Lits1).

exists_mode(Lit):-
	functor(Lit,Name,Arity),
	functor(ModeLit,Name,Arity),
	determ(_,ModeLit),
	mode(ModeLit).

select_mode(Lit,ModeLit):-
	functor(Lit,Name,Arity),
	functor(ModeLit,Name,Arity),
	mode(ModeLit).

match_mode(Lit,VM,Mode,VM1):-
	Lit =.. [Name|Args],
	Mode =.. [Name|ModeArgs],
	match_args(ModeArgs,Args,VM,VM1).


match_args([],[],V,V).
match_args([ModeArg|ModeArgs],[Arg|Args],VM0,VM):-
	match_arg(ModeArg,Arg,VM0,VM1),
	match_args(ModeArgs,Args,VM1,VM).

match_arg(ModeArg,Arg,VM0,VM1):-
	var(ModeArg), !,
	lookup_varmap(Arg,ModeArg/Arg,VM0,VM1).
match_arg(ModeArg,Arg,VM0,VM1):-
	split_mode(ModeArg,IO,Type),
	(IO = none -> TypeTerm = Type;
		arg(1,Type,TypeTerm)),
	\+ mismatch(TypeTerm,Arg),
	(IO = constant -> TypeTerm = Arg, VM1 = VM0;
		(var(TypeTerm) ->
			lookup_varmap(Arg,TypeTerm/Arg,VM0,VM1);
			match_mode(Arg,VM0,TypeTerm,VM1))).

mismatch(Type,Arg):-
	Type = Arg, !,
	fail.
mismatch(_,_).


remove_types(Lit,UntypedLit):-
	Lit =.. [Name|ModeArgs],
	remove_modetypes(ModeArgs,Args),
	UntypedLit =.. [Name|Args].

remove_modetypes([],[]).
remove_modetypes([ModeArg|ModeArgs],[Arg|Args]):-
	split_mode(ModeArg,_,TypedArg),
	arg(1,TypedArg,Arg),
	remove_modetypes(ModeArgs,Args).


lookup_varmap(T,V/T,VM,VM):-
	mem(V/T1,VM),
	T == T1, !.
lookup_varmap(T,V/T,VM,[V/T|VM]).


split_mode(Var,none,Var):- var(Var), !.
split_mode(+Type,input,TypeCall):-
	(ground(Type) -> functor(TypeCall,Type,1); TypeCall = Type), !.
split_mode(-Type,output,TypeCall):- 
	(ground(Type) -> functor(TypeCall,Type,1); TypeCall = Type), !.
split_mode(#Type,constant,TypeCall):- 
	(ground(Type) -> functor(TypeCall,Type,1); TypeCall = Type), !.
split_mode(Type,none,Type).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% general utilities

% generate a new feature number
% provided it is less than the maximum number of features allowed
gen_featurenum(Feature1):-
	var_setting(feature_count,Feature0),
        Feature1 is Feature0 + 1,
	set_var(feature_count,Feature1).
gen_featurenum(Feature1):-
        var_setting(feature_offset,Offset),
        Feature1 is Offset + 1,
	set_var(feature_count,Feature1).

split_clause((Head:-true),Head,true):- !.
split_clause((Head:-Body1),Head,Body2):- !, Body1 = Body2.
split_clause([Head|T],Head,T):- !.
split_clause([Head],Head,[true]):- !.
split_clause(Head,Head,true).

copy_iargs(0,_,_,_):- !.
copy_iargs(Arg,Old,New,Arg):-
        !,
        Arg1 is Arg - 1,
        copy_iargs(Arg1,Old,New,Arg).
copy_iargs(Arg,Old,New,Out):-
        arg(Arg,Old,Val),
        arg(Arg,New,Val),
        Arg1 is Arg - 1,
        copy_iargs(Arg1,Old,New,Out).

in_cache(clause(Status,(Head:-Body))):-
	!,
	goals2list((Head,Body),L),
	(var_setting(reduce_clause,true) -> rsubset_var(L,L0); L0 = L),
	cache(clause(Status,L1)),
	equiv(L0,L1).
in_cache(template(Head,Clause)):-
	var_setting(gen_template,true), !,
	cache(template(_,Clause1)),
	equiv_template(Clause1,Clause),
	% more_general_template(Clause1,Clause),
	debug_write(Clause1), debug_write(nl),
	debug_write('equiv: '), debug_write(Clause),
	debug_write(nl), debug_write(nl).
in_cache(Entry):-
	% \+ var_setting(gen_template,true),
	cache(Entry).

update_cache(Entry):-
	\+ in_cache(Entry), !,
	update_cache_entry(Entry).

add_cache(Entry):-
	update_cache(Entry).

update_cache_entry(clause(Status,(Head:-Body))):-
	!,
	goals2list((Head,Body),L),
	(var_setting(reduce_clause,true) -> rsubset_var(L,L0); L0 = L),
	asserta(cache(clause(Status,L0))).
update_cache_entry(template(Head,Clause)):-
	var_setting(gen_template,true),
	cache(template(_,Clause1)),
	equiv(Clause,Clause1),
	% more_general_template(Clause,Clause1),
	retract(cache(template(_,Clause1))),
	debug_write('removing: '), debug_write(Clause1), debug_write(nl),
	debug_write('equivalent to: '), debug_write(Clause), debug_write(nl), debug_write(nl),
	fail.
update_cache_entry(Entry):-
	asserta(cache(Entry)).

rm_cache(Entry):-
	retractall(cache(Entry)).

% vars_in_term([],Vars,Vars1):- sort(Vars,Vars1), !.
% vars_in_term([Var|T],VarsSoFar,Vars):-
        % var(Var), !,
        % vars_in_term(T,[Var|VarsSoFar],Vars).
% vars_in_term([Term|T],VarsSoFar,Vars):-
        % Term =.. [_|Terms], !,
        % vars_in_term(Terms,VarsSoFar,V1),
        % vars_in_term(T,V1,Vars).
% vars_in_term([_|T],VarsSoFar,Vars):-
        % vars_in_term(T,VarsSoFar,Vars).



name_code(X,Code):-
	atomic(X),
	name(X,[Code]).

%Does not return multiple solutions
mem1(X,[X|_]):-!.
mem1(X,[_|T]):-mem1(X,T).

%returns multiple solutions
mem(X,[X|_]).
mem(X,[_|T]):-mem(X,T).

% like member1, but works for variables
in(L,[L1|_]):-
	L == L1, !.
in(L,[_|T]):-
	in(L,T).

subset_var([],_).
subset_var([X|Y],S):-
	mem1(X,S),
	subset_var(Y,S).

check_intersects([E1|_],Set):-
	in(E1,Set), !.
check_intersects([_|Set0],Set):-
	check_intersects(Set0,Set).

rsubset_var([],[]).
rsubset_var([H|T],T1):-
	in(H,T), !,
	rsubset_var(T,T1).
rsubset_var([H|T],[H|T1]):-
	rsubset_var(T,T1).


vars_in_term([],Vars,Vars1):- sort(Vars,Vars1), !.
vars_in_term([Var|T],VarsSoFar,Vars):-
        var(Var), !,
        vars_in_term(T,[Var|VarsSoFar],Vars).
vars_in_term([Term|T],VarsSoFar,Vars):-
        Term =.. [_|Terms], !,
        vars_in_term(Terms,VarsSoFar,V1),
        vars_in_term(T,V1,Vars).
vars_in_term([_|T],VarsSoFar,Vars):-
        vars_in_term(T,VarsSoFar,Vars).


reverse(L1, L2) :- revz(L1, [], L2).

revz([X|L], L2, L3) :- revz(L, [X|L2], L3).
revz([], L, L).

abs2(X,Y) :- X<0,Y is -X.
abs2(X,X) :- X>=0, X is X, !.

conc([],L,L).
conc([H|T],L,[H|T1]):-
	conc(T,L,T1).


del(X,[X|L],L).
del(X,[H|T],[H|T1]):-
	del(X,T,T1), !.
del(X,L,L).

distinct(S):-
	length(S,N),
	sort(S,S1),
	length(S1,N1),
	N = N1.


skolemize_term(Term,T):-
	copy_term(Term,T),
	numbervars(T,0,_).

list2clause([Head|List],Clause):-
	list2goals(List,Body),
	Clause = (Head:- Body).

list2goals([L],L):- !.
list2goals([L1|Ls],(L1,Rest)):-
	list2goals(Ls,Rest).


goals2list((G1,Gs),[G1|Rest]):-
	!,
	goals2list(Gs,Rest).
goals2list(G,[G]).


mywrite(Text):-
	var_setting(verbose,true), !,
	writeq(Text), nl.
mywrite(_).

write_clause(Clause):-
	copy_term(Clause,(Head:-Body)),
	numbervars((Head:-Body),0,_),
	writeq(Head), write(':- '), nl,
	write_body(Body).

write_wclause((W::Clause)):-
	copy_term(Clause,(Head:-Body)),
	numbervars((Head:-Body),0,_),
	write(W), write('::'), 
	writeq(Head), write(':- '), nl,
	write_body(Body).

write_body((L1,Lits)):-
	!,
	tab(4), writeq(L1), write(','), nl,
	write_body(Lits).
write_body(L):-
	tab(4), writeq(L), write('.'), nl, nl.


set_var(Variable,Value):-
	set_var(Variable,Value,true).

set_var(Variable,Value,Cleanup):-
	((Cleanup = true) -> retractall(var_setting(Variable,_)); true),
	asserta(var_setting(Variable,Value)).
noset_var(Variable):-
	retractall(var_setting(Variable,_)).


modeb(Recall,Mode):-
	assertz(mode(Mode)).
modeh(Recall,Mode):-
	assertz(mode(Mode)).
mode(Recall,Mode):-
	assertz(mode(Mode)).

determination(P1/A1,P2/A2):-
	!,
	functor(D1,P1,A1),
	functor(D2,P2,A2),
	assertz(determ(D1,D2)).

example(_,_,E):-
	determ(E,_), !.

set(Var,Value):-
	set_var(Var,Value).
	
seen_proof(P):-
	proof(_,_,_,P1),
	equiv(P,P1).


show_templates:-
	cache(template(_,L)),
	list2goals(L,(H,B)),
	Clause = (H:-B),
	write('Template Clause:'), nl,
	write_clause(Clause),
	fail.
show_templates.

show_features:-
	listing('$aleph_feature'/5),
	listing('$aleph_feature_weight'/2),
	listing('$aleph_feature_count'/1).
debug_write(Term):-
	var_setting(debug,true), !,
	(Term = nl -> nl;
		copy_term(Term,Term1),
		numbervars(Term1,0,_),
		write(Term1)).
debug_write(_).

clean_up:-
	retractall(cache(_)),
	retractall(type(_,_)).

clean_up_templates:-
	retractall(cache(template(_,_))),
	retractall(type(_,_)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% read in background knowledge containing modes and determs

:- [back].
