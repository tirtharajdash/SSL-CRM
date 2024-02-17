:- [aleph].
:- [subtle].
%:- [target_theory].

:- dynamic cache/1.
:- dynamic aln_cache/2.
:- dynamic type/2.
:- dynamic var_setting/2.

:- dynamic aln/2.
:- dynamic func/2.
:- dynamic target/2.
:- dynamic crm_connected/3.

:- dynamic subsume_equiv/3.

:- multifile prune/1.
:- multifile target/2.

:- discontiguous aln/2.
:- discontiguous func/2.
:- discontiguous crm_connected/3.

crm(MaxComp,MaxConc):-
	repeat,
	crm_init,
	set_var(max_comp,MaxComp),
	set_var(max_conc,MaxConc),
	once(initiate_aln),
	once(sample_alns(MaxComp)),
	get_target_equivs,
	(var_setting(check_target,true) ->
		\+ subsume_equiv(_,_,[]);
		true),  !,
	write_all.

crm(MaxComp):-
	repeat,
	crm_init,
	set_var(max_comp,MaxComp),
	once(initiate_aln),
	once(sample_alns(MaxComp)),
	get_target_equivs,
	(var_setting(check_target,true) ->
		\+ subsume_equiv(_,_,[]);
		true),  !,
	write_all.

sample_alns(MaxComp):-
	interval_to_list(2-MaxComp,Comps),	% in aleph.pl
	var_setting(samplesize,N),
	mem(Comp,Comps),
	once(sample_aln(Comp,N)),
	fail.
sample_alns(_).

sample_aln(Comp,N):-
	var_setting(trials,T),
	set_var(sampled,0),
	repeat,
	(sample_aln(Comp,T,Aln) ->
		once(var_setting(sampled,S)),
		S1 is S + 1,
		set_var(sampled,S1),
		S1 > N;
		true), !,
	Comp1 is Comp-1,
	var_setting(counter(a,Comp1),_-N1),
	var_setting(counter(a),N2),
	F2 is N1 + 1,
	set_var(counter(a,Comp),F2-N2).

sample_aln(Comp,T,Aln):-
	T > 0,
	operator_name(Comp,Op),	% prob grammar
	operator_args(Comp,Op,Args),	% prob grammar
	apply(Comp,Op,Args,Aln).
sample_aln(Comp,T,Aln):-
	T > 1, !,
	T0 is T - 1,
	sample_aln(Comp,T0,Aln).
% sample_aln(_,_,null).

get_target_equivs:-
	target(Id,Target),
	clause_to_list(Target,TargetL),	% in aleph.pl
	findall(Func,subsume_equiv(TargetL,Func),FL),
	assertz(subsume_equiv(Id,Target,FL)),
	fail.
get_target_equivs.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% composition by application of operators

% unary operator
apply(Comp,Op,[N1],a(N)):-
	aln(a(N1),Aln1),
	Aln1 = [_,_,f=f(F1),g=G],
	L is Comp,
	% depth_ok(L),
	Composition =.. [Op,f(F1)],
	Aln = [depth=L,comp=Composition,f=f(F),g=G],
	func(f(F1),Def1),
	Def1 = [type=_,def=FDef1],
	compose(Op,FDef1,FDef),
	func_ok(FDef),
	Def = [type=complex,def=FDef],
	assign_def(f(F),Def),
	assign_def(a(N),Aln),
	assign_def(crm_connected(a(N)),[[a(N1)],[1]]).

% binary operator
apply(Comp,Op,[N1,N2],a(N)):-
	aln(a(N1),Aln1),
	aln(a(N2),Aln2),
	Aln1 = [_,_,f=f(F1),g=G],
	Aln2 = [_,_,f=f(F2),g=G],
	L is Comp,
	% depth_ok(L),
	Composition =.. [Op,f(F1),f(F2)],
	Aln = [depth=L,comp=Composition,f=f(F),g=G],
	func(f(F1),Def1),
	Def1 = [type=_,def=FDef1],
	func(f(F2),Def2),
	Def2 = [type=_,def=FDef2],
	compose(Op,FDef1,FDef2,FDef),
	func_ok(FDef),
	Def = [type=complex,def=FDef],
	assign_def(f(F),Def),
	assign_def(a(N),Aln),
	assign_def(crm_connected(a(N)),[[a(N1),a(N2)],[1,1]]).
	

compose(eq,(Head:-Body),(Head:-Body1)):-
	constrain_vars(eq,(Head:-Body),Eq),
	conc_lits(Body,Eq,Body1).
compose(neq,(Head:-Body),(Head:-Body1)):-
	constrain_vars(neq,(Head:-Body),NEq),
	conc_lits(Body,NEq,Body1).
compose(conc,(Head:-Body1),(Head:-Body2),(Head:-Body)):-
	\+ (Body1 == Body2),
	conc_lits(Body1,Body2,Body).


depth_ok(L):-
	var_setting(max_comp,Max),
	L =< Max.

constrain_vars(eq,(Head:-Body),(V1=V2)):-
	get_input_vars(Head,UV),
	get_compatible_vars(eq,UV,V1,V2),
	\+ redundant((Head:-Body),(V1=V2)).
constrain_vars(eq,(Head:-Body),(V1=V2)):-
	exists_vars(Body,EV),
	get_compatible_vars(eq,EV,V1,V2),
	\+ redundant((Head:-Body),(V1=V2)).
constrain_vars(eq,(Head:-Body),(V1\=V2)):-
	get_input_vars(Head,UV),
	get_compatible_vars(eq,UV,V1,V2),
	\+ redundant((Head:-Body),(V1\=V2)).
constrain_vars(neq,(Head:-Body),(V1\=V2)):-
	exists_vars(Body,EV),
	get_compatible_vars(EV,V1,V2),
	\+ redundant((Head:-Body),(V1\=V2)).

get_compatible_vars(Rel,Vars,V1,V2):-
	del(Type1-V1,Vars,Rest),
	mem(Type2-V2,Rest),
	exists_mode(Rel,Type1,Type2),
	V1 @< V2.

exists_mode(eq,Type1,Type2):-
	mode((+Type1 = +Type2)), !.
exists_mode(eq,Type1,Type2):-
	mode((+Type2 = +Type1)).
exists_mode(neq,Type1,Type2):-
	mode((+Type1 \= +Type2)), !.
exists_mode(neq,Type1,Type2):-
	mode((+Type2 \= +Type1)).

redundant((_:- Body),(V1=V2)):-
	goals2list(Body,L),
	exists_equality(V1,V2,L).
redundant((_:- Body),(V1\=V2)):-
	goals2list(Body,L),
	exists_inequality(V1,V2,L).
	

exists_equality(V1,V2,L):-
	mem((X=Y),L),
	((X==V1, Y==V2); (X==V2, Y==V1)), !.

exists_inequality(V1,V2,L):-
	mem((X\=Y),L),
	((X==V1, Y==V2); (X==V2, Y==V1)), !.
	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% aln-specific utilities

aln(A,Aln):-
	A = a(_),
	var_setting(A,Aln).
	
func(F,Def):-
	F = f(_),
	var_setting(F,Def).
func(true,Def):-
	var_setting(true,Def).
func(false,Def):-
	var_setting(true,Def).

func(G,Def):-
	G = g(_),
	var_setting(G,Def).

crm_connected(A,As,Ws):-
	A = a(_),
	var_setting(crm_connected(A),[As,Ws]).

assign_def(X,Def):-
	ground(X),
	var_setting(X,_), !,
	set_var(X,Def).
assign_def(crm_connected(A),Def):-
	!,
	set_var(crm_connected(A),Def).
assign_def(a(A),Def):-
	!,
	aln_name(a(A)),
	set_var(a(A),Def).
	% debug_write('Defined Aln: '), debug_write(a(A)), debug_write(nl).
assign_def(Fn,Def):-
	fn_name(Fn),
	set_var(Fn,Def).
	% debug_write('Defined Func: '), debug_write(Fn), debug_write(nl).

aln_name(a(N)):-
	var_setting(counter(a),N0), !,
	N is N0 + 1,
	set_var(counter(a),N).
	% (var(N) ->
		% N is N0 + 1,
		% set_var(counter(a),N);
		% (N =< N0 -> true; set_var(counter(a),N))).
aln_name(a(1)):-
	set_var(counter(a),1).
% aln_name(a(N)):-
	% (var(N) -> N = 1; true),
	% set_var(counter(a),N).

fn_name(f(N)):-
	var_setting(counter(f),N0), !,
	N is N0 + 1,
	set_var(counter(f),N).
fn_name(f(1)):-
	set_var(counter(f),1).

fn_name(g(N)):-
	var_setting(counter(g),N0), !,
	N is N0 + 1,
	set_var(counter(g),N).
fn_name(g(1)):-
	set_var(counter(g),1).

write_all:-
	nl, nl,
	write_params,
	nl, nl,
	write_aln,
	nl,
	write_connected,
	nl,
	write_func,
	nl, nl,
	write_counter,
	nl, nl,
	write_target_equivs.

write_params:-
	var_setting(debug,Debug),
	var_setting(min_precision,Prec),	
	var_setting(min_support,Supp),	
	var_setting(epsilon_simple,Eps),
	var_setting(simple_lits,L),
	var_setting(max_comp,Depth),
	var_setting(max_conc,Conc),
	var_setting(select_aln,Select),	
	var_setting(samplesize,N),
	var_setting(trials,T),	
	var_setting(check_redun,R),
	var_setting(check_target,Target),
	var_setting(featurefile,File),
	Params = [
			debug=Debug,
			min_precision=Prec,
			min_support= Supp,
			epsilon_simple=Eps,
			simple_lits=L,
			max_comp=Depth,
			max_conc=Conc,
			select_aln=Select,
			samplesize=N,
			trials=T,
			check_redun=R,
			check_target=Target,
			featurefile=File
		],
	write_comments(['Parameters:'|Params]).

write_aln:-
	aln(A,Aln),
	write(aln(A,Aln)), write('.'), nl,
	fail.
write_aln.

write_connected:-
	crm_connected(A,As,Ws),
	write(connected(A,As,Ws)), write('.'), nl,
	fail.
write_connected.

write_func:-
	func(F,Def),
	numbervars(Def,0,_),
	write(func(F,Def)), write('.'), nl,
	fail.
write_func.


write_counter:-
	var_setting(counter(X),N),
	write(count(X,N)), write('.'), nl, 
	fail.
write_counter.


write_target_equivs:-
	subsume_equiv(Id,Target,FL),
	numbervars(Target,0,_),
	write(subsume_equiv(Id,Target,FL)), write('.'), nl,
	fail.
write_target_equivs.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% domain-specific  simple features

initiate_aln:-
	once(gen_simple_features),
	'$aleph_feature'(F,_,_,Head,Body),
	FDef = [type=simple,def=(Head:-Body)],
	func(g(0),GDef),
	assign_def(f(F),FDef),
	% assign_def(g(F),GDef),
	ADef = [depth=1,comp=none,f=f(F),g=g(0)],
	assign_def(a(F),ADef),
	assign_def(crm_connected(a(F)),[[a(0),a(0)],[1,0]]),
	fail.
initiate_aln:-
	var_setting(counter(a),N),
	set_var(counter(a,1),1-N).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generation of simple features from the mode declatations

% simple depth-bounded theorem-prover for a Goal

prove(Depth,_,N-_,_):-
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
% generate simple features from modes
%	use examples for checking on support/precision constraints

gen_simple_features:-
	var_setting(featurefile,FeatureFile), !,
	clean_up_features,
	consult(FeatureFile).

gen_simple_features:-
	clean_up_features,
	var_setting(simple_lits,NLits),
	var_setting(epsilon_simple,Epsilon),
	var_setting(min_precision,Precision),
	var_setting(min_support,Support),
	gen_simple_features(NLits,Epsilon,Precision,Support).

gen_simple_features(Depth,Epsilon,Prec,Support):-
	set_var(min_precision,Prec),
	set_var(min_support,Support),
	% meta_prove(pos,1,Depth,Epsilon),
	meta_prove(Depth,Epsilon),
	instantiate_templates.


% construction of templates
%	for simple clauses by meta-interpretion of modes

% meta_prove(Type,Id,Depth,Epsilon):-
meta_prove(Depth,Epsilon):-
	cache_mode_args,
	set_var(epsilon,Epsilon),
	get_template_example(Example),
	get_templates(Depth,Example).

% get_template_example(Example):-
	% example(pos,1,Example),

get_template_example(Example):-
	once(determ(Example,_)),
	numbervars(Example,0,_).

% instantiate #'ed args using type-definitions in backgroung

instantiate_templates:-
	select_template([Head|Body]),
	ground_lits(Body),
	list_to_clause([Head|Body],Clause),
	label_ok(Clause),
	% update_cache(instantiate_template(Head,[Head|Body])),
	debug_write('Instantiated Template: '), debug_write([Head|Body]), debug_write(nl),
	fail.
instantiate_templates.

func_ok(Func):-
	\+ redun(Func),
	label_ok(Func).

label_ok(Clause):-
	once(label_create(Clause,ExtendedLabel)),
	assemble_label(ExtendedLabel,Label),
	(var_setting(min_precision,MinPrec) -> true; MinPrec = 0),
	(var_setting(min_support,MinSupp) -> true; MinSupp = 0),
	label_cover(pos,Label,PC),
	label_cover(neg,Label,NC),
	Support is max(PC,NC),
	Support > 0,
	Support >= MinSupp,
	Precision is Support/(PC+NC),
	Precision >= MinPrec,
	gen_feature(Clause,Label).
	


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

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% mode-directed construction of clause templates


get_templates(Depth,Example):-
	crm_clean_up_templates,
	functor(Example,Name,Arity),
	functor(Head,Name,Arity),
	set_var(gen_template,true),
	get_template(Depth,Head,Template),
	\+ reject(Template),
	once(update_templates(Head,Template)),
	% update_cache(template(Head,Template)),
	fail.
get_templates(_,_):-
	noset_var(gen_template).

get_template(Depth,Head,[Head|Template]):-
	get_mode(Head,_,Inputs,_,_),
	update_types(Inputs,Head),
	prove(Depth,Head,0-[Head],Template).

update_templates(Head,[Head|Body]):-
	\+ contains_useless_lit(Head,Body), 
	debug_write('Template: '), debug_write([Head|Body]), debug_write(nl),
	update_cache(template(Head,[Head|Body])).

contains_useless_lit(Head,Body):-
	remove_useless_lits(Head,Body,Body1),
	Body \= Body1, !.


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
% mode-based utilities

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
	remove_uncrm_connected_lits(Lits,OVars,Lits0),
	(Lits == Lits0 -> Lits1 = Lits;
		remove_useless(Lits0,OVars,Lits1)).

remove_uncrm_connected_lits([],_,[]).
remove_uncrm_connected_lits([Lit|Lits],HOVars,[Lit|Lits1]):-
	crm_connected_lit(Lit,Lits,HOVars), !,
	remove_uncrm_connected_lits(Lits,HOVars,Lits1).
remove_uncrm_connected_lits([_|Lits],HOVars,Lits1):-
	remove_uncrm_connected_lits(Lits,HOVars,Lits1).

crm_connected_lit(Lit,Lits,HOVars):-
	get_output_vars(Lit,OVars),
	(check_intersects(OVars,HOVars) -> true;
			intersects_ivars(OVars,Lits)).

intersects_output_vars(Head,Goals):-
	get_output_vars(Head,OVars),
	goals2list(Goals,Lits),
	intersects_ovars(OVars,Lits).

check_simple((Head:-Body)):-
	goals2list(Body,BodyL),
	simple_clause([Head|BodyL]).

simple_clause([_|Lits]):-
	(var_setting(epsilon,Epsilon) -> true; Epsilon = 0),
	sink_literals(Lits,Sinks),
	length(Sinks,N),
	N =< (1 + Epsilon).


almost_simple_clause([_|Lits]):-
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
	\+ crm_connected_lit(Lit,Lits,[]).



get_output_vars(Lit,Vars):-
	(in_cache(output_args(Lit,Out))->
		true;
		get_output_args(Lit,Out),
		add_cache(output_args(Lit,Out))),
	get_argvars(Lit,Out,Vars).

get_typed_output_vars(Lit,Vars):-
	(in_cache(output_args(Lit,Out))->
		true;
		get_output_args(Lit,Out),
		add_cache(output_args(Lit,Out))),
	get_typed_argvars(Lit,Out,Vars).

get_input_vars(Lit,Vars):-
	(in_cache(input_args(Lit,In))->
		true;
		get_input_args(Lit,In),
		add_cache(input_args(Lit,In))),
	get_typed_argvars(Lit,In,Vars).


get_output_args(Lit,Args):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	get_type_args(output,Arity,Mode,Args).

get_input_args(Lit,Args):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	get_type_args(input,Arity,Mode,Args).

get_constant_args(Lit,Args):-
	functor(Lit,Name,Arity),
	functor(Mode,Name,Arity),
	mode(Mode),
	get_type_args(constant,Arity,Mode,Args).

get_type_args(_,0,_,[]):- !.
get_type_args(Type,Arg,Mode,[Arg/T|ArgTypes]):-
	arg_type(Type,Arg/T,Mode), !,
	Arg0 is Arg - 1,
	get_type_args(Type,Arg0,Mode,ArgTypes).
get_type_args(Type,Arg,Mode,ArgTypes):-
	Arg0 is Arg - 1,
	get_type_args(Type,Arg0,Mode,ArgTypes).

arg_type(input,Arg/Type,Mode):-
	arg(Arg,Mode,+Type).
arg_type(output,Arg/Type,Mode):-
	arg(Arg,Mode,-Type).
arg_type(constant,Arg/Type,Mode):-
	arg(Arg,Mode,#Type).

get_argvars(_,[],[]):- !.
get_argvars(Lit,[Arg/_|Args],Vars):-
	arg(Arg,Lit,Term),
	vars_in_term([Term],[],V1),
	get_argvars(Lit,Args,V2),
	conc(V1,V2,V),
	sort(V,Vars).

get_typed_argvars(_,[],[]):- !.
get_typed_argvars(Lit,[Arg/Type|Args],Vars):-
	arg(Arg,Lit,Term),
	vars_in_term([Term],[],V1),
	add_types(V1,Type,TV1),
	get_typed_argvars(Lit,Args,TV2),
	conc(TV1,TV2,TV),
	sort(TV,Vars).

add_types([],_,[]).
add_types([Var|Vars],Type,[Type-Var|TV]):-
	add_types(Vars,Type,TV).
	
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


mode(Mode):-
	'$aleph_global'(mode,mode(_,Mode)).


determ(A,B):-
	'$aleph_global'(determination,determination(P1/A1,P2/A2)),
	functor(A,P1,A1),
	functor(B,P2,A2).

exists_vars(Body,EVars):-
	get_output_vars(Body,[],OVars),
	sort(OVars,EVars).


get_output_vars((Lit,Lits),OVarsSoFar,OVars):-
	!,
	get_typed_output_vars(Lit,Vars),
	conc(Vars,OVarsSoFar,OVarsSoFar1),
	get_output_vars(Lits,OVarsSoFar1,OVars).
get_output_vars(Lit,OVarsSoFar,OVars):-
	get_typed_output_vars(Lit,Vars),
	conc(Vars,OVarsSoFar,OVars).

copy_outputs(Lit,Mode,Outputs):-
	functor(Mode,_,Arity),
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

in_cache(clause(Status,(Head:-Body))):-
	!,
	goals2list((Head,Body),L),
	(var_setting(reduce_clause,true) -> rsubset_var(L,L0); L0 = L),
	cache(clause(Status,L1)),
	equiv(L0,L1).
in_cache(template(_,Clause)):-
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
update_cache_entry(template(_,Clause)):-
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

seen_proof(P):-
	proof(_,_,_,P1),
	equiv(P,P1).

subsume_equiv(ClauseL,Func):-
	func(Func,Def),
	Def = [_,def=FDef],
	clause_to_list(FDef,FDefL),	% in aleph.pl
	enforce_eqs(FDefL,RFDefL),
	equiv(ClauseL,RFDefL).


execute_eq([],[]).
execute_eq([(A=B)|T],T1):-
	!,
	A=B,
	execute_eq(T,T1).
execute_eq([H|T],[H|T1]):-
	execute_eq(T,T1).

show_templates:-
	cache(template(_,L)),
	list2goals(L,(H,B)),
	Clause = (H:-B),
	write('Template Clause:'), nl,
	write_clause(Clause),
	fail.
show_templates.

debug_write(Term):-
	var_setting(debug,true), !,
	(Term = nl -> nl;
		copy_term(Term,Term1),
		numbervars(Term1,0,_),
		write(Term1)).
debug_write(_).

write_comments([]).
write_comments([T|Rest]):-
	write('% '), write(T), nl,
	write_comments(Rest).

crm_clean_up:-
	crm_clean_up_cache,
	crm_clean_up_templates,
	clean_up_features,	% in aleph.pl
	retractall(subsume_equiv(_,_,_)),
	retractall(var_setting(_,_)).

crm_clean_up_cache:-
	retractall(cache(_)),
	retractall(aln_cache(_,_)),
	retractall(type(_,_)).

crm_clean_up_templates:-
	retractall(cache(template(_,_))),
	retractall(type(_,_)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% general utilities

mem(X,[X|_]).
mem(X,[_|T]):- mem(X,T).

mem1(X,[X|_]):-!.
mem1(X,[_|T]):-mem1(X,T).

% like member1, but works for variables
in(L,[L1|_]):-
	L == L1, !.
in(L,[_|T]):-
	in(L,T).

update_set(E,[],[E]).
update_set(E,[E1|S],S):-
	E == E1, !.
update_set(E,[_|S],S1):-
	update_set(E,S,S1).

reverse(L1, L2) :- revz(L1, [], L2).

revz([X|L], L2, L3) :- revz(L, [X|L2], L3).
revz([], L, L).


conc([],L,L).
conc([H|T],L,[H|T1]):-
	conc(T,L,T1).


del(X,[X|L],L).
del(X,[H|T],[H|T1]):-
	del(X,T,T1).
% del(_,L,L).

		
conc_lits((L1,L2),L,(L1,L3)):-
	!,
	conc_lits(L2,L,L3).
conc_lits(L1,L2,(L1,L2)).

list_max(L,X):-
	prolog_type(swi), !,
	max_list(L,X).

list_max([X|Y],Z):-
	list_max(Y,X,Z).

list_max([],X,X).
list_max([Y|T],X,Z):-
	X >= Y, !,
	list_max(T,X,Z).
list_max([Y|T],_,Z):-
	list_max(T,Y,Z).

get_random(First,Last,INum):-
        aleph_random(X),
        INum1 is integer(X*(Last-First+1) + 0.5),
        (INum1 = 0 ->
                INum = First;
                (INum1 > Last ->
                        INum = Last;
                        INum is First + INum1
                )
        ).


set_var(Variable,Valne):-
	set_var(Variable,Valne,true).

set_var(Variable,Valne,Cleanup):-
	((Cleanup = true) -> retractall(var_setting(Variable,_)); true),
	asserta(var_setting(Variable,Valne)).
noset_var(Variable):-
	retractall(var_setting(Variable,_)).




equality((_=_)).

redun((Head:-Body)):-
	var_setting(check_redun,true), !,
	goals2list((Head,Body),L),
	enforce_eqs(L,L1),
	numbervars(L1,0,_),
	sort(L1,L2),
	rm_identical(L2,[],L3),
	length(L3,N),
	(aln_cache(N,L3)-> true;
		asserta(aln_cache(N,L3)),
		!, fail).

enforce_eqs([],[]).
enforce_eqs([X=Y|Rest],T):-
	!,
	X=Y,
	enforce_eqs(Rest,T).
enforce_eqs([L1|Rest],[L1|T]):-
	enforce_eqs(Rest,T).

rm_identical([],_,[]).
rm_identical([Lit|Lits],LitsSoFar,RedLits):-
	in(Lit,LitsSoFar), !,
	rm_identical(Lits,LitsSoFar,RedLits).
rm_identical([Lit|Lits],LitsSoFar,[Lit|RedLits]):-
	rm_identical(Lits,[Lit|LitsSoFar],RedLits).

name_code(X,Code):-
	atomic(X),
	name(X,[Code]).

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



abs2(X,Y) :- X<0,Y is -X.
abs2(X,X) :- X>=0, X is X, !.

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

write_body((L1,Lits)):-
	!,
	tab(4), writeq(L1), write(','), nl,
	write_body(Lits).
write_body(L):-
	tab(4), writeq(L), write('.'), nl, nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
crm_init:-
	crm_clean_up,
	set_var(debug,true),  		% for printing optimised clauses
	set_var(min_precision,0.5),	% min precision for feature-clauses
	set_var(min_support,10),	% min support for feature-clauses
	set_var(epsilon_simple,0),	% epsilon tolerance on sinks
	set_var(simple_lits,2),		% max body literals for simple clauses
	set_var(max_comp,10),		% max length of derivation sequences
	set_var(max_conc,10),		% max depth for conc operator
	set_var(select_aln,random),	% random sampling of alns
	set_var(samplesize,5000),	% max alns to be sampled in a layer: for czech data
	set_var(trials,100),		% max trials per sample: for czech data
	set_var(check_redun,true),	% check for redundant alns
	set_var(check_target,true),	% check for target clauses
	set_var(featurefile,'features.pl'),	% get simple features from file
	set_var(a(0),[depth=0,comp=none,f=true,g=g(0)]), % 1 domain-independent special aln
	set_var(true,[type=special,def=[_,true]]), % special function: always 1
	set_var(false,[type=special,def=[_,fail]]),% special function: always 0
	set_var(g(0),[type=relu,def=reludef]).	% activation function

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Stochastic Definite Clause Grammar for
%	operators and their arguments
%	distributions are depth-linked

operator_name(Depth,Op):-
	var_setting(select_aln,random), !,
	draw_op_name(Depth,Op).
operator_name(_,Op):-
	mem(Op,[eq,conc]).

draw_op_name(Depth,conc):-
	var_setting(max_conc,Conc), 
	Depth =< Conc, !.
	% P = [0-eq,0-neq,1-conc],	% not normalised
	% draw_element(P,Op).		% in aleph.pl
draw_op_name(Depth,eq):-
	var_setting(max_conc,Conc),
	Depth > Conc.
	% P = [1-eq,0-neq,0-conc],	
	% draw_element(P,Op).

% operator_name(_,Op):-
	% P = [1-eq,1-conc],	
	% draw_element(P,Op).
% 
% operator_args(_,Op,[N1]):-
	% Op = eq,
 	% var_setting(counter(a),Last),
	% get_random(Last,N1).		% in aleph.pl
% operator_args(Depth,Op,[N1,N2]):-
	% Op = conc,
 	% var_setting(counter(a,1),1-S),	% simple clauses
 	% PrevDepth is Depth - 1,
 	% var_setting(counter(a,PrevDepth),A-B),	% clauses in prev layer
 	% get_random(1,S,N1),
	% get_random(A,B,N2).

operator_args(Depth,Op,[N1]):-
	Op = eq,		% unary op
	PrevDepth is Depth - 1,
	(var_setting(select_aln,random) ->
		var_setting(counter(a,PrevDepth),A-B),	% clauses in prev layer
		get_random(A,B,N1);
		var_setting(counter(a),Last),
		interval_to_list(1-Last,L),
		mem(N1,L)).
operator_args(Depth,Op,[N1]):-
	Op = neq,		% unary op
	PrevDepth is Depth - 1,
	(var_setting(select_aln,random) ->
		var_setting(counter(a,PrevDepth),A-B),	% clauses in prev layer
		get_random(A,B,N1);
		var_setting(counter(a),Last),
		interval_to_list(1-Last,L),
		mem(N1,L)).
operator_args(Depth,Op,Args):-
	Op = conc,		% binary op
	PrevDepth is Depth - 1,
	var_setting(counter(a,1),1-S),	% simple clauses
	var_setting(counter(a,PrevDepth),A-B),	% clauses in prev layer
	(var_setting(select_aln,random) ->
		get_random(1,S,N1),
		get_random(A,B,N2);
		interval_to_list(1-S,L1),
		mem(N1,L1),
		(PrevDepth = 1 ->
			interval_to_list(N1-S,L2);
			interval_to_list(A-B,L2)),
		mem(N2,L2)),
	(N1 =< N2 -> Args = [N1,N2]; Args = [N2,N1]).

