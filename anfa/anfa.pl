% general list utilities
does_not_occur_in(_,[]).
does_not_occur_in(A,[H|T]) :- dif(A,H), does_not_occur_in(A,T).

% syntax of formulas
atomic_formula(A) :- member(A, [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]).

formula(A) :- atomic_formula(A).
formula(lnot(A)) :- formula(A).
formula(land(A,B)) :- formula(A), formula(B).
formula(lor(A,B)) :- formula(A), formula(B).
formula(lthen(A,B)) :- formula(A), formula(B).
formula(liff(A,B)) :- formula(A), formula(B).

% semantic tableaux main predicate
semantic_tableaux(Formulas, State, Models):- semantic_tableaux(Formulas, [], [], State, Models).

%%%%%%%%%%%%%%%%
% Exit clauses %
%%%%%%%%%%%%%%%%

% 0. empty set is consistent
semantic_tableaux([], Po, Ne, open, [[Po, Ne]]).
% 1A positive literal conflicts with known negative literals
semantic_tableaux([F|_], _, Ne, closed, []):- 
    % atomic_formula(F),
    member(lnot(F), Ne).
% 1B: negated literal conflicts with known positive literals
semantic_tableaux([lnot(F)|_], Po, _, closed, []):- 
    atomic_formula(F),
    member(F, Po).

%%%%%%%%%%%%%%%%%%%%%
% Recursive clauses %
%%%%%%%%%%%%%%%%%%%%%

% 2A: negation of positive literal does not occur in known negative literals, so we move it to known positive literals
semantic_tableaux([F|Formulas], Po, Ne, State, Models):- 
    atomic_formula(F),
    does_not_occur_in(lnot(F), Ne),
    semantic_tableaux(Formulas, [F|Po], Ne, State, Models).

% 2A: the atom of negative literal does not occur in known positive literals, so we move it to known negative literals
semantic_tableaux([lnot(F)|Formulas], Po, Ne, State, Models):- 
    atomic_formula(F),
    does_not_occur_in(F, Po),
    semantic_tableaux(Formulas, Po, [lnot(F)|Ne], State, Models).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 3: non-branching connectives: %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% 3A: double negation:
semantic_tableaux([lnot(lnot(A))|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([A|Formulas], Po, Ne, State, Models).

% 3B: conjunction
semantic_tableaux([land(A,B)|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([A,B|Formulas], Po, Ne, State, Models).

% 3C: negated disjunction
semantic_tableaux([lnot(lor(A,B))|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([lnot(A), lnot(B)|Formulas], Po, Ne, State, Models).

% 3D: negated implication
semantic_tableaux([lnot(lthen(A,B))|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([A, lnot(B)|Formulas], Po, Ne, State, Models).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 4: branching connectives: %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% 4A: disjunction
semantic_tableaux([lor(A,B)|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([A|Formulas], Po, Ne, State1, Models1),
    semantic_tableaux([B|Formulas], Po, Ne, State2, Models2),
    combine_or(State1, Models1, State2, Models2, State, Models).

% 4B: negated conjunction
semantic_tableaux([lnot(land(A,B))|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([lnot(A)|Formulas], Po, Ne, State1, Models1),
    semantic_tableaux([lnot(B)|Formulas], Po, Ne, State2, Models2),
    combine_or(State1, Models1, State2, Models2, State, Models).
    
% 4C: conditional
semantic_tableaux([lthen(A,B)|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([lnot(A)|Formulas], Po, Ne, State1, Models1),
    semantic_tableaux([B|Formulas], Po, Ne, State2, Models2),
    combine_or(State1, Models1, State2, Models2, State, Models).

% 4D: biconditional
semantic_tableaux([liff(A,B)|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([A,B|Formulas], Po, Ne, State1, Models1),
    semantic_tableaux([lnot(A), lnot(B)|Formulas], Po, Ne, State2, Models2),
    combine_or(State1, Models1, State2, Models2, State, Models).

% 4D: negated biconditional
semantic_tableaux([lnot(liff(A,B))|Formulas], Po, Ne, State, Models):-
    semantic_tableaux([lnot(A),B|Formulas], Po, Ne, State1, Models1),
    semantic_tableaux([A, lnot(B)|Formulas], Po, Ne, State2, Models2),
    combine_or(State1, Models1, State2, Models2, State, Models).

% Model-building and open-closed relation determiner
combine_or(closed, [], closed, [], closed, []).
combine_or(open, Models1, closed, [], open, Models1).
combine_or(closed, [], open, Models2, open, Models2).
combine_or(open, Models1, open, Models2, open, Models) :-
    append(Models1, Models2, Models).

