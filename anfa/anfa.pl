%kielegitheto(Formulahalmaz, Literalok)

kielegitheto([],[])



inconsistent_with(A, Literalok) :-
    atomic_sentence(A),
    member(negation(A), Literalok).

inconsistent_with(negation(A), Literalok) :-
    atomic_sentence(A),
    member(A, Literalok).

atomic_sentence(A) :- member(A, [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z]).

formula

