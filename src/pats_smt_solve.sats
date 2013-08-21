

staload "./pats_lintprgm.sats"
staload "./pats_constraint3.sats"


fun {a:t@ype}
solve_smt {n:pos} (ics: &icnstrlst (a, n), n: int (n)): Ans2

