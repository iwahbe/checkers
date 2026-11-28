module nat_alias_chain

# An alias of an alias of … of `Nat` is `Nat` however many aliases
# there are: its subtraction must stay at or above zero.

type N0 = x~Nat
type N1 = x~N0
type N2 = x~N1
type N3 = x~N2
type N4 = x~N3
type N5 = x~N4
type N6 = x~N5
type N7 = x~N6
type N8 = x~N7
type N9 = x~N8
type N10 = x~N9
type N11 = x~N10
type N12 = x~N11
type N13 = x~N12
type N14 = x~N13
type N15 = x~N14
type N16 = x~N15
type N17 = x~N16
type N18 = x~N17
type N19 = x~N18
type N20 = x~N19
type N21 = x~N20
type N22 = x~N21
type N23 = x~N22
type N24 = x~N23
type N25 = x~N24
type N26 = x~N25
type N27 = x~N26
type N28 = x~N27
type N29 = x~N28
type N30 = x~N29
type N31 = x~N30
type N32 = x~N31
type N33 = x~N32
type N34 = x~N33
type N35 = x~N34
type N36 = x~N35
type N37 = x~N36
type N38 = x~N37
type N39 = x~N38
type N40 = x~N39
type N41 = x~N40
type N42 = x~N41
type N43 = x~N42
type N44 = x~N43
type N45 = x~N44
type N46 = x~N45
type N47 = x~N46
type N48 = x~N47
type N49 = x~N48
type N50 = x~N49
type N51 = x~N50
type N52 = x~N51
type N53 = x~N52
type N54 = x~N53
type N55 = x~N54
type N56 = x~N55
type N57 = x~N56
type N58 = x~N57
type N59 = x~N58
type N60 = x~N59
type N61 = x~N60
type N62 = x~N61
type N63 = x~N62
type N64 = x~N63
type N65 = x~N64
type N66 = x~N65
type N67 = x~N66
type N68 = x~N67
type N69 = x~N68
type N70 = x~N69

fn below -> r : r~N70
    0 - 1
