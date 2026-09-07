import PBCounterexample.Gram7CertificateData
import PBCounterexample.Gram7CoefficientRank
import PBCounterexample.Gram7CoefficientBounds
import PBCounterexample.Gram7Function
import PBCounterexample.Gram7Implicit

namespace PBCounterexample.Gram7.CertificateData
open Polynomial Gram7Coefficient
open scoped Matrix BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def p0 : ℚ[X] := u22 0
theorem h0 : Cert 23 p0 c0 := Cert.ofList 23 _

def p1 : ℚ[X] := u22 1
theorem h1 : Cert 23 p1 c1 := Cert.ofList 23 _

def p2 : ℚ[X] := u22 2
theorem h2 : Cert 23 p2 c2 := Cert.ofList 23 _

def p3 : ℚ[X] := u22 3
theorem h3 : Cert 23 p3 c3 := Cert.ofList 23 _

def p4 : ℚ[X] := u22 4
theorem h4 : Cert 23 p4 c4 := Cert.ofList 23 _

def p5 : ℚ[X] := u22 5
theorem h5 : Cert 23 p5 c5 := Cert.ofList 23 _

def p6 : ℚ[X] := u22 6
theorem h6 : Cert 23 p6 c6 := Cert.ofList 23 _

def p7 : ℚ[X] := C 1
theorem h7 : Cert 23 p7 c7 := Cert.const 23 1

def p8 : ℚ[X] := ofList [0,1]
theorem h8 : Cert 23 p8 c8 := Cert.ofList 23 _

def p9 : ℚ[X] := p0 * p0
theorem h9 : Cert 23 p9 c9 := Cert.mul h0 h0 (by decide +kernel)

def p10 : ℚ[X] := p1 * p1
theorem h10 : Cert 23 p10 c10 := Cert.mul h1 h1 (by decide +kernel)

def p11 : ℚ[X] := p2 * p2
theorem h11 : Cert 23 p11 c11 := Cert.mul h2 h2 (by decide +kernel)

def p12 : ℚ[X] := p7 + p9
theorem h12 : Cert 23 p12 c12 := Cert.add h7 h9 (by decide +kernel)

def p13 : ℚ[X] := p12 + p10
theorem h13 : Cert 23 p13 c13 := Cert.add h12 h10 (by decide +kernel)

def p14 : ℚ[X] := p13 + p11
theorem h14 : Cert 23 p14 c14 := Cert.add h13 h11 (by decide +kernel)

def p15 : ℚ[X] := p7 + p9
theorem h15 : Cert 23 p15 c15 := Cert.add h7 h9 (by decide +kernel)

def p16 : ℚ[X] := p15 - p10
theorem h16 : Cert 23 p16 c16 := Cert.sub h15 h10 (by decide +kernel)

def p17 : ℚ[X] := p16 - p11
theorem h17 : Cert 23 p17 c17 := Cert.sub h16 h11 (by decide +kernel)

def p18 : ℚ[X] := p0 * p1
theorem h18 : Cert 23 p18 c18 := Cert.mul h0 h1 (by decide +kernel)

def p19 : ℚ[X] := p18 - p2
theorem h19 : Cert 23 p19 c19 := Cert.sub h18 h2 (by decide +kernel)

def p20 : ℚ[X] := C (2) * p19
theorem h20 : Cert 23 p20 c20 := Cert.scale (2) h19 (by decide +kernel)

def p21 : ℚ[X] := p0 * p1
theorem h21 : Cert 23 p21 c21 := Cert.mul h0 h1 (by decide +kernel)

def p22 : ℚ[X] := p21 + p2
theorem h22 : Cert 23 p22 c22 := Cert.add h21 h2 (by decide +kernel)

def p23 : ℚ[X] := C (2) * p22
theorem h23 : Cert 23 p23 c23 := Cert.scale (2) h22 (by decide +kernel)

def p24 : ℚ[X] := p7 - p9
theorem h24 : Cert 23 p24 c24 := Cert.sub h7 h9 (by decide +kernel)

def p25 : ℚ[X] := p24 + p10
theorem h25 : Cert 23 p25 c25 := Cert.add h24 h10 (by decide +kernel)

def p26 : ℚ[X] := p25 - p11
theorem h26 : Cert 23 p26 c26 := Cert.sub h25 h11 (by decide +kernel)

def p27 : ℚ[X] := p0 * p2
theorem h27 : Cert 23 p27 c27 := Cert.mul h0 h2 (by decide +kernel)

def p28 : ℚ[X] := p27 - p1
theorem h28 : Cert 23 p28 c28 := Cert.sub h27 h1 (by decide +kernel)

def p29 : ℚ[X] := C (2) * p28
theorem h29 : Cert 23 p29 c29 := Cert.scale (2) h28 (by decide +kernel)

def p30 : ℚ[X] := p1 * p2
theorem h30 : Cert 23 p30 c30 := Cert.mul h1 h2 (by decide +kernel)

def p31 : ℚ[X] := p30 + p0
theorem h31 : Cert 23 p31 c31 := Cert.add h30 h0 (by decide +kernel)

def p32 : ℚ[X] := C (2) * p31
theorem h32 : Cert 23 p32 c32 := Cert.scale (2) h31 (by decide +kernel)

def p33 : ℚ[X] := p8 - p7
theorem h33 : Cert 23 p33 c33 := Cert.sub h8 h7 (by decide +kernel)

def p34 : ℚ[X] := p5 * p4
theorem h34 : Cert 23 p34 c34 := Cert.mul h5 h4 (by decide +kernel)

def p35 : ℚ[X] := p3 + p34
theorem h35 : Cert 23 p35 c35 := Cert.add h3 h34 (by decide +kernel)

def p36 : ℚ[X] := p6 * p3
theorem h36 : Cert 23 p36 c36 := Cert.mul h6 h3 (by decide +kernel)

def p37 : ℚ[X] := p33 * p4
theorem h37 : Cert 23 p37 c37 := Cert.mul h33 h4 (by decide +kernel)

def p38 : ℚ[X] := p36 + p37
theorem h38 : Cert 23 p38 c38 := Cert.add h36 h37 (by decide +kernel)

def p39 : ℚ[X] := p17 * p7
theorem h39 : Cert 23 p39 c39 := Cert.mul h17 h7 (by decide +kernel)

def p40 : ℚ[X] := p20 * p6
theorem h40 : Cert 23 p40 c40 := Cert.mul h20 h6 (by decide +kernel)

def p41 : ℚ[X] := p39 + p40
theorem h41 : Cert 23 p41 c41 := Cert.add h39 h40 (by decide +kernel)

def p42 : ℚ[X] := p17 * p5
theorem h42 : Cert 23 p42 c42 := Cert.mul h17 h5 (by decide +kernel)

def p43 : ℚ[X] := p20 * p33
theorem h43 : Cert 23 p43 c43 := Cert.mul h20 h33 (by decide +kernel)

def p44 : ℚ[X] := p42 + p43
theorem h44 : Cert 23 p44 c44 := Cert.add h42 h43 (by decide +kernel)

def p45 : ℚ[X] := p17 * p35
theorem h45 : Cert 23 p45 c45 := Cert.mul h17 h35 (by decide +kernel)

def p46 : ℚ[X] := p20 * p38
theorem h46 : Cert 23 p46 c46 := Cert.mul h20 h38 (by decide +kernel)

def p47 : ℚ[X] := p45 + p46
theorem h47 : Cert 23 p47 c47 := Cert.add h45 h46 (by decide +kernel)

def p48 : ℚ[X] := p23 * p7
theorem h48 : Cert 23 p48 c48 := Cert.mul h23 h7 (by decide +kernel)

def p49 : ℚ[X] := p26 * p6
theorem h49 : Cert 23 p49 c49 := Cert.mul h26 h6 (by decide +kernel)

def p50 : ℚ[X] := p48 + p49
theorem h50 : Cert 23 p50 c50 := Cert.add h48 h49 (by decide +kernel)

def p51 : ℚ[X] := p23 * p5
theorem h51 : Cert 23 p51 c51 := Cert.mul h23 h5 (by decide +kernel)

def p52 : ℚ[X] := p26 * p33
theorem h52 : Cert 23 p52 c52 := Cert.mul h26 h33 (by decide +kernel)

def p53 : ℚ[X] := p51 + p52
theorem h53 : Cert 23 p53 c53 := Cert.add h51 h52 (by decide +kernel)

def p54 : ℚ[X] := p23 * p35
theorem h54 : Cert 23 p54 c54 := Cert.mul h23 h35 (by decide +kernel)

def p55 : ℚ[X] := p26 * p38
theorem h55 : Cert 23 p55 c55 := Cert.mul h26 h38 (by decide +kernel)

def p56 : ℚ[X] := p54 + p55
theorem h56 : Cert 23 p56 c56 := Cert.add h54 h55 (by decide +kernel)

def p57 : ℚ[X] := p29 * p7
theorem h57 : Cert 23 p57 c57 := Cert.mul h29 h7 (by decide +kernel)

def p58 : ℚ[X] := p32 * p6
theorem h58 : Cert 23 p58 c58 := Cert.mul h32 h6 (by decide +kernel)

def p59 : ℚ[X] := p57 + p58
theorem h59 : Cert 23 p59 c59 := Cert.add h57 h58 (by decide +kernel)

def p60 : ℚ[X] := p29 * p5
theorem h60 : Cert 23 p60 c60 := Cert.mul h29 h5 (by decide +kernel)

def p61 : ℚ[X] := p32 * p33
theorem h61 : Cert 23 p61 c61 := Cert.mul h32 h33 (by decide +kernel)

def p62 : ℚ[X] := p60 + p61
theorem h62 : Cert 23 p62 c62 := Cert.add h60 h61 (by decide +kernel)

def p63 : ℚ[X] := p29 * p35
theorem h63 : Cert 23 p63 c63 := Cert.mul h29 h35 (by decide +kernel)

def p64 : ℚ[X] := p32 * p38
theorem h64 : Cert 23 p64 c64 := Cert.mul h32 h38 (by decide +kernel)

def p65 : ℚ[X] := p63 + p64
theorem h65 : Cert 23 p65 c65 := Cert.add h63 h64 (by decide +kernel)

def p66 : ℚ[X] := p14 * p7
theorem h66 : Cert 23 p66 c66 := Cert.mul h14 h7 (by decide +kernel)

def p67 : ℚ[X] := p14 * p5
theorem h67 : Cert 23 p67 c67 := Cert.mul h14 h5 (by decide +kernel)

def p68 : ℚ[X] := p14 * p35
theorem h68 : Cert 23 p68 c68 := Cert.mul h14 h35 (by decide +kernel)

def p69 : ℚ[X] := p14 * p6
theorem h69 : Cert 23 p69 c69 := Cert.mul h14 h6 (by decide +kernel)

def p70 : ℚ[X] := p14 * p33
theorem h70 : Cert 23 p70 c70 := Cert.mul h14 h33 (by decide +kernel)

def p71 : ℚ[X] := p14 * p38
theorem h71 : Cert 23 p71 c71 := Cert.mul h14 h38 (by decide +kernel)

def p72 : ℚ[X] := ofList []
theorem h72 : Cert 23 p72 c72 := Cert.ofList 23 _

def p73 : ℚ[X] := C (3) * p41
theorem h73 : Cert 23 p73 c73 := Cert.scale (3) h41 (by decide +kernel)

def p74 : ℚ[X] := C (1) * p47
theorem h74 : Cert 23 p74 c74 := Cert.scale (1) h47 (by decide +kernel)

def p75 : ℚ[X] := C (1) * p56
theorem h75 : Cert 23 p75 c75 := Cert.scale (1) h56 (by decide +kernel)

def p76 : ℚ[X] := C (1) * p65
theorem h76 : Cert 23 p76 c76 := Cert.scale (1) h65 (by decide +kernel)

def p77 : ℚ[X] := C (-2) * p66
theorem h77 : Cert 23 p77 c77 := Cert.scale (-2) h66 (by decide +kernel)

def p78 : ℚ[X] := C (-1) * p69
theorem h78 : Cert 23 p78 c78 := Cert.scale (-1) h69 (by decide +kernel)

def p79 : ℚ[X] := C (1) * p70
theorem h79 : Cert 23 p79 c79 := Cert.scale (1) h70 (by decide +kernel)

def p80 : ℚ[X] := p73 + p74
theorem h80 : Cert 23 p80 c80 := Cert.add h73 h74 (by decide +kernel)

def p81 : ℚ[X] := p80 + p75
theorem h81 : Cert 23 p81 c81 := Cert.add h80 h75 (by decide +kernel)

def p82 : ℚ[X] := p81 + p76
theorem h82 : Cert 23 p82 c82 := Cert.add h81 h76 (by decide +kernel)

def p83 : ℚ[X] := p82 + p77
theorem h83 : Cert 23 p83 c83 := Cert.add h82 h77 (by decide +kernel)

def p84 : ℚ[X] := p83 + p78
theorem h84 : Cert 23 p84 c84 := Cert.add h83 h78 (by decide +kernel)

def p85 : ℚ[X] := p84 + p79
theorem h85 : Cert 23 p85 c85 := Cert.add h84 h79 (by decide +kernel)

def p86 : ℚ[X] := C (-326) * p47
theorem h86 : Cert 23 p86 c86 := Cert.scale (-326) h47 (by decide +kernel)

def p87 : ℚ[X] := C (630) * p50
theorem h87 : Cert 23 p87 c87 := Cert.scale (630) h50 (by decide +kernel)

def p88 : ℚ[X] := C (490) * p56
theorem h88 : Cert 23 p88 c88 := Cert.scale (490) h56 (by decide +kernel)

def p89 : ℚ[X] := C (-59) * p65
theorem h89 : Cert 23 p89 c89 := Cert.scale (-59) h65 (by decide +kernel)

def p90 : ℚ[X] := C (-80) * p66
theorem h90 : Cert 23 p90 c90 := Cert.scale (-80) h66 (by decide +kernel)

def p91 : ℚ[X] := C (-3) * p67
theorem h91 : Cert 23 p91 c91 := Cert.scale (-3) h67 (by decide +kernel)

def p92 : ℚ[X] := C (185) * p69
theorem h92 : Cert 23 p92 c92 := Cert.scale (185) h69 (by decide +kernel)

def p93 : ℚ[X] := C (-80) * p70
theorem h93 : Cert 23 p93 c93 := Cert.scale (-80) h70 (by decide +kernel)

def p94 : ℚ[X] := p86 + p87
theorem h94 : Cert 23 p94 c94 := Cert.add h86 h87 (by decide +kernel)

def p95 : ℚ[X] := p94 + p88
theorem h95 : Cert 23 p95 c95 := Cert.add h94 h88 (by decide +kernel)

def p96 : ℚ[X] := p95 + p89
theorem h96 : Cert 23 p96 c96 := Cert.add h95 h89 (by decide +kernel)

def p97 : ℚ[X] := p96 + p90
theorem h97 : Cert 23 p97 c97 := Cert.add h96 h90 (by decide +kernel)

def p98 : ℚ[X] := p97 + p91
theorem h98 : Cert 23 p98 c98 := Cert.add h97 h91 (by decide +kernel)

def p99 : ℚ[X] := p98 + p92
theorem h99 : Cert 23 p99 c99 := Cert.add h98 h92 (by decide +kernel)

def p100 : ℚ[X] := p99 + p93
theorem h100 : Cert 23 p100 c100 := Cert.add h99 h93 (by decide +kernel)

def p101 : ℚ[X] := C (46) * p47
theorem h101 : Cert 23 p101 c101 := Cert.scale (46) h47 (by decide +kernel)

def p102 : ℚ[X] := C (35) * p56
theorem h102 : Cert 23 p102 c102 := Cert.scale (35) h56 (by decide +kernel)

def p103 : ℚ[X] := C (105) * p59
theorem h103 : Cert 23 p103 c103 := Cert.scale (105) h59 (by decide +kernel)

def p104 : ℚ[X] := C (-11) * p65
theorem h104 : Cert 23 p104 c104 := Cert.scale (-11) h65 (by decide +kernel)

def p105 : ℚ[X] := C (45) * p66
theorem h105 : Cert 23 p105 c105 := Cert.scale (45) h66 (by decide +kernel)

def p106 : ℚ[X] := C (38) * p67
theorem h106 : Cert 23 p106 c106 := Cert.scale (38) h67 (by decide +kernel)

def p107 : ℚ[X] := C (25) * p69
theorem h107 : Cert 23 p107 c107 := Cert.scale (25) h69 (by decide +kernel)

def p108 : ℚ[X] := C (45) * p70
theorem h108 : Cert 23 p108 c108 := Cert.scale (45) h70 (by decide +kernel)

def p109 : ℚ[X] := p101 + p102
theorem h109 : Cert 23 p109 c109 := Cert.add h101 h102 (by decide +kernel)

def p110 : ℚ[X] := p109 + p103
theorem h110 : Cert 23 p110 c110 := Cert.add h109 h103 (by decide +kernel)

def p111 : ℚ[X] := p110 + p104
theorem h111 : Cert 23 p111 c111 := Cert.add h110 h104 (by decide +kernel)

def p112 : ℚ[X] := p111 + p105
theorem h112 : Cert 23 p112 c112 := Cert.add h111 h105 (by decide +kernel)

def p113 : ℚ[X] := p112 + p106
theorem h113 : Cert 23 p113 c113 := Cert.add h112 h106 (by decide +kernel)

def p114 : ℚ[X] := p113 + p107
theorem h114 : Cert 23 p114 c114 := Cert.add h113 h107 (by decide +kernel)

def p115 : ℚ[X] := p114 + p108
theorem h115 : Cert 23 p115 c115 := Cert.add h114 h108 (by decide +kernel)

def p116 : ℚ[X] := C (90) * p44
theorem h116 : Cert 23 p116 c116 := Cert.scale (90) h44 (by decide +kernel)

def p117 : ℚ[X] := C (-38) * p47
theorem h117 : Cert 23 p117 c117 := Cert.scale (-38) h47 (by decide +kernel)

def p118 : ℚ[X] := C (10) * p56
theorem h118 : Cert 23 p118 c118 := Cert.scale (10) h56 (by decide +kernel)

def p119 : ℚ[X] := C (13) * p65
theorem h119 : Cert 23 p119 c119 := Cert.scale (13) h65 (by decide +kernel)

def p120 : ℚ[X] := C (40) * p66
theorem h120 : Cert 23 p120 c120 := Cert.scale (40) h66 (by decide +kernel)

def p121 : ℚ[X] := C (-9) * p67
theorem h121 : Cert 23 p121 c121 := Cert.scale (-9) h67 (by decide +kernel)

def p122 : ℚ[X] := C (-55) * p69
theorem h122 : Cert 23 p122 c122 := Cert.scale (-55) h69 (by decide +kernel)

def p123 : ℚ[X] := C (40) * p70
theorem h123 : Cert 23 p123 c123 := Cert.scale (40) h70 (by decide +kernel)

def p124 : ℚ[X] := p116 + p117
theorem h124 : Cert 23 p124 c124 := Cert.add h116 h117 (by decide +kernel)

def p125 : ℚ[X] := p124 + p118
theorem h125 : Cert 23 p125 c125 := Cert.add h124 h118 (by decide +kernel)

def p126 : ℚ[X] := p125 + p119
theorem h126 : Cert 23 p126 c126 := Cert.add h125 h119 (by decide +kernel)

def p127 : ℚ[X] := p126 + p120
theorem h127 : Cert 23 p127 c127 := Cert.add h126 h120 (by decide +kernel)

def p128 : ℚ[X] := p127 + p121
theorem h128 : Cert 23 p128 c128 := Cert.add h127 h121 (by decide +kernel)

def p129 : ℚ[X] := p128 + p122
theorem h129 : Cert 23 p129 c129 := Cert.add h128 h122 (by decide +kernel)

def p130 : ℚ[X] := p129 + p123
theorem h130 : Cert 23 p130 c130 := Cert.add h129 h123 (by decide +kernel)

def p131 : ℚ[X] := C (1) * p47
theorem h131 : Cert 23 p131 c131 := Cert.scale (1) h47 (by decide +kernel)

def p132 : ℚ[X] := C (3) * p53
theorem h132 : Cert 23 p132 c132 := Cert.scale (3) h53 (by decide +kernel)

def p133 : ℚ[X] := C (1) * p56
theorem h133 : Cert 23 p133 c133 := Cert.scale (1) h56 (by decide +kernel)

def p134 : ℚ[X] := C (1) * p65
theorem h134 : Cert 23 p134 c134 := Cert.scale (1) h65 (by decide +kernel)

def p135 : ℚ[X] := C (1) * p66
theorem h135 : Cert 23 p135 c135 := Cert.scale (1) h66 (by decide +kernel)

def p136 : ℚ[X] := C (-1) * p69
theorem h136 : Cert 23 p136 c136 := Cert.scale (-1) h69 (by decide +kernel)

def p137 : ℚ[X] := C (-2) * p70
theorem h137 : Cert 23 p137 c137 := Cert.scale (-2) h70 (by decide +kernel)

def p138 : ℚ[X] := p131 + p132
theorem h138 : Cert 23 p138 c138 := Cert.add h131 h132 (by decide +kernel)

def p139 : ℚ[X] := p138 + p133
theorem h139 : Cert 23 p139 c139 := Cert.add h138 h133 (by decide +kernel)

def p140 : ℚ[X] := p139 + p134
theorem h140 : Cert 23 p140 c140 := Cert.add h139 h134 (by decide +kernel)

def p141 : ℚ[X] := p140 + p135
theorem h141 : Cert 23 p141 c141 := Cert.add h140 h135 (by decide +kernel)

def p142 : ℚ[X] := p141 + p136
theorem h142 : Cert 23 p142 c142 := Cert.add h141 h136 (by decide +kernel)

def p143 : ℚ[X] := p142 + p137
theorem h143 : Cert 23 p143 c143 := Cert.add h142 h137 (by decide +kernel)

def p144 : ℚ[X] := C (23) * p47
theorem h144 : Cert 23 p144 c144 := Cert.scale (23) h47 (by decide +kernel)

def p145 : ℚ[X] := C (14) * p56
theorem h145 : Cert 23 p145 c145 := Cert.scale (14) h56 (by decide +kernel)

def p146 : ℚ[X] := C (63) * p62
theorem h146 : Cert 23 p146 c146 := Cert.scale (63) h62 (by decide +kernel)

def p147 : ℚ[X] := C (-37) * p65
theorem h147 : Cert 23 p147 c147 := Cert.scale (-37) h65 (by decide +kernel)

def p148 : ℚ[X] := C (5) * p66
theorem h148 : Cert 23 p148 c148 := Cert.scale (5) h66 (by decide +kernel)

def p149 : ℚ[X] := C (-30) * p67
theorem h149 : Cert 23 p149 c149 := Cert.scale (-30) h67 (by decide +kernel)

def p150 : ℚ[X] := C (-5) * p69
theorem h150 : Cert 23 p150 c150 := Cert.scale (-5) h69 (by decide +kernel)

def p151 : ℚ[X] := C (5) * p70
theorem h151 : Cert 23 p151 c151 := Cert.scale (5) h70 (by decide +kernel)

def p152 : ℚ[X] := p144 + p145
theorem h152 : Cert 23 p152 c152 := Cert.add h144 h145 (by decide +kernel)

def p153 : ℚ[X] := p152 + p146
theorem h153 : Cert 23 p153 c153 := Cert.add h152 h146 (by decide +kernel)

def p154 : ℚ[X] := p153 + p147
theorem h154 : Cert 23 p154 c154 := Cert.add h153 h147 (by decide +kernel)

def p155 : ℚ[X] := p154 + p148
theorem h155 : Cert 23 p155 c155 := Cert.add h154 h148 (by decide +kernel)

def p156 : ℚ[X] := p155 + p149
theorem h156 : Cert 23 p156 c156 := Cert.add h155 h149 (by decide +kernel)

def p157 : ℚ[X] := p156 + p150
theorem h157 : Cert 23 p157 c157 := Cert.add h156 h150 (by decide +kernel)

def p158 : ℚ[X] := p157 + p151
theorem h158 : Cert 23 p158 c158 := Cert.add h157 h151 (by decide +kernel)

def p159 : ℚ[X] := C (-4) * p47
theorem h159 : Cert 23 p159 c159 := Cert.scale (-4) h47 (by decide +kernel)

def p160 : ℚ[X] := C (-31) * p65
theorem h160 : Cert 23 p160 c160 := Cert.scale (-31) h65 (by decide +kernel)

def p161 : ℚ[X] := C (-10) * p66
theorem h161 : Cert 23 p161 c161 := Cert.scale (-10) h66 (by decide +kernel)

def p162 : ℚ[X] := C (-17) * p67
theorem h162 : Cert 23 p162 c162 := Cert.scale (-17) h67 (by decide +kernel)

def p163 : ℚ[X] := C (70) * p68
theorem h163 : Cert 23 p163 c163 := Cert.scale (70) h68 (by decide +kernel)

def p164 : ℚ[X] := C (-25) * p69
theorem h164 : Cert 23 p164 c164 := Cert.scale (-25) h69 (by decide +kernel)

def p165 : ℚ[X] := C (-10) * p70
theorem h165 : Cert 23 p165 c165 := Cert.scale (-10) h70 (by decide +kernel)

def p166 : ℚ[X] := p159 + p160
theorem h166 : Cert 23 p166 c166 := Cert.add h159 h160 (by decide +kernel)

def p167 : ℚ[X] := p166 + p161
theorem h167 : Cert 23 p167 c167 := Cert.add h166 h161 (by decide +kernel)

def p168 : ℚ[X] := p167 + p162
theorem h168 : Cert 23 p168 c168 := Cert.add h167 h162 (by decide +kernel)

def p169 : ℚ[X] := p168 + p163
theorem h169 : Cert 23 p169 c169 := Cert.add h168 h163 (by decide +kernel)

def p170 : ℚ[X] := p169 + p164
theorem h170 : Cert 23 p170 c170 := Cert.add h169 h164 (by decide +kernel)

def p171 : ℚ[X] := p170 + p165
theorem h171 : Cert 23 p171 c171 := Cert.add h170 h165 (by decide +kernel)

def p172 : ℚ[X] := C (4) * p47
theorem h172 : Cert 23 p172 c172 := Cert.scale (4) h47 (by decide +kernel)

def p173 : ℚ[X] := C (31) * p65
theorem h173 : Cert 23 p173 c173 := Cert.scale (31) h65 (by decide +kernel)

def p174 : ℚ[X] := C (10) * p66
theorem h174 : Cert 23 p174 c174 := Cert.scale (10) h66 (by decide +kernel)

def p175 : ℚ[X] := C (-53) * p67
theorem h175 : Cert 23 p175 c175 := Cert.scale (-53) h67 (by decide +kernel)

def p176 : ℚ[X] := C (25) * p69
theorem h176 : Cert 23 p176 c176 := Cert.scale (25) h69 (by decide +kernel)

def p177 : ℚ[X] := C (10) * p70
theorem h177 : Cert 23 p177 c177 := Cert.scale (10) h70 (by decide +kernel)

def p178 : ℚ[X] := C (70) * p71
theorem h178 : Cert 23 p178 c178 := Cert.scale (70) h71 (by decide +kernel)

def p179 : ℚ[X] := p172 + p173
theorem h179 : Cert 23 p179 c179 := Cert.add h172 h173 (by decide +kernel)

def p180 : ℚ[X] := p179 + p174
theorem h180 : Cert 23 p180 c180 := Cert.add h179 h174 (by decide +kernel)

def p181 : ℚ[X] := p180 + p175
theorem h181 : Cert 23 p181 c181 := Cert.add h180 h175 (by decide +kernel)

def p182 : ℚ[X] := p181 + p176
theorem h182 : Cert 23 p182 c182 := Cert.add h181 h176 (by decide +kernel)

def p183 : ℚ[X] := p182 + p177
theorem h183 : Cert 23 p183 c183 := Cert.add h182 h177 (by decide +kernel)

def p184 : ℚ[X] := p183 + p178
theorem h184 : Cert 23 p184 c184 := Cert.add h183 h178 (by decide +kernel)

def p185 : ℚ[X] := p47 * p47
theorem h185 : Cert 23 p185 c185 := Cert.mul h47 h47 (by decide +kernel)

def p186 : ℚ[X] := p47 * p56
theorem h186 : Cert 23 p186 c186 := Cert.mul h47 h56 (by decide +kernel)

def p187 : ℚ[X] := p47 * p65
theorem h187 : Cert 23 p187 c187 := Cert.mul h47 h65 (by decide +kernel)

def p188 : ℚ[X] := p47 * p66
theorem h188 : Cert 23 p188 c188 := Cert.mul h47 h66 (by decide +kernel)

def p189 : ℚ[X] := p47 * p69
theorem h189 : Cert 23 p189 c189 := Cert.mul h47 h69 (by decide +kernel)

def p190 : ℚ[X] := p47 * p67
theorem h190 : Cert 23 p190 c190 := Cert.mul h47 h67 (by decide +kernel)

def p191 : ℚ[X] := p47 * p70
theorem h191 : Cert 23 p191 c191 := Cert.mul h47 h70 (by decide +kernel)

def p192 : ℚ[X] := p56 * p56
theorem h192 : Cert 23 p192 c192 := Cert.mul h56 h56 (by decide +kernel)

def p193 : ℚ[X] := p56 * p65
theorem h193 : Cert 23 p193 c193 := Cert.mul h56 h65 (by decide +kernel)

def p194 : ℚ[X] := p56 * p66
theorem h194 : Cert 23 p194 c194 := Cert.mul h56 h66 (by decide +kernel)

def p195 : ℚ[X] := p56 * p69
theorem h195 : Cert 23 p195 c195 := Cert.mul h56 h69 (by decide +kernel)

def p196 : ℚ[X] := p56 * p67
theorem h196 : Cert 23 p196 c196 := Cert.mul h56 h67 (by decide +kernel)

def p197 : ℚ[X] := p56 * p70
theorem h197 : Cert 23 p197 c197 := Cert.mul h56 h70 (by decide +kernel)

def p198 : ℚ[X] := p65 * p65
theorem h198 : Cert 23 p198 c198 := Cert.mul h65 h65 (by decide +kernel)

def p199 : ℚ[X] := p65 * p66
theorem h199 : Cert 23 p199 c199 := Cert.mul h65 h66 (by decide +kernel)

def p200 : ℚ[X] := p65 * p69
theorem h200 : Cert 23 p200 c200 := Cert.mul h65 h69 (by decide +kernel)

def p201 : ℚ[X] := p65 * p67
theorem h201 : Cert 23 p201 c201 := Cert.mul h65 h67 (by decide +kernel)

def p202 : ℚ[X] := p65 * p70
theorem h202 : Cert 23 p202 c202 := Cert.mul h65 h70 (by decide +kernel)

def p203 : ℚ[X] := p66 * p66
theorem h203 : Cert 23 p203 c203 := Cert.mul h66 h66 (by decide +kernel)

def p204 : ℚ[X] := p66 * p69
theorem h204 : Cert 23 p204 c204 := Cert.mul h66 h69 (by decide +kernel)

def p205 : ℚ[X] := p66 * p67
theorem h205 : Cert 23 p205 c205 := Cert.mul h66 h67 (by decide +kernel)

def p206 : ℚ[X] := p66 * p70
theorem h206 : Cert 23 p206 c206 := Cert.mul h66 h70 (by decide +kernel)

def p207 : ℚ[X] := p69 * p69
theorem h207 : Cert 23 p207 c207 := Cert.mul h69 h69 (by decide +kernel)

def p208 : ℚ[X] := p69 * p67
theorem h208 : Cert 23 p208 c208 := Cert.mul h69 h67 (by decide +kernel)

def p209 : ℚ[X] := p69 * p70
theorem h209 : Cert 23 p209 c209 := Cert.mul h69 h70 (by decide +kernel)

def p210 : ℚ[X] := p67 * p67
theorem h210 : Cert 23 p210 c210 := Cert.mul h67 h67 (by decide +kernel)

def p211 : ℚ[X] := p67 * p70
theorem h211 : Cert 23 p211 c211 := Cert.mul h67 h70 (by decide +kernel)

def p212 : ℚ[X] := p70 * p70
theorem h212 : Cert 23 p212 c212 := Cert.mul h70 h70 (by decide +kernel)

end
end PBCounterexample.Gram7.CertificateData

namespace PBCounterexample.Gram7.CertificateData
open Polynomial Gram7Coefficient Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
local instance : Fact (Nat.Prime 1009) := ⟨by decide⟩
theorem linear_clear_rational : ∀ i j, (linearNumerator i j : ℚ) =
    (linearDenominator i : ℚ) * linearMinorData i j := by decide +kernel

theorem linear_clear_modular : linearNumerator.map (Int.castRingHom (ZMod 1009)) =
    diagonal (fun i => (linearDenominator i : ZMod 1009)) * linearReducedMinor := by decide +kernel

theorem linear_denominators_nonzero : ∀ i, (linearDenominator i : ZMod 1009) ≠ 0 := by decide +kernel

theorem linear_factorization : linearReducedMinor.submatrix linearPermutation id =
    linearLower * linearUpper := by decide +kernel

theorem linear_lower_triangular : linearLower.IsLowerTriangular := by decide +kernel

theorem linear_upper_triangular : linearUpper.IsUpperTriangular := by decide +kernel

theorem linear_lower_det : linearLower.det = 1 := by
  rw [det_of_isLowerTriangular _ linear_lower_triangular]
  decide +kernel

theorem linear_upper_det : linearUpper.det = 316 := by
  rw [det_of_isUpperTriangular linear_upper_triangular]
  decide +kernel

theorem linear_modular_minor : linearReducedMinor.det = 693 := by
  have hs : Equiv.Perm.sign linearPermutation = -1 := by
    simp only [linearPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]
    decide +kernel
  have h := congrArg Matrix.det linear_factorization
  rw [det_permute, det_mul, linear_lower_det, linear_upper_det, hs] at h
  change (-1 : ZMod 1009) * linearReducedMinor.det = 1 * 316 at h
  simp only [one_mul, neg_one_mul] at h
  have hn := congrArg (fun x : ZMod 1009 => -x) h
  simp only [neg_neg] at hn
  exact hn.trans (by decide +kernel)

theorem linear_numerator_modular_det_ne_zero :
    (linearNumerator.map (Int.castRingHom (ZMod 1009))).det ≠ 0 := by
  rw [linear_clear_modular, det_mul, det_diagonal, linear_modular_minor]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => linear_denominators_nonzero i)) (by decide)


theorem quadratic_clear_rational : ∀ i j, (quadraticNumerator i j : ℚ) =
    (quadraticDenominator i : ℚ) * quadraticMinorData i j := by decide +kernel

theorem quadratic_clear_modular : quadraticNumerator.map (Int.castRingHom (ZMod 1009)) =
    diagonal (fun i => (quadraticDenominator i : ZMod 1009)) * quadraticReducedMinor := by decide +kernel

theorem quadratic_denominators_nonzero : ∀ i, (quadraticDenominator i : ZMod 1009) ≠ 0 := by decide +kernel

theorem quadratic_factorization : quadraticReducedMinor.submatrix quadraticPermutation id =
    quadraticLower * quadraticUpper := by decide +kernel

theorem quadratic_lower_triangular : quadraticLower.IsLowerTriangular := by decide +kernel

theorem quadratic_upper_triangular : quadraticUpper.IsUpperTriangular := by decide +kernel

theorem quadratic_lower_det : quadraticLower.det = 1 := by
  rw [det_of_isLowerTriangular _ quadratic_lower_triangular]
  decide +kernel

theorem quadratic_upper_det : quadraticUpper.det = 660 := by
  rw [det_of_isUpperTriangular quadratic_upper_triangular]
  decide +kernel

theorem quadratic_modular_minor : quadraticReducedMinor.det = 349 := by
  have hs : Equiv.Perm.sign quadraticPermutation = -1 := by
    simp only [quadraticPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]
    decide +kernel
  have h := congrArg Matrix.det quadratic_factorization
  rw [det_permute, det_mul, quadratic_lower_det, quadratic_upper_det, hs] at h
  change (-1 : ZMod 1009) * quadraticReducedMinor.det = 1 * 660 at h
  simp only [one_mul, neg_one_mul] at h
  have hn := congrArg (fun x : ZMod 1009 => -x) h
  simp only [neg_neg] at hn
  exact hn.trans (by decide +kernel)

theorem quadratic_numerator_modular_det_ne_zero :
    (quadraticNumerator.map (Int.castRingHom (ZMod 1009))).det ≠ 0 := by
  rw [quadratic_clear_modular, det_mul, det_diagonal, quadratic_modular_minor]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => quadratic_denominators_nonzero i)) (by decide)


theorem gram_clear_rational : ∀ i j, (gramNumerator i j : ℚ) =
    (gramDenominator i : ℚ) * gramMinorData i j := by decide +kernel

theorem gram_clear_modular : gramNumerator.map (Int.castRingHom (ZMod 1009)) =
    diagonal (fun i => (gramDenominator i : ZMod 1009)) * gramReducedMinor := by decide +kernel

theorem gram_denominators_nonzero : ∀ i, (gramDenominator i : ZMod 1009) ≠ 0 := by decide +kernel

theorem gram_factorization : gramReducedMinor.submatrix gramPermutation id =
    gramLower * gramUpper := by decide +kernel

theorem gram_lower_triangular : gramLower.IsLowerTriangular := by decide +kernel

theorem gram_upper_triangular : gramUpper.IsUpperTriangular := by decide +kernel

theorem gram_lower_det : gramLower.det = 1 := by
  rw [det_of_isLowerTriangular _ gram_lower_triangular]
  decide +kernel

theorem gram_upper_det : gramUpper.det = 256 := by
  rw [det_of_isUpperTriangular gram_upper_triangular]
  decide +kernel

theorem gram_modular_minor : gramReducedMinor.det = 256 := by
  have hs : Equiv.Perm.sign gramPermutation = 1 := by
    simp only [gramPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]
    decide +kernel
  have h := congrArg Matrix.det gram_factorization
  rw [det_permute, det_mul, gram_lower_det, gram_upper_det, hs] at h
  change (1 : ZMod 1009) * gramReducedMinor.det = 1 * 256 at h
  simp only [one_mul, neg_one_mul] at h
  exact h

theorem gram_numerator_modular_det_ne_zero :
    (gramNumerator.map (Int.castRingHom (ZMod 1009))).det ≠ 0 := by
  rw [gram_clear_modular, det_mul, det_diagonal, gram_modular_minor]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => gram_denominators_nonzero i)) (by decide)


theorem gram_trace_relation : ∀ j, gramData 0 j + gramData 3 j = gramData 5 j := by decide +kernel

theorem quadratic_gram_annihilation : quadraticData * gramData.transpose = 0 := by decide +kernel
end PBCounterexample.Gram7.CertificateData

/-!
# A rational polynomial approximation of order twenty-two

The unknowns are k₀, k₁, k₂, t₀, t₁, C₀₁, C₁₀. The free parameter is
C₁₁ + 1 and C₀₀ is one. The seven coordinates are the unscaled negative
coordinates of the ambient quadratic form. Quadratic columns are ordered
lexicographically by pairs i ≤ j.
-/

noncomputable section

namespace PBCounterexample.Gram7

open Polynomial Gram7Coefficient Matrix CertificateData Filter Asymptotics
open scoped BigOperators Topology

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def constraintsQ : Matrix (Fin 8) (Fin 15) ℚ := !![
  3, 0, 1, 0, 0, 1, 0, 0, 1, -2, 0, 0, -1, 1, 0;
  0, 0, -326, 630, 0, 490, 0, 0, -59, -80, -3, 0, 185, -80, 0;
  0, 0, 46, 0, 0, 35, 105, 0, -11, 45, 38, 0, 25, 45, 0;
  0, 90, -38, 0, 0, 10, 0, 0, 13, 40, -9, 0, -55, 40, 0;
  0, 0, 1, 0, 3, 1, 0, 0, 1, 1, 0, 0, -1, -2, 0;
  0, 0, 23, 0, 0, 14, 0, 63, -37, 5, -30, 0, -5, 5, 0;
  0, 0, -4, 0, 0, 0, 0, 0, -31, -10, -17, 70, -25, -10, 0;
  0, 0, 4, 0, 0, 0, 0, 0, 31, 10, -53, 0, 25, 10, 70]

def constraintPolynomials22 : Fin 8 → ℚ[X] := (constraintsQ.map C) *ᵥ ambient22

def activeResidual22 (i : Fin 7) : ℚ[X] := constraintPolynomials22 i.succ

def unknownApproximation (i : Fin 7) : ℝ[X] := (u22 i).map (algebraMap ℚ ℝ)

def chartApproximation (i : Fin 7) : ℝ[X] := (coordinate22 i).map (algebraMap ℚ ℝ)

theorem u22_zero (i : Fin 7) : (u22 i).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, u22, FiniteCoefficientCertificate.polynomialOfList_coeff]
  fin_cases i <;> rfl

theorem u22_natDegree (i : Fin 7) : (u22 i).natDegree ≤ 22 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [u22, FiniteCoefficientCertificate.polynomialOfList_coeff]
  have hlen : (unknownCoefficients i).length = 23 := by fin_cases i <;> rfl
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem unknownApproximation_zero : (fun i => (unknownApproximation i).eval 0) = 0 := by
  ext i
  change ((u22 i).map (algebraMap ℚ ℝ)).eval 0 = 0
  rw [eval_zero_map, u22_zero, map_zero]

theorem ambient22_eq_nodes : ambient22 =
    ![p41,p44,p47,p50,p53,p56,p59,p62,p65,p66,p67,p68,p69,p70,p71] := by
  funext i
  fin_cases i <;>
    simp [ambient22, phi, phiA_apply, phiB_apply, rotationNumerator,
      rotationDenominator, chartCV,
      p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,
      p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,
      p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,
      p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,
      ofList, FiniteCoefficientCertificate.polynomialOfList, map_ofNat] <;> ring_nf <;> simp

theorem ambient22_certificate (i : Fin 15) :
    Cert 23 (ambient22 i) (ambientCoefficients i) := by
  rw [ambient22_eq_nodes]
  fin_cases i
  · exact h41
  · exact h44
  · exact h47
  · exact h50
  · exact h53
  · exact h56
  · exact h59
  · exact h62
  · exact h65
  · exact h66
  · exact h67
  · exact h68
  · exact h69
  · exact h70
  · exact h71

theorem constraintPolynomials22_eq_nodes : constraintPolynomials22 =
    ![p85,p100,p115,p130,p143,p158,p171,p184] := by
  unfold constraintPolynomials22
  rw [ambient22_eq_nodes]
  funext i
  fin_cases i <;>
    simp [constraintsQ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,
      p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,
      p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115,
      p116,p117,p118,p119,p120,p121,p122,p123,p124,p125,p126,p127,p128,p129,p130,
      p131,p132,p133,p134,p135,p136,p137,p138,p139,p140,p141,p142,p143,
      p144,p145,p146,p147,p148,p149,p150,p151,p152,p153,p154,p155,p156,p157,p158,
      p159,p160,p161,p162,p163,p164,p165,p166,p167,p168,p169,p170,p171,
      p172,p173,p174,p175,p176,p177,p178,p179,p180,p181,p182,p183,p184] <;> ring

theorem constraintPolynomials22_dvd (i : Fin 8) : X^23 ∣ constraintPolynomials22 i := by
  rw [constraintPolynomials22_eq_nodes]
  fin_cases i
  · exact h85.X_pow_dvd
  · exact h100.X_pow_dvd
  · exact h115.X_pow_dvd
  · exact h130.X_pow_dvd
  · exact h143.X_pow_dvd
  · exact h158.X_pow_dvd
  · exact h171.X_pow_dvd
  · exact h184.X_pow_dvd

theorem activeResidual22_dvd (i : Fin 7) : X^23 ∣ activeResidual22 i :=
  constraintPolynomials22_dvd i.succ

theorem quadratic22_eq_nodes : quadratic22 =
    ![p185,p186,p187,p188,p189,p190,p191,p192,p193,p194,p195,p196,p197,p198,
      p199,p200,p201,p202,p203,p204,p205,p206,p207,p208,p209,p210,p211,p212] := by
  funext i
  simp only [quadratic22, coordinate22, ambient22_eq_nodes]
  fin_cases i <;> rfl

theorem quadratic22_certificate (i : Fin 28) :
    Cert 23 (quadratic22 i) (quadraticCoefficients i) := by
  rw [quadratic22_eq_nodes]
  fin_cases i
  · exact h185
  · exact h186
  · exact h187
  · exact h188
  · exact h189
  · exact h190
  · exact h191
  · exact h192
  · exact h193
  · exact h194
  · exact h195
  · exact h196
  · exact h197
  · exact h198
  · exact h199
  · exact h200
  · exact h201
  · exact h202
  · exact h203
  · exact h204
  · exact h205
  · exact h206
  · exact h207
  · exact h208
  · exact h209
  · exact h210
  · exact h211
  · exact h212

def linearCoefficientMatrix : Matrix (Fin 23) (Fin 7) ℚ :=
  fun k i => (coordinate22 i).coeff k

def quadraticCoefficientMatrix : Matrix (Fin 23) (Fin 28) ℚ :=
  fun k i => (quadratic22 i).coeff k

theorem linearCoefficientMatrix_eq_data : linearCoefficientMatrix = linearData := by
  ext k i
  exact ambient22_certificate (negativeIndex i) k

theorem quadraticCoefficientMatrix_eq_data : quadraticCoefficientMatrix = quadraticData := by
  ext k i
  exact quadratic22_certificate i k

theorem linear_minor_det_ne_zero :
    (linearCoefficientMatrix.submatrix (Fin.castLE (by decide : 7 ≤ 23)) id).det ≠ 0 := by
  rw [linearCoefficientMatrix_eq_data]
  exact rational_det_ne_zero_of_row_clear _ _ _ linear_clear_rational
    linear_numerator_modular_det_ne_zero

theorem quadratic_minor_det_ne_zero :
    (quadraticCoefficientMatrix.submatrix id (Fin.castLE (by decide : 23 ≤ 28))).det ≠ 0 := by
  rw [quadraticCoefficientMatrix_eq_data]
  exact rational_det_ne_zero_of_row_clear _ _ _ quadratic_clear_rational
    quadratic_numerator_modular_det_ne_zero

theorem linearCoefficientMatrix_rank : linearCoefficientMatrix.rank = 7 := by
  have hr := Matrix.rank_of_det_ne_zero linear_minor_det_ne_zero
  have hl := Matrix.rank_submatrix_le linearCoefficientMatrix
    (Fin.castLE (by decide : 7 ≤ 23)) id
  have hu := Matrix.rank_le_card_width linearCoefficientMatrix
  simp only [Fintype.card_fin] at hr hu
  omega

theorem quadraticCoefficientMatrix_rank : quadraticCoefficientMatrix.rank = 23 := by
  have hr := Matrix.rank_of_det_ne_zero quadratic_minor_det_ne_zero
  have hl := Matrix.rank_submatrix_le quadraticCoefficientMatrix
    id (Fin.castLE (by decide : 23 ≤ 28))
  have hu := Matrix.rank_le_card_height quadraticCoefficientMatrix
  simp only [Fintype.card_fin] at hr hu
  omega

def gramPairs : Fin 6 → Index × Index := ![(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]

def quadraticExponent (i : Fin 28) : Fin 7 →₀ ℕ :=
  Finsupp.single (quadraticPairs i).1 1 + Finsupp.single (quadraticPairs i).2 1

theorem quadraticPairs_ordered : ∀ i, (quadraticPairs i).1 ≤ (quadraticPairs i).2 := by
  decide

theorem quadraticPairs_complete : ∀ i j : Fin 7, i ≤ j →
    ∃ k : Fin 28, quadraticPairs k = (i,j) := by
  decide

def quadraticMonomial (i : Fin 28) : MvPolynomial (Fin 7) ℝ :=
  MvPolynomial.X (quadraticPairs i).1 * MvPolynomial.X (quadraticPairs i).2

def gramPolynomials (i : Fin 6) : MvPolynomial (Fin 7) ℝ :=
  (aPolynomialᵀ * aPolynomial - bPolynomialᵀ * bPolynomial)
    (gramPairs i).1 (gramPairs i).2

def gramCoefficientMatrix : Matrix (Fin 6) (Fin 28) ℝ :=
  fun i j => MvPolynomial.coeff (quadraticExponent j) (gramPolynomials i)

theorem quadraticExponent_injective : Function.Injective quadraticExponent := by
  have key : ∀ i j : Fin 28,
      (∀ k : Fin 7,
        ((if k = (quadraticPairs i).1 then 1 else 0) +
          (if k = (quadraticPairs i).2 then 1 else 0) : ℕ) =
        ((if k = (quadraticPairs j).1 then 1 else 0) +
          (if k = (quadraticPairs j).2 then 1 else 0) : ℕ)) → i = j := by
    decide +kernel
  intro i j h
  apply key i j
  intro k
  simpa [quadraticExponent, Finsupp.single_apply, eq_comm] using DFunLike.congr_fun h k

theorem quadraticMonomial_coeff (i j : Fin 28) :
    MvPolynomial.coeff (quadraticExponent i) (quadraticMonomial j) =
      if j = i then 1 else 0 := by
  rw [quadraticMonomial, MvPolynomial.X, MvPolynomial.X,
    MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.coeff_monomial]
  change (if quadraticExponent j = quadraticExponent i then (1 : ℝ) else 0) = _
  simp only [quadraticExponent_injective.eq_iff]

theorem gramPolynomials_eq_coefficients (i : Fin 6) :
    gramPolynomials i =
      ∑ j : Fin 28, MvPolynomial.C (algebraMap ℚ ℝ (gramData i j)) * quadraticMonomial j := by
  apply MvPolynomial.funext
  intro z
  have hz : z = ![z 0,z 1,z 2,z 3,z 4,z 5,z 6] := by
    funext j
    fin_cases j <;> rfl
  rw [hz]
  fin_cases i <;>
    norm_num [gramPolynomials, gramPairs, quadraticMonomial, quadraticPairs,
      gramData, aPolynomial, bPolynomial, ambientPolynomial, aIndex, bIndex, basis,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val, Fin.succ] <;> ring!

theorem gramCoefficientMatrix_eq_data :
    gramCoefficientMatrix = gramData.map (algebraMap ℚ ℝ) := by
  ext i j
  simp [gramCoefficientMatrix, gramPolynomials_eq_coefficients,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, quadraticMonomial_coeff]

theorem eval_gramPolynomials (i : Fin 6) (z : Coord) :
    MvPolynomial.eval z (gramPolynomials i) = gramMatrix z (gramPairs i).1 (gramPairs i).2 := by
  simp [gramPolynomials, gramMatrix, Matrix.mul_apply, aPolynomial, bPolynomial,
    aMatrix, bMatrix, ambientA, ambientB]

theorem gram_minor_det_ne_zero :
    (gramCoefficientMatrix.submatrix Fin.castSucc (Fin.castLE (by decide : 5 ≤ 28))).det ≠ 0 := by
  rw [gramCoefficientMatrix_eq_data]
  exact cast_det_ne_zero gramMinorData
    (rational_det_ne_zero_of_row_clear _ _ _ gram_clear_rational
      gram_numerator_modular_det_ne_zero)

def gramRowCombination : Matrix (Fin 6) (Fin 5) ℚ := !![
  1,0,0,0,0; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1; 1,0,0,1,0]

theorem gramData_row_combination :
    gramData = gramRowCombination * gramData.submatrix Fin.castSucc id := by
  ext i j
  fin_cases i <;> simp [gramRowCombination, Matrix.mul_apply, Fin.sum_univ_succ,
    gram_trace_relation]

theorem gramCoefficientMatrix_rank : gramCoefficientMatrix.rank = 5 := by
  have hr := Matrix.rank_of_det_ne_zero gram_minor_det_ne_zero
  have hl := Matrix.rank_submatrix_le gramCoefficientMatrix
    Fin.castSucc (Fin.castLE (by decide : 5 ≤ 28))
  have hfactor : gramCoefficientMatrix =
      (gramRowCombination.map (algebraMap ℚ ℝ)) *
        ((gramData.submatrix Fin.castSucc id).map (algebraMap ℚ ℝ)) := by
    calc
      gramCoefficientMatrix = gramData.map (algebraMap ℚ ℝ) := gramCoefficientMatrix_eq_data
      _ = (gramRowCombination * gramData.submatrix Fin.castSucc id).map (algebraMap ℚ ℝ) :=
        congrArg (fun M : Matrix (Fin 6) (Fin 28) ℚ => M.map (algebraMap ℚ ℝ))
          gramData_row_combination
      _ = _ := Matrix.map_mul (f := algebraMap ℚ ℝ)
  have hu : gramCoefficientMatrix.rank ≤ 5 := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  simp only [Fintype.card_fin] at hr
  omega

theorem quadraticCoefficientMatrix_gram_annihilation :
    (quadraticCoefficientMatrix.map (algebraMap ℚ ℝ)) * gramCoefficientMatrixᵀ = 0 := by
  rw [quadraticCoefficientMatrix_eq_data, gramCoefficientMatrix_eq_data]
  change quadraticData.map (algebraMap ℚ ℝ) *
      gramData.transpose.map (algebraMap ℚ ℝ) = 0
  rw [← Matrix.map_mul, quadratic_gram_annihilation]
  ext i j
  simp

def linearCoefficientMatrixOver (K : Type*) [Field K] [CharZero K] :
    Matrix (Fin 23) (Fin 7) K :=
  fun k i => ((coordinate22 i).map (algebraMap ℚ K)).coeff k

def quadraticCoefficientMatrixOver (K : Type*) [Field K] [CharZero K] :
    Matrix (Fin 23) (Fin 28) K :=
  fun k i => (((coordinate22 (quadraticPairs i).1).map (algebraMap ℚ K)) *
      ((coordinate22 (quadraticPairs i).2).map (algebraMap ℚ K))).coeff k

theorem linearCoefficientMatrixOver_eq (K : Type*) [Field K] [CharZero K] :
    linearCoefficientMatrixOver K = linearCoefficientMatrix.map (algebraMap ℚ K) := by
  ext k i
  exact coeff_map _ _

theorem quadraticCoefficientMatrixOver_eq (K : Type*) [Field K] [CharZero K] :
    quadraticCoefficientMatrixOver K = quadraticCoefficientMatrix.map (algebraMap ℚ K) := by
  ext k i
  simp only [quadraticCoefficientMatrixOver, quadraticCoefficientMatrix, quadratic22,
    Matrix.map_apply, ← Polynomial.map_mul, coeff_map]

theorem linearCoefficientMatrixOver_rank (K : Type*) [Field K] [CharZero K] :
    (linearCoefficientMatrixOver K).rank = 7 := by
  have hm : ((linearCoefficientMatrixOver K).submatrix
      (Fin.castLE (by decide : 7 ≤ 23)) id).det ≠ 0 := by
    rw [linearCoefficientMatrixOver_eq]
    exact cast_det_ne_zero _ linear_minor_det_ne_zero
  have hr := Matrix.rank_of_det_ne_zero hm
  have hl := Matrix.rank_submatrix_le (linearCoefficientMatrixOver K)
    (Fin.castLE (by decide : 7 ≤ 23)) id
  have hu := Matrix.rank_le_card_width (linearCoefficientMatrixOver K)
  simp only [Fintype.card_fin] at hr hu
  omega

theorem quadraticCoefficientMatrixOver_rank (K : Type*) [Field K] [CharZero K] :
    (quadraticCoefficientMatrixOver K).rank = 23 := by
  have hm : ((quadraticCoefficientMatrixOver K).submatrix
      id (Fin.castLE (by decide : 23 ≤ 28))).det ≠ 0 := by
    rw [quadraticCoefficientMatrixOver_eq]
    exact cast_det_ne_zero _ quadratic_minor_det_ne_zero
  have hr := Matrix.rank_of_det_ne_zero hm
  have hl := Matrix.rank_submatrix_le (quadraticCoefficientMatrixOver K)
    id (Fin.castLE (by decide : 23 ≤ 28))
  have hu := Matrix.rank_le_card_height (quadraticCoefficientMatrixOver K)
  simp only [Fintype.card_fin] at hr hu
  omega

theorem ambient22_eval (t : ℝ) :
    (fun i => (ambient22 i).eval₂ (algebraMap ℚ ℝ) t) =
      phi ((unknownApproximation 0).eval t) ((unknownApproximation 1).eval t)
        ((unknownApproximation 2).eval t) ((unknownApproximation 3).eval t)
        ((unknownApproximation 4).eval t) 1 ((unknownApproximation 5).eval t)
        ((unknownApproximation 6).eval t) (-1+t) := by
  let e := Polynomial.eval₂RingHom (algebraMap ℚ ℝ) t
  have hX : e (-1+X) = -1+t := by
    change Polynomial.eval₂ (algebraMap ℚ ℝ) t (-1+X) = -1+t
    rw [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_one, Polynomial.eval₂_X]
  have h := phi_map e
    (u22 0) (u22 1) (u22 2) (u22 3) (u22 4) 1 (u22 5) (u22 6) (-1+X)
  rw [hX, map_one] at h
  simpa only [ambient22, unknownApproximation, ← eval₂_eq_eval_map,
    e, Polynomial.coe_eval₂RingHom] using h

theorem chartApproximation_eval (t : ℝ) :
    (fun i => (chartApproximation i).eval t) =
      coordinates (phi ((unknownApproximation 0).eval t) ((unknownApproximation 1).eval t)
        ((unknownApproximation 2).eval t) ((unknownApproximation 3).eval t)
        ((unknownApproximation 4).eval t) 1 ((unknownApproximation 5).eval t)
        ((unknownApproximation 6).eval t) (-1+t)) := by
  ext i
  simpa only [chartApproximation, coordinate22, coordinates, ← eval₂_eq_eval_map] using
    congrFun (ambient22_eval t) (negativeIndex i)

theorem constraintsQ_cast : constraintsQ.map (algebraMap ℚ ℝ) = constraintsMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [constraintsQ, constraintsMatrix]

theorem activeResidual22_eval (t : ℝ) (i : Fin 7) :
    (activeResidual22 i).eval₂ (algebraMap ℚ ℝ) t =
      activeConstraints (phi
        ((unknownApproximation 0).eval t) ((unknownApproximation 1).eval t)
        ((unknownApproximation 2).eval t) ((unknownApproximation 3).eval t)
        ((unknownApproximation 4).eval t) 1 ((unknownApproximation 5).eval t)
        ((unknownApproximation 6).eval t) (-1+t)) i := by
  simp only [activeResidual22, constraintPolynomials22, activeConstraints, constraints,
    Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun (ambient22_eval t) j]
  congr 1
  exact congrFun (congrFun constraintsQ_cast i.succ) j

theorem activeResidual22_real_dvd (i : Fin 7) :
    (X : ℝ[X])^23 ∣ (activeResidual22 i).map (algebraMap ℚ ℝ) := by
  simpa using (Polynomial.map_dvd (algebraMap ℚ ℝ) (activeResidual22_dvd i))

theorem activeResidual22_isBigO :
    (fun t : ℝ => fun i : Fin 7 => (activeResidual22 i).eval₂ (algebraMap ℚ ℝ) t)
      =O[𝓝 0] (fun t : ℝ => t^23) := by
  apply Asymptotics.isBigO_pi.mpr
  intro i
  simpa [eval₂_eq_eval_map] using eval_isBigO_pow_of_dvd (activeResidual22_real_dvd i)

theorem chartApproximation_zero : (fun i => (chartApproximation i).eval 0) =
    ![0,0,0,1,0,0,-1] := by
  rw [chartApproximation_eval]
  have hu (i : Fin 7) : (unknownApproximation i).eval 0 = 0 :=
    congrFun unknownApproximation_zero i
  simp only [hu, add_zero, phi_base]
  ext i
  fin_cases i <;> rfl

theorem chartApproximation_eval_eq_chart (t : ℝ) :
    (fun i => (chartApproximation i).eval t) =
      coordinates (chart (t, fun i => (unknownApproximation i).eval t)) :=
  chartApproximation_eval t

theorem chartSystem_unknownApproximation_isBigO :
    (fun t : ℝ => chartSystem (t, fun i => (unknownApproximation i).eval t))
      =O[𝓝 0] (fun t : ℝ => t^23) := by
  convert activeResidual22_isBigO using 1
  funext t i
  exact (activeResidual22_eval t i).symm

theorem unknownApproximation_error_isBigO :
    (fun t : ℝ => (fun i => (unknownApproximation i).eval t) - implicitUnknown t)
      =O[𝓝 0] (fun t : ℝ => t^23) :=
  polynomialApproximation_error_isBigO unknownApproximation unknownApproximation_zero 23
    chartSystem_unknownApproximation_isBigO

theorem chartApproximation_linear_rank :
    (show Matrix (Fin 23) (Fin 7) ℝ from fun k i => (chartApproximation i).coeff k).rank = 7 :=
  linearCoefficientMatrixOver_rank ℝ

theorem chartApproximation_quadratic_rank :
    (show Matrix (Fin 23) (Fin 28) ℝ from fun k i =>
      (chartApproximation (quadraticPairs i).1 *
        chartApproximation (quadraticPairs i).2).coeff k).rank = 23 :=
  quadraticCoefficientMatrixOver_rank ℝ

theorem finite_coefficient_certificate :
    (∀ i, (u22 i).eval 0 = 0) ∧
    (∀ i, (u22 i).natDegree ≤ 22) ∧
    (∀ i, (X : ℚ[X])^23 ∣ activeResidual22 i) ∧
    (show Matrix (Fin 23) (Fin 7) ℝ from fun k i =>
      (chartApproximation i).coeff k).rank = 7 ∧
    (show Matrix (Fin 23) (Fin 28) ℝ from fun k i =>
      (chartApproximation (quadraticPairs i).1 *
        chartApproximation (quadraticPairs i).2).coeff k).rank = 23 ∧
    gramCoefficientMatrix.rank = 5 ∧ baseJacobian.det = 16383079440000 ∧
    (fderiv ℝ chartSystem (0, chartBase)).comp
      (ContinuousLinearMap.inr ℝ ℝ ChartUnknown) = baseJacobianL :=
  ⟨u22_zero, u22_natDegree, activeResidual22_dvd, chartApproximation_linear_rank,
    chartApproximation_quadratic_rank, gramCoefficientMatrix_rank, baseJacobian_det,
    chartSystem_vertical_derivative⟩

end PBCounterexample.Gram7
