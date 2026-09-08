import GafniTao.FordExplicitData.Negative0
import GafniTao.FordExplicitData.Negative1
import GafniTao.FordExplicitData.Negative2
import GafniTao.FordExplicitData.Positive0
import GafniTao.FordExplicitData.Positive1
import GafniTao.FordExplicitData.Positive2
import GafniTao.FordExplicitData.Positive3
import GafniTao.FordExplicitData.Positive4
import GafniTao.FordExplicitData.Positive5
import GafniTao.FordExplicitData.Positive6
import GafniTao.FordExplicitData.Positive7
import GafniTao.FordExplicitData.Positive8
import GafniTao.FordExplicitData.Positive9

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0


def fordNegativeUpperBlock0 : FordBiPolynomial :=
  Polynomial.C (fordNegativeUpperCoeff0) * Polynomial.X ^ 0 +
    Polynomial.C (fordNegativeUpperCoeff1) * Polynomial.X ^ 1 +
    Polynomial.C (fordNegativeUpperCoeff2) * Polynomial.X ^ 2 +
    Polynomial.C (fordNegativeUpperCoeff3) * Polynomial.X ^ 3 +
    Polynomial.C (fordNegativeUpperCoeff4) * Polynomial.X ^ 4 +
    Polynomial.C (fordNegativeUpperCoeff5) * Polynomial.X ^ 5 +
    Polynomial.C (fordNegativeUpperCoeff6) * Polynomial.X ^ 6 +
    Polynomial.C (fordNegativeUpperCoeff7) * Polynomial.X ^ 7 +
    Polynomial.C (fordNegativeUpperCoeff8) * Polynomial.X ^ 8 +
    Polynomial.C (fordNegativeUpperCoeff9) * Polynomial.X ^ 9 +
    Polynomial.C (fordNegativeUpperCoeff10) * Polynomial.X ^ 10 +
    Polynomial.C (fordNegativeUpperCoeff11) * Polynomial.X ^ 11 +
    Polynomial.C (fordNegativeUpperCoeff12) * Polynomial.X ^ 12 +
    Polynomial.C (fordNegativeUpperCoeff13) * Polynomial.X ^ 13 +
    Polynomial.C (fordNegativeUpperCoeff14) * Polynomial.X ^ 14 +
    Polynomial.C (fordNegativeUpperCoeff15) * Polynomial.X ^ 15 +
    Polynomial.C (fordNegativeUpperCoeff16) * Polynomial.X ^ 16 +
    Polynomial.C (fordNegativeUpperCoeff17) * Polynomial.X ^ 17 +
    Polynomial.C (fordNegativeUpperCoeff18) * Polynomial.X ^ 18 +
    Polynomial.C (fordNegativeUpperCoeff19) * Polynomial.X ^ 19

def fordNegativeUpperBlock1 : FordBiPolynomial :=
  Polynomial.C (fordNegativeUpperCoeff20) * Polynomial.X ^ 20 +
    Polynomial.C (fordNegativeUpperCoeff21) * Polynomial.X ^ 21 +
    Polynomial.C (fordNegativeUpperCoeff22) * Polynomial.X ^ 22 +
    Polynomial.C (fordNegativeUpperCoeff23) * Polynomial.X ^ 23 +
    Polynomial.C (fordNegativeUpperCoeff24) * Polynomial.X ^ 24 +
    Polynomial.C (fordNegativeUpperCoeff25) * Polynomial.X ^ 25 +
    Polynomial.C (fordNegativeUpperCoeff26) * Polynomial.X ^ 26 +
    Polynomial.C (fordNegativeUpperCoeff27) * Polynomial.X ^ 27 +
    Polynomial.C (fordNegativeUpperCoeff28) * Polynomial.X ^ 28 +
    Polynomial.C (fordNegativeUpperCoeff29) * Polynomial.X ^ 29 +
    Polynomial.C (fordNegativeUpperCoeff30) * Polynomial.X ^ 30 +
    Polynomial.C (fordNegativeUpperCoeff31) * Polynomial.X ^ 31 +
    Polynomial.C (fordNegativeUpperCoeff32) * Polynomial.X ^ 32 +
    Polynomial.C (fordNegativeUpperCoeff33) * Polynomial.X ^ 33 +
    Polynomial.C (fordNegativeUpperCoeff34) * Polynomial.X ^ 34 +
    Polynomial.C (fordNegativeUpperCoeff35) * Polynomial.X ^ 35 +
    Polynomial.C (fordNegativeUpperCoeff36) * Polynomial.X ^ 36 +
    Polynomial.C (fordNegativeUpperCoeff37) * Polynomial.X ^ 37 +
    Polynomial.C (fordNegativeUpperCoeff38) * Polynomial.X ^ 38 +
    Polynomial.C (fordNegativeUpperCoeff39) * Polynomial.X ^ 39

def fordNegativeUpperBlock2 : FordBiPolynomial :=
  Polynomial.C (fordNegativeUpperCoeff40) * Polynomial.X ^ 40 +
    Polynomial.C (fordNegativeUpperCoeff41) * Polynomial.X ^ 41 +
    Polynomial.C (fordNegativeUpperCoeff42) * Polynomial.X ^ 42 +
    Polynomial.C (fordNegativeUpperCoeff43) * Polynomial.X ^ 43 +
    Polynomial.C (fordNegativeUpperCoeff44) * Polynomial.X ^ 44 +
    Polynomial.C (fordNegativeUpperCoeff45) * Polynomial.X ^ 45 +
    Polynomial.C (fordNegativeUpperCoeff46) * Polynomial.X ^ 46 +
    Polynomial.C (fordNegativeUpperCoeff47) * Polynomial.X ^ 47 +
    Polynomial.C (fordNegativeUpperCoeff48) * Polynomial.X ^ 48 +
    Polynomial.C (fordNegativeUpperCoeff49) * Polynomial.X ^ 49 +
    Polynomial.C (fordNegativeUpperCoeff50) * Polynomial.X ^ 50 +
    Polynomial.C (fordNegativeUpperCoeff51) * Polynomial.X ^ 51 +
    Polynomial.C (fordNegativeUpperCoeff52) * Polynomial.X ^ 52 +
    Polynomial.C (fordNegativeUpperCoeff53) * Polynomial.X ^ 53 +
    Polynomial.C (fordNegativeUpperCoeff54) * Polynomial.X ^ 54

def fordPositiveUpperBlock0 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff0) * Polynomial.X ^ 0 +
    Polynomial.C (fordPositiveUpperCoeff1) * Polynomial.X ^ 1 +
    Polynomial.C (fordPositiveUpperCoeff2) * Polynomial.X ^ 2 +
    Polynomial.C (fordPositiveUpperCoeff3) * Polynomial.X ^ 3 +
    Polynomial.C (fordPositiveUpperCoeff4) * Polynomial.X ^ 4 +
    Polynomial.C (fordPositiveUpperCoeff5) * Polynomial.X ^ 5 +
    Polynomial.C (fordPositiveUpperCoeff6) * Polynomial.X ^ 6 +
    Polynomial.C (fordPositiveUpperCoeff7) * Polynomial.X ^ 7 +
    Polynomial.C (fordPositiveUpperCoeff8) * Polynomial.X ^ 8 +
    Polynomial.C (fordPositiveUpperCoeff9) * Polynomial.X ^ 9 +
    Polynomial.C (fordPositiveUpperCoeff10) * Polynomial.X ^ 10 +
    Polynomial.C (fordPositiveUpperCoeff11) * Polynomial.X ^ 11 +
    Polynomial.C (fordPositiveUpperCoeff12) * Polynomial.X ^ 12 +
    Polynomial.C (fordPositiveUpperCoeff13) * Polynomial.X ^ 13 +
    Polynomial.C (fordPositiveUpperCoeff14) * Polynomial.X ^ 14 +
    Polynomial.C (fordPositiveUpperCoeff15) * Polynomial.X ^ 15 +
    Polynomial.C (fordPositiveUpperCoeff16) * Polynomial.X ^ 16 +
    Polynomial.C (fordPositiveUpperCoeff17) * Polynomial.X ^ 17 +
    Polynomial.C (fordPositiveUpperCoeff18) * Polynomial.X ^ 18 +
    Polynomial.C (fordPositiveUpperCoeff19) * Polynomial.X ^ 19

def fordPositiveUpperBlock1 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff20) * Polynomial.X ^ 20 +
    Polynomial.C (fordPositiveUpperCoeff21) * Polynomial.X ^ 21 +
    Polynomial.C (fordPositiveUpperCoeff22) * Polynomial.X ^ 22 +
    Polynomial.C (fordPositiveUpperCoeff23) * Polynomial.X ^ 23 +
    Polynomial.C (fordPositiveUpperCoeff24) * Polynomial.X ^ 24 +
    Polynomial.C (fordPositiveUpperCoeff25) * Polynomial.X ^ 25 +
    Polynomial.C (fordPositiveUpperCoeff26) * Polynomial.X ^ 26 +
    Polynomial.C (fordPositiveUpperCoeff27) * Polynomial.X ^ 27 +
    Polynomial.C (fordPositiveUpperCoeff28) * Polynomial.X ^ 28 +
    Polynomial.C (fordPositiveUpperCoeff29) * Polynomial.X ^ 29 +
    Polynomial.C (fordPositiveUpperCoeff30) * Polynomial.X ^ 30 +
    Polynomial.C (fordPositiveUpperCoeff31) * Polynomial.X ^ 31 +
    Polynomial.C (fordPositiveUpperCoeff32) * Polynomial.X ^ 32 +
    Polynomial.C (fordPositiveUpperCoeff33) * Polynomial.X ^ 33 +
    Polynomial.C (fordPositiveUpperCoeff34) * Polynomial.X ^ 34 +
    Polynomial.C (fordPositiveUpperCoeff35) * Polynomial.X ^ 35 +
    Polynomial.C (fordPositiveUpperCoeff36) * Polynomial.X ^ 36 +
    Polynomial.C (fordPositiveUpperCoeff37) * Polynomial.X ^ 37 +
    Polynomial.C (fordPositiveUpperCoeff38) * Polynomial.X ^ 38 +
    Polynomial.C (fordPositiveUpperCoeff39) * Polynomial.X ^ 39

def fordPositiveUpperBlock2 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff40) * Polynomial.X ^ 40 +
    Polynomial.C (fordPositiveUpperCoeff41) * Polynomial.X ^ 41 +
    Polynomial.C (fordPositiveUpperCoeff42) * Polynomial.X ^ 42 +
    Polynomial.C (fordPositiveUpperCoeff43) * Polynomial.X ^ 43 +
    Polynomial.C (fordPositiveUpperCoeff44) * Polynomial.X ^ 44 +
    Polynomial.C (fordPositiveUpperCoeff45) * Polynomial.X ^ 45 +
    Polynomial.C (fordPositiveUpperCoeff46) * Polynomial.X ^ 46 +
    Polynomial.C (fordPositiveUpperCoeff47) * Polynomial.X ^ 47 +
    Polynomial.C (fordPositiveUpperCoeff48) * Polynomial.X ^ 48 +
    Polynomial.C (fordPositiveUpperCoeff49) * Polynomial.X ^ 49 +
    Polynomial.C (fordPositiveUpperCoeff50) * Polynomial.X ^ 50 +
    Polynomial.C (fordPositiveUpperCoeff51) * Polynomial.X ^ 51 +
    Polynomial.C (fordPositiveUpperCoeff52) * Polynomial.X ^ 52 +
    Polynomial.C (fordPositiveUpperCoeff53) * Polynomial.X ^ 53 +
    Polynomial.C (fordPositiveUpperCoeff54) * Polynomial.X ^ 54 +
    Polynomial.C (fordPositiveUpperCoeff55) * Polynomial.X ^ 55 +
    Polynomial.C (fordPositiveUpperCoeff56) * Polynomial.X ^ 56 +
    Polynomial.C (fordPositiveUpperCoeff57) * Polynomial.X ^ 57 +
    Polynomial.C (fordPositiveUpperCoeff58) * Polynomial.X ^ 58 +
    Polynomial.C (fordPositiveUpperCoeff59) * Polynomial.X ^ 59

def fordPositiveUpperBlock3 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff60) * Polynomial.X ^ 60 +
    Polynomial.C (fordPositiveUpperCoeff61) * Polynomial.X ^ 61 +
    Polynomial.C (fordPositiveUpperCoeff62) * Polynomial.X ^ 62 +
    Polynomial.C (fordPositiveUpperCoeff63) * Polynomial.X ^ 63 +
    Polynomial.C (fordPositiveUpperCoeff64) * Polynomial.X ^ 64 +
    Polynomial.C (fordPositiveUpperCoeff65) * Polynomial.X ^ 65 +
    Polynomial.C (fordPositiveUpperCoeff66) * Polynomial.X ^ 66 +
    Polynomial.C (fordPositiveUpperCoeff67) * Polynomial.X ^ 67 +
    Polynomial.C (fordPositiveUpperCoeff68) * Polynomial.X ^ 68 +
    Polynomial.C (fordPositiveUpperCoeff69) * Polynomial.X ^ 69 +
    Polynomial.C (fordPositiveUpperCoeff70) * Polynomial.X ^ 70 +
    Polynomial.C (fordPositiveUpperCoeff71) * Polynomial.X ^ 71 +
    Polynomial.C (fordPositiveUpperCoeff72) * Polynomial.X ^ 72 +
    Polynomial.C (fordPositiveUpperCoeff73) * Polynomial.X ^ 73 +
    Polynomial.C (fordPositiveUpperCoeff74) * Polynomial.X ^ 74 +
    Polynomial.C (fordPositiveUpperCoeff75) * Polynomial.X ^ 75 +
    Polynomial.C (fordPositiveUpperCoeff76) * Polynomial.X ^ 76 +
    Polynomial.C (fordPositiveUpperCoeff77) * Polynomial.X ^ 77 +
    Polynomial.C (fordPositiveUpperCoeff78) * Polynomial.X ^ 78 +
    Polynomial.C (fordPositiveUpperCoeff79) * Polynomial.X ^ 79

def fordPositiveUpperBlock4 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff80) * Polynomial.X ^ 80 +
    Polynomial.C (fordPositiveUpperCoeff81) * Polynomial.X ^ 81 +
    Polynomial.C (fordPositiveUpperCoeff82) * Polynomial.X ^ 82 +
    Polynomial.C (fordPositiveUpperCoeff83) * Polynomial.X ^ 83 +
    Polynomial.C (fordPositiveUpperCoeff84) * Polynomial.X ^ 84 +
    Polynomial.C (fordPositiveUpperCoeff85) * Polynomial.X ^ 85 +
    Polynomial.C (fordPositiveUpperCoeff86) * Polynomial.X ^ 86 +
    Polynomial.C (fordPositiveUpperCoeff87) * Polynomial.X ^ 87 +
    Polynomial.C (fordPositiveUpperCoeff88) * Polynomial.X ^ 88 +
    Polynomial.C (fordPositiveUpperCoeff89) * Polynomial.X ^ 89 +
    Polynomial.C (fordPositiveUpperCoeff90) * Polynomial.X ^ 90 +
    Polynomial.C (fordPositiveUpperCoeff91) * Polynomial.X ^ 91 +
    Polynomial.C (fordPositiveUpperCoeff92) * Polynomial.X ^ 92 +
    Polynomial.C (fordPositiveUpperCoeff93) * Polynomial.X ^ 93 +
    Polynomial.C (fordPositiveUpperCoeff94) * Polynomial.X ^ 94 +
    Polynomial.C (fordPositiveUpperCoeff95) * Polynomial.X ^ 95 +
    Polynomial.C (fordPositiveUpperCoeff96) * Polynomial.X ^ 96 +
    Polynomial.C (fordPositiveUpperCoeff97) * Polynomial.X ^ 97 +
    Polynomial.C (fordPositiveUpperCoeff98) * Polynomial.X ^ 98 +
    Polynomial.C (fordPositiveUpperCoeff99) * Polynomial.X ^ 99

def fordPositiveUpperBlock5 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff100) * Polynomial.X ^ 100 +
    Polynomial.C (fordPositiveUpperCoeff101) * Polynomial.X ^ 101 +
    Polynomial.C (fordPositiveUpperCoeff102) * Polynomial.X ^ 102 +
    Polynomial.C (fordPositiveUpperCoeff103) * Polynomial.X ^ 103 +
    Polynomial.C (fordPositiveUpperCoeff104) * Polynomial.X ^ 104 +
    Polynomial.C (fordPositiveUpperCoeff105) * Polynomial.X ^ 105 +
    Polynomial.C (fordPositiveUpperCoeff106) * Polynomial.X ^ 106 +
    Polynomial.C (fordPositiveUpperCoeff107) * Polynomial.X ^ 107 +
    Polynomial.C (fordPositiveUpperCoeff108) * Polynomial.X ^ 108 +
    Polynomial.C (fordPositiveUpperCoeff109) * Polynomial.X ^ 109 +
    Polynomial.C (fordPositiveUpperCoeff110) * Polynomial.X ^ 110 +
    Polynomial.C (fordPositiveUpperCoeff111) * Polynomial.X ^ 111 +
    Polynomial.C (fordPositiveUpperCoeff112) * Polynomial.X ^ 112 +
    Polynomial.C (fordPositiveUpperCoeff113) * Polynomial.X ^ 113 +
    Polynomial.C (fordPositiveUpperCoeff114) * Polynomial.X ^ 114 +
    Polynomial.C (fordPositiveUpperCoeff115) * Polynomial.X ^ 115 +
    Polynomial.C (fordPositiveUpperCoeff116) * Polynomial.X ^ 116 +
    Polynomial.C (fordPositiveUpperCoeff117) * Polynomial.X ^ 117 +
    Polynomial.C (fordPositiveUpperCoeff118) * Polynomial.X ^ 118 +
    Polynomial.C (fordPositiveUpperCoeff119) * Polynomial.X ^ 119

def fordPositiveUpperBlock6 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff120) * Polynomial.X ^ 120 +
    Polynomial.C (fordPositiveUpperCoeff121) * Polynomial.X ^ 121 +
    Polynomial.C (fordPositiveUpperCoeff122) * Polynomial.X ^ 122 +
    Polynomial.C (fordPositiveUpperCoeff123) * Polynomial.X ^ 123 +
    Polynomial.C (fordPositiveUpperCoeff124) * Polynomial.X ^ 124 +
    Polynomial.C (fordPositiveUpperCoeff125) * Polynomial.X ^ 125 +
    Polynomial.C (fordPositiveUpperCoeff126) * Polynomial.X ^ 126 +
    Polynomial.C (fordPositiveUpperCoeff127) * Polynomial.X ^ 127 +
    Polynomial.C (fordPositiveUpperCoeff128) * Polynomial.X ^ 128 +
    Polynomial.C (fordPositiveUpperCoeff129) * Polynomial.X ^ 129 +
    Polynomial.C (fordPositiveUpperCoeff130) * Polynomial.X ^ 130 +
    Polynomial.C (fordPositiveUpperCoeff131) * Polynomial.X ^ 131 +
    Polynomial.C (fordPositiveUpperCoeff132) * Polynomial.X ^ 132 +
    Polynomial.C (fordPositiveUpperCoeff133) * Polynomial.X ^ 133 +
    Polynomial.C (fordPositiveUpperCoeff134) * Polynomial.X ^ 134 +
    Polynomial.C (fordPositiveUpperCoeff135) * Polynomial.X ^ 135 +
    Polynomial.C (fordPositiveUpperCoeff136) * Polynomial.X ^ 136 +
    Polynomial.C (fordPositiveUpperCoeff137) * Polynomial.X ^ 137 +
    Polynomial.C (fordPositiveUpperCoeff138) * Polynomial.X ^ 138 +
    Polynomial.C (fordPositiveUpperCoeff139) * Polynomial.X ^ 139

def fordPositiveUpperBlock7 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff140) * Polynomial.X ^ 140 +
    Polynomial.C (fordPositiveUpperCoeff141) * Polynomial.X ^ 141 +
    Polynomial.C (fordPositiveUpperCoeff142) * Polynomial.X ^ 142 +
    Polynomial.C (fordPositiveUpperCoeff143) * Polynomial.X ^ 143 +
    Polynomial.C (fordPositiveUpperCoeff144) * Polynomial.X ^ 144 +
    Polynomial.C (fordPositiveUpperCoeff145) * Polynomial.X ^ 145 +
    Polynomial.C (fordPositiveUpperCoeff146) * Polynomial.X ^ 146 +
    Polynomial.C (fordPositiveUpperCoeff147) * Polynomial.X ^ 147 +
    Polynomial.C (fordPositiveUpperCoeff148) * Polynomial.X ^ 148 +
    Polynomial.C (fordPositiveUpperCoeff149) * Polynomial.X ^ 149 +
    Polynomial.C (fordPositiveUpperCoeff150) * Polynomial.X ^ 150 +
    Polynomial.C (fordPositiveUpperCoeff151) * Polynomial.X ^ 151 +
    Polynomial.C (fordPositiveUpperCoeff152) * Polynomial.X ^ 152 +
    Polynomial.C (fordPositiveUpperCoeff153) * Polynomial.X ^ 153 +
    Polynomial.C (fordPositiveUpperCoeff154) * Polynomial.X ^ 154 +
    Polynomial.C (fordPositiveUpperCoeff155) * Polynomial.X ^ 155 +
    Polynomial.C (fordPositiveUpperCoeff156) * Polynomial.X ^ 156 +
    Polynomial.C (fordPositiveUpperCoeff157) * Polynomial.X ^ 157 +
    Polynomial.C (fordPositiveUpperCoeff158) * Polynomial.X ^ 158 +
    Polynomial.C (fordPositiveUpperCoeff159) * Polynomial.X ^ 159

def fordPositiveUpperBlock8 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff160) * Polynomial.X ^ 160 +
    Polynomial.C (fordPositiveUpperCoeff161) * Polynomial.X ^ 161 +
    Polynomial.C (fordPositiveUpperCoeff162) * Polynomial.X ^ 162 +
    Polynomial.C (fordPositiveUpperCoeff163) * Polynomial.X ^ 163 +
    Polynomial.C (fordPositiveUpperCoeff164) * Polynomial.X ^ 164 +
    Polynomial.C (fordPositiveUpperCoeff165) * Polynomial.X ^ 165 +
    Polynomial.C (fordPositiveUpperCoeff166) * Polynomial.X ^ 166 +
    Polynomial.C (fordPositiveUpperCoeff167) * Polynomial.X ^ 167 +
    Polynomial.C (fordPositiveUpperCoeff168) * Polynomial.X ^ 168 +
    Polynomial.C (fordPositiveUpperCoeff169) * Polynomial.X ^ 169 +
    Polynomial.C (fordPositiveUpperCoeff170) * Polynomial.X ^ 170 +
    Polynomial.C (fordPositiveUpperCoeff171) * Polynomial.X ^ 171 +
    Polynomial.C (fordPositiveUpperCoeff172) * Polynomial.X ^ 172 +
    Polynomial.C (fordPositiveUpperCoeff173) * Polynomial.X ^ 173 +
    Polynomial.C (fordPositiveUpperCoeff174) * Polynomial.X ^ 174 +
    Polynomial.C (fordPositiveUpperCoeff175) * Polynomial.X ^ 175 +
    Polynomial.C (fordPositiveUpperCoeff176) * Polynomial.X ^ 176 +
    Polynomial.C (fordPositiveUpperCoeff177) * Polynomial.X ^ 177 +
    Polynomial.C (fordPositiveUpperCoeff178) * Polynomial.X ^ 178 +
    Polynomial.C (fordPositiveUpperCoeff179) * Polynomial.X ^ 179

def fordPositiveUpperBlock9 : FordBiPolynomial :=
  Polynomial.C (fordPositiveUpperCoeff180) * Polynomial.X ^ 180 +
    Polynomial.C (fordPositiveUpperCoeff181) * Polynomial.X ^ 181 +
    Polynomial.C (fordPositiveUpperCoeff182) * Polynomial.X ^ 182 +
    Polynomial.C (fordPositiveUpperCoeff183) * Polynomial.X ^ 183 +
    Polynomial.C (fordPositiveUpperCoeff184) * Polynomial.X ^ 184 +
    Polynomial.C (fordPositiveUpperCoeff185) * Polynomial.X ^ 185 +
    Polynomial.C (fordPositiveUpperCoeff186) * Polynomial.X ^ 186 +
    Polynomial.C (fordPositiveUpperCoeff187) * Polynomial.X ^ 187 +
    Polynomial.C (fordPositiveUpperCoeff188) * Polynomial.X ^ 188 +
    Polynomial.C (fordPositiveUpperCoeff189) * Polynomial.X ^ 189 +
    Polynomial.C (fordPositiveUpperCoeff190) * Polynomial.X ^ 190 +
    Polynomial.C (fordPositiveUpperCoeff191) * Polynomial.X ^ 191 +
    Polynomial.C (fordPositiveUpperCoeff192) * Polynomial.X ^ 192 +
    Polynomial.C (fordPositiveUpperCoeff193) * Polynomial.X ^ 193 +
    Polynomial.C (fordPositiveUpperCoeff194) * Polynomial.X ^ 194 +
    Polynomial.C (fordPositiveUpperCoeff195) * Polynomial.X ^ 195 +
    Polynomial.C (fordPositiveUpperCoeff196) * Polynomial.X ^ 196 +
    Polynomial.C (fordPositiveUpperCoeff197) * Polynomial.X ^ 197 +
    Polynomial.C (fordPositiveUpperCoeff198) * Polynomial.X ^ 198

def fordNegativePrimitiveBlock0 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 : ℚ) * fordNegativeUpperCoeff0) * Polynomial.X ^ 1 +
    Polynomial.C (Polynomial.C (1 / 2 : ℚ) * fordNegativeUpperCoeff1) * Polynomial.X ^ 2 +
    Polynomial.C (Polynomial.C (1 / 3 : ℚ) * fordNegativeUpperCoeff2) * Polynomial.X ^ 3 +
    Polynomial.C (Polynomial.C (1 / 4 : ℚ) * fordNegativeUpperCoeff3) * Polynomial.X ^ 4 +
    Polynomial.C (Polynomial.C (1 / 5 : ℚ) * fordNegativeUpperCoeff4) * Polynomial.X ^ 5 +
    Polynomial.C (Polynomial.C (1 / 6 : ℚ) * fordNegativeUpperCoeff5) * Polynomial.X ^ 6 +
    Polynomial.C (Polynomial.C (1 / 7 : ℚ) * fordNegativeUpperCoeff6) * Polynomial.X ^ 7 +
    Polynomial.C (Polynomial.C (1 / 8 : ℚ) * fordNegativeUpperCoeff7) * Polynomial.X ^ 8 +
    Polynomial.C (Polynomial.C (1 / 9 : ℚ) * fordNegativeUpperCoeff8) * Polynomial.X ^ 9 +
    Polynomial.C (Polynomial.C (1 / 10 : ℚ) * fordNegativeUpperCoeff9) * Polynomial.X ^ 10 +
    Polynomial.C (Polynomial.C (1 / 11 : ℚ) * fordNegativeUpperCoeff10) * Polynomial.X ^ 11 +
    Polynomial.C (Polynomial.C (1 / 12 : ℚ) * fordNegativeUpperCoeff11) * Polynomial.X ^ 12 +
    Polynomial.C (Polynomial.C (1 / 13 : ℚ) * fordNegativeUpperCoeff12) * Polynomial.X ^ 13 +
    Polynomial.C (Polynomial.C (1 / 14 : ℚ) * fordNegativeUpperCoeff13) * Polynomial.X ^ 14 +
    Polynomial.C (Polynomial.C (1 / 15 : ℚ) * fordNegativeUpperCoeff14) * Polynomial.X ^ 15 +
    Polynomial.C (Polynomial.C (1 / 16 : ℚ) * fordNegativeUpperCoeff15) * Polynomial.X ^ 16 +
    Polynomial.C (Polynomial.C (1 / 17 : ℚ) * fordNegativeUpperCoeff16) * Polynomial.X ^ 17 +
    Polynomial.C (Polynomial.C (1 / 18 : ℚ) * fordNegativeUpperCoeff17) * Polynomial.X ^ 18 +
    Polynomial.C (Polynomial.C (1 / 19 : ℚ) * fordNegativeUpperCoeff18) * Polynomial.X ^ 19 +
    Polynomial.C (Polynomial.C (1 / 20 : ℚ) * fordNegativeUpperCoeff19) * Polynomial.X ^ 20

def fordNegativePrimitiveBlock1 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 21 : ℚ) * fordNegativeUpperCoeff20) * Polynomial.X ^ 21 +
    Polynomial.C (Polynomial.C (1 / 22 : ℚ) * fordNegativeUpperCoeff21) * Polynomial.X ^ 22 +
    Polynomial.C (Polynomial.C (1 / 23 : ℚ) * fordNegativeUpperCoeff22) * Polynomial.X ^ 23 +
    Polynomial.C (Polynomial.C (1 / 24 : ℚ) * fordNegativeUpperCoeff23) * Polynomial.X ^ 24 +
    Polynomial.C (Polynomial.C (1 / 25 : ℚ) * fordNegativeUpperCoeff24) * Polynomial.X ^ 25 +
    Polynomial.C (Polynomial.C (1 / 26 : ℚ) * fordNegativeUpperCoeff25) * Polynomial.X ^ 26 +
    Polynomial.C (Polynomial.C (1 / 27 : ℚ) * fordNegativeUpperCoeff26) * Polynomial.X ^ 27 +
    Polynomial.C (Polynomial.C (1 / 28 : ℚ) * fordNegativeUpperCoeff27) * Polynomial.X ^ 28 +
    Polynomial.C (Polynomial.C (1 / 29 : ℚ) * fordNegativeUpperCoeff28) * Polynomial.X ^ 29 +
    Polynomial.C (Polynomial.C (1 / 30 : ℚ) * fordNegativeUpperCoeff29) * Polynomial.X ^ 30 +
    Polynomial.C (Polynomial.C (1 / 31 : ℚ) * fordNegativeUpperCoeff30) * Polynomial.X ^ 31 +
    Polynomial.C (Polynomial.C (1 / 32 : ℚ) * fordNegativeUpperCoeff31) * Polynomial.X ^ 32 +
    Polynomial.C (Polynomial.C (1 / 33 : ℚ) * fordNegativeUpperCoeff32) * Polynomial.X ^ 33 +
    Polynomial.C (Polynomial.C (1 / 34 : ℚ) * fordNegativeUpperCoeff33) * Polynomial.X ^ 34 +
    Polynomial.C (Polynomial.C (1 / 35 : ℚ) * fordNegativeUpperCoeff34) * Polynomial.X ^ 35 +
    Polynomial.C (Polynomial.C (1 / 36 : ℚ) * fordNegativeUpperCoeff35) * Polynomial.X ^ 36 +
    Polynomial.C (Polynomial.C (1 / 37 : ℚ) * fordNegativeUpperCoeff36) * Polynomial.X ^ 37 +
    Polynomial.C (Polynomial.C (1 / 38 : ℚ) * fordNegativeUpperCoeff37) * Polynomial.X ^ 38 +
    Polynomial.C (Polynomial.C (1 / 39 : ℚ) * fordNegativeUpperCoeff38) * Polynomial.X ^ 39 +
    Polynomial.C (Polynomial.C (1 / 40 : ℚ) * fordNegativeUpperCoeff39) * Polynomial.X ^ 40

def fordNegativePrimitiveBlock2 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 41 : ℚ) * fordNegativeUpperCoeff40) * Polynomial.X ^ 41 +
    Polynomial.C (Polynomial.C (1 / 42 : ℚ) * fordNegativeUpperCoeff41) * Polynomial.X ^ 42 +
    Polynomial.C (Polynomial.C (1 / 43 : ℚ) * fordNegativeUpperCoeff42) * Polynomial.X ^ 43 +
    Polynomial.C (Polynomial.C (1 / 44 : ℚ) * fordNegativeUpperCoeff43) * Polynomial.X ^ 44 +
    Polynomial.C (Polynomial.C (1 / 45 : ℚ) * fordNegativeUpperCoeff44) * Polynomial.X ^ 45 +
    Polynomial.C (Polynomial.C (1 / 46 : ℚ) * fordNegativeUpperCoeff45) * Polynomial.X ^ 46 +
    Polynomial.C (Polynomial.C (1 / 47 : ℚ) * fordNegativeUpperCoeff46) * Polynomial.X ^ 47 +
    Polynomial.C (Polynomial.C (1 / 48 : ℚ) * fordNegativeUpperCoeff47) * Polynomial.X ^ 48 +
    Polynomial.C (Polynomial.C (1 / 49 : ℚ) * fordNegativeUpperCoeff48) * Polynomial.X ^ 49 +
    Polynomial.C (Polynomial.C (1 / 50 : ℚ) * fordNegativeUpperCoeff49) * Polynomial.X ^ 50 +
    Polynomial.C (Polynomial.C (1 / 51 : ℚ) * fordNegativeUpperCoeff50) * Polynomial.X ^ 51 +
    Polynomial.C (Polynomial.C (1 / 52 : ℚ) * fordNegativeUpperCoeff51) * Polynomial.X ^ 52 +
    Polynomial.C (Polynomial.C (1 / 53 : ℚ) * fordNegativeUpperCoeff52) * Polynomial.X ^ 53 +
    Polynomial.C (Polynomial.C (1 / 54 : ℚ) * fordNegativeUpperCoeff53) * Polynomial.X ^ 54 +
    Polynomial.C (Polynomial.C (1 / 55 : ℚ) * fordNegativeUpperCoeff54) * Polynomial.X ^ 55

def fordPositivePrimitiveBlock0 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 : ℚ) * fordPositiveUpperCoeff0) * Polynomial.X ^ 1 +
    Polynomial.C (Polynomial.C (1 / 2 : ℚ) * fordPositiveUpperCoeff1) * Polynomial.X ^ 2 +
    Polynomial.C (Polynomial.C (1 / 3 : ℚ) * fordPositiveUpperCoeff2) * Polynomial.X ^ 3 +
    Polynomial.C (Polynomial.C (1 / 4 : ℚ) * fordPositiveUpperCoeff3) * Polynomial.X ^ 4 +
    Polynomial.C (Polynomial.C (1 / 5 : ℚ) * fordPositiveUpperCoeff4) * Polynomial.X ^ 5 +
    Polynomial.C (Polynomial.C (1 / 6 : ℚ) * fordPositiveUpperCoeff5) * Polynomial.X ^ 6 +
    Polynomial.C (Polynomial.C (1 / 7 : ℚ) * fordPositiveUpperCoeff6) * Polynomial.X ^ 7 +
    Polynomial.C (Polynomial.C (1 / 8 : ℚ) * fordPositiveUpperCoeff7) * Polynomial.X ^ 8 +
    Polynomial.C (Polynomial.C (1 / 9 : ℚ) * fordPositiveUpperCoeff8) * Polynomial.X ^ 9 +
    Polynomial.C (Polynomial.C (1 / 10 : ℚ) * fordPositiveUpperCoeff9) * Polynomial.X ^ 10 +
    Polynomial.C (Polynomial.C (1 / 11 : ℚ) * fordPositiveUpperCoeff10) * Polynomial.X ^ 11 +
    Polynomial.C (Polynomial.C (1 / 12 : ℚ) * fordPositiveUpperCoeff11) * Polynomial.X ^ 12 +
    Polynomial.C (Polynomial.C (1 / 13 : ℚ) * fordPositiveUpperCoeff12) * Polynomial.X ^ 13 +
    Polynomial.C (Polynomial.C (1 / 14 : ℚ) * fordPositiveUpperCoeff13) * Polynomial.X ^ 14 +
    Polynomial.C (Polynomial.C (1 / 15 : ℚ) * fordPositiveUpperCoeff14) * Polynomial.X ^ 15 +
    Polynomial.C (Polynomial.C (1 / 16 : ℚ) * fordPositiveUpperCoeff15) * Polynomial.X ^ 16 +
    Polynomial.C (Polynomial.C (1 / 17 : ℚ) * fordPositiveUpperCoeff16) * Polynomial.X ^ 17 +
    Polynomial.C (Polynomial.C (1 / 18 : ℚ) * fordPositiveUpperCoeff17) * Polynomial.X ^ 18 +
    Polynomial.C (Polynomial.C (1 / 19 : ℚ) * fordPositiveUpperCoeff18) * Polynomial.X ^ 19 +
    Polynomial.C (Polynomial.C (1 / 20 : ℚ) * fordPositiveUpperCoeff19) * Polynomial.X ^ 20

def fordPositivePrimitiveBlock1 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 21 : ℚ) * fordPositiveUpperCoeff20) * Polynomial.X ^ 21 +
    Polynomial.C (Polynomial.C (1 / 22 : ℚ) * fordPositiveUpperCoeff21) * Polynomial.X ^ 22 +
    Polynomial.C (Polynomial.C (1 / 23 : ℚ) * fordPositiveUpperCoeff22) * Polynomial.X ^ 23 +
    Polynomial.C (Polynomial.C (1 / 24 : ℚ) * fordPositiveUpperCoeff23) * Polynomial.X ^ 24 +
    Polynomial.C (Polynomial.C (1 / 25 : ℚ) * fordPositiveUpperCoeff24) * Polynomial.X ^ 25 +
    Polynomial.C (Polynomial.C (1 / 26 : ℚ) * fordPositiveUpperCoeff25) * Polynomial.X ^ 26 +
    Polynomial.C (Polynomial.C (1 / 27 : ℚ) * fordPositiveUpperCoeff26) * Polynomial.X ^ 27 +
    Polynomial.C (Polynomial.C (1 / 28 : ℚ) * fordPositiveUpperCoeff27) * Polynomial.X ^ 28 +
    Polynomial.C (Polynomial.C (1 / 29 : ℚ) * fordPositiveUpperCoeff28) * Polynomial.X ^ 29 +
    Polynomial.C (Polynomial.C (1 / 30 : ℚ) * fordPositiveUpperCoeff29) * Polynomial.X ^ 30 +
    Polynomial.C (Polynomial.C (1 / 31 : ℚ) * fordPositiveUpperCoeff30) * Polynomial.X ^ 31 +
    Polynomial.C (Polynomial.C (1 / 32 : ℚ) * fordPositiveUpperCoeff31) * Polynomial.X ^ 32 +
    Polynomial.C (Polynomial.C (1 / 33 : ℚ) * fordPositiveUpperCoeff32) * Polynomial.X ^ 33 +
    Polynomial.C (Polynomial.C (1 / 34 : ℚ) * fordPositiveUpperCoeff33) * Polynomial.X ^ 34 +
    Polynomial.C (Polynomial.C (1 / 35 : ℚ) * fordPositiveUpperCoeff34) * Polynomial.X ^ 35 +
    Polynomial.C (Polynomial.C (1 / 36 : ℚ) * fordPositiveUpperCoeff35) * Polynomial.X ^ 36 +
    Polynomial.C (Polynomial.C (1 / 37 : ℚ) * fordPositiveUpperCoeff36) * Polynomial.X ^ 37 +
    Polynomial.C (Polynomial.C (1 / 38 : ℚ) * fordPositiveUpperCoeff37) * Polynomial.X ^ 38 +
    Polynomial.C (Polynomial.C (1 / 39 : ℚ) * fordPositiveUpperCoeff38) * Polynomial.X ^ 39 +
    Polynomial.C (Polynomial.C (1 / 40 : ℚ) * fordPositiveUpperCoeff39) * Polynomial.X ^ 40

def fordPositivePrimitiveBlock2 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 41 : ℚ) * fordPositiveUpperCoeff40) * Polynomial.X ^ 41 +
    Polynomial.C (Polynomial.C (1 / 42 : ℚ) * fordPositiveUpperCoeff41) * Polynomial.X ^ 42 +
    Polynomial.C (Polynomial.C (1 / 43 : ℚ) * fordPositiveUpperCoeff42) * Polynomial.X ^ 43 +
    Polynomial.C (Polynomial.C (1 / 44 : ℚ) * fordPositiveUpperCoeff43) * Polynomial.X ^ 44 +
    Polynomial.C (Polynomial.C (1 / 45 : ℚ) * fordPositiveUpperCoeff44) * Polynomial.X ^ 45 +
    Polynomial.C (Polynomial.C (1 / 46 : ℚ) * fordPositiveUpperCoeff45) * Polynomial.X ^ 46 +
    Polynomial.C (Polynomial.C (1 / 47 : ℚ) * fordPositiveUpperCoeff46) * Polynomial.X ^ 47 +
    Polynomial.C (Polynomial.C (1 / 48 : ℚ) * fordPositiveUpperCoeff47) * Polynomial.X ^ 48 +
    Polynomial.C (Polynomial.C (1 / 49 : ℚ) * fordPositiveUpperCoeff48) * Polynomial.X ^ 49 +
    Polynomial.C (Polynomial.C (1 / 50 : ℚ) * fordPositiveUpperCoeff49) * Polynomial.X ^ 50 +
    Polynomial.C (Polynomial.C (1 / 51 : ℚ) * fordPositiveUpperCoeff50) * Polynomial.X ^ 51 +
    Polynomial.C (Polynomial.C (1 / 52 : ℚ) * fordPositiveUpperCoeff51) * Polynomial.X ^ 52 +
    Polynomial.C (Polynomial.C (1 / 53 : ℚ) * fordPositiveUpperCoeff52) * Polynomial.X ^ 53 +
    Polynomial.C (Polynomial.C (1 / 54 : ℚ) * fordPositiveUpperCoeff53) * Polynomial.X ^ 54 +
    Polynomial.C (Polynomial.C (1 / 55 : ℚ) * fordPositiveUpperCoeff54) * Polynomial.X ^ 55 +
    Polynomial.C (Polynomial.C (1 / 56 : ℚ) * fordPositiveUpperCoeff55) * Polynomial.X ^ 56 +
    Polynomial.C (Polynomial.C (1 / 57 : ℚ) * fordPositiveUpperCoeff56) * Polynomial.X ^ 57 +
    Polynomial.C (Polynomial.C (1 / 58 : ℚ) * fordPositiveUpperCoeff57) * Polynomial.X ^ 58 +
    Polynomial.C (Polynomial.C (1 / 59 : ℚ) * fordPositiveUpperCoeff58) * Polynomial.X ^ 59 +
    Polynomial.C (Polynomial.C (1 / 60 : ℚ) * fordPositiveUpperCoeff59) * Polynomial.X ^ 60

def fordPositivePrimitiveBlock3 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 61 : ℚ) * fordPositiveUpperCoeff60) * Polynomial.X ^ 61 +
    Polynomial.C (Polynomial.C (1 / 62 : ℚ) * fordPositiveUpperCoeff61) * Polynomial.X ^ 62 +
    Polynomial.C (Polynomial.C (1 / 63 : ℚ) * fordPositiveUpperCoeff62) * Polynomial.X ^ 63 +
    Polynomial.C (Polynomial.C (1 / 64 : ℚ) * fordPositiveUpperCoeff63) * Polynomial.X ^ 64 +
    Polynomial.C (Polynomial.C (1 / 65 : ℚ) * fordPositiveUpperCoeff64) * Polynomial.X ^ 65 +
    Polynomial.C (Polynomial.C (1 / 66 : ℚ) * fordPositiveUpperCoeff65) * Polynomial.X ^ 66 +
    Polynomial.C (Polynomial.C (1 / 67 : ℚ) * fordPositiveUpperCoeff66) * Polynomial.X ^ 67 +
    Polynomial.C (Polynomial.C (1 / 68 : ℚ) * fordPositiveUpperCoeff67) * Polynomial.X ^ 68 +
    Polynomial.C (Polynomial.C (1 / 69 : ℚ) * fordPositiveUpperCoeff68) * Polynomial.X ^ 69 +
    Polynomial.C (Polynomial.C (1 / 70 : ℚ) * fordPositiveUpperCoeff69) * Polynomial.X ^ 70 +
    Polynomial.C (Polynomial.C (1 / 71 : ℚ) * fordPositiveUpperCoeff70) * Polynomial.X ^ 71 +
    Polynomial.C (Polynomial.C (1 / 72 : ℚ) * fordPositiveUpperCoeff71) * Polynomial.X ^ 72 +
    Polynomial.C (Polynomial.C (1 / 73 : ℚ) * fordPositiveUpperCoeff72) * Polynomial.X ^ 73 +
    Polynomial.C (Polynomial.C (1 / 74 : ℚ) * fordPositiveUpperCoeff73) * Polynomial.X ^ 74 +
    Polynomial.C (Polynomial.C (1 / 75 : ℚ) * fordPositiveUpperCoeff74) * Polynomial.X ^ 75 +
    Polynomial.C (Polynomial.C (1 / 76 : ℚ) * fordPositiveUpperCoeff75) * Polynomial.X ^ 76 +
    Polynomial.C (Polynomial.C (1 / 77 : ℚ) * fordPositiveUpperCoeff76) * Polynomial.X ^ 77 +
    Polynomial.C (Polynomial.C (1 / 78 : ℚ) * fordPositiveUpperCoeff77) * Polynomial.X ^ 78 +
    Polynomial.C (Polynomial.C (1 / 79 : ℚ) * fordPositiveUpperCoeff78) * Polynomial.X ^ 79 +
    Polynomial.C (Polynomial.C (1 / 80 : ℚ) * fordPositiveUpperCoeff79) * Polynomial.X ^ 80

def fordPositivePrimitiveBlock4 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 81 : ℚ) * fordPositiveUpperCoeff80) * Polynomial.X ^ 81 +
    Polynomial.C (Polynomial.C (1 / 82 : ℚ) * fordPositiveUpperCoeff81) * Polynomial.X ^ 82 +
    Polynomial.C (Polynomial.C (1 / 83 : ℚ) * fordPositiveUpperCoeff82) * Polynomial.X ^ 83 +
    Polynomial.C (Polynomial.C (1 / 84 : ℚ) * fordPositiveUpperCoeff83) * Polynomial.X ^ 84 +
    Polynomial.C (Polynomial.C (1 / 85 : ℚ) * fordPositiveUpperCoeff84) * Polynomial.X ^ 85 +
    Polynomial.C (Polynomial.C (1 / 86 : ℚ) * fordPositiveUpperCoeff85) * Polynomial.X ^ 86 +
    Polynomial.C (Polynomial.C (1 / 87 : ℚ) * fordPositiveUpperCoeff86) * Polynomial.X ^ 87 +
    Polynomial.C (Polynomial.C (1 / 88 : ℚ) * fordPositiveUpperCoeff87) * Polynomial.X ^ 88 +
    Polynomial.C (Polynomial.C (1 / 89 : ℚ) * fordPositiveUpperCoeff88) * Polynomial.X ^ 89 +
    Polynomial.C (Polynomial.C (1 / 90 : ℚ) * fordPositiveUpperCoeff89) * Polynomial.X ^ 90 +
    Polynomial.C (Polynomial.C (1 / 91 : ℚ) * fordPositiveUpperCoeff90) * Polynomial.X ^ 91 +
    Polynomial.C (Polynomial.C (1 / 92 : ℚ) * fordPositiveUpperCoeff91) * Polynomial.X ^ 92 +
    Polynomial.C (Polynomial.C (1 / 93 : ℚ) * fordPositiveUpperCoeff92) * Polynomial.X ^ 93 +
    Polynomial.C (Polynomial.C (1 / 94 : ℚ) * fordPositiveUpperCoeff93) * Polynomial.X ^ 94 +
    Polynomial.C (Polynomial.C (1 / 95 : ℚ) * fordPositiveUpperCoeff94) * Polynomial.X ^ 95 +
    Polynomial.C (Polynomial.C (1 / 96 : ℚ) * fordPositiveUpperCoeff95) * Polynomial.X ^ 96 +
    Polynomial.C (Polynomial.C (1 / 97 : ℚ) * fordPositiveUpperCoeff96) * Polynomial.X ^ 97 +
    Polynomial.C (Polynomial.C (1 / 98 : ℚ) * fordPositiveUpperCoeff97) * Polynomial.X ^ 98 +
    Polynomial.C (Polynomial.C (1 / 99 : ℚ) * fordPositiveUpperCoeff98) * Polynomial.X ^ 99 +
    Polynomial.C (Polynomial.C (1 / 100 : ℚ) * fordPositiveUpperCoeff99) * Polynomial.X ^ 100

def fordPositivePrimitiveBlock5 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 101 : ℚ) * fordPositiveUpperCoeff100) * Polynomial.X ^ 101 +
    Polynomial.C (Polynomial.C (1 / 102 : ℚ) * fordPositiveUpperCoeff101) * Polynomial.X ^ 102 +
    Polynomial.C (Polynomial.C (1 / 103 : ℚ) * fordPositiveUpperCoeff102) * Polynomial.X ^ 103 +
    Polynomial.C (Polynomial.C (1 / 104 : ℚ) * fordPositiveUpperCoeff103) * Polynomial.X ^ 104 +
    Polynomial.C (Polynomial.C (1 / 105 : ℚ) * fordPositiveUpperCoeff104) * Polynomial.X ^ 105 +
    Polynomial.C (Polynomial.C (1 / 106 : ℚ) * fordPositiveUpperCoeff105) * Polynomial.X ^ 106 +
    Polynomial.C (Polynomial.C (1 / 107 : ℚ) * fordPositiveUpperCoeff106) * Polynomial.X ^ 107 +
    Polynomial.C (Polynomial.C (1 / 108 : ℚ) * fordPositiveUpperCoeff107) * Polynomial.X ^ 108 +
    Polynomial.C (Polynomial.C (1 / 109 : ℚ) * fordPositiveUpperCoeff108) * Polynomial.X ^ 109 +
    Polynomial.C (Polynomial.C (1 / 110 : ℚ) * fordPositiveUpperCoeff109) * Polynomial.X ^ 110 +
    Polynomial.C (Polynomial.C (1 / 111 : ℚ) * fordPositiveUpperCoeff110) * Polynomial.X ^ 111 +
    Polynomial.C (Polynomial.C (1 / 112 : ℚ) * fordPositiveUpperCoeff111) * Polynomial.X ^ 112 +
    Polynomial.C (Polynomial.C (1 / 113 : ℚ) * fordPositiveUpperCoeff112) * Polynomial.X ^ 113 +
    Polynomial.C (Polynomial.C (1 / 114 : ℚ) * fordPositiveUpperCoeff113) * Polynomial.X ^ 114 +
    Polynomial.C (Polynomial.C (1 / 115 : ℚ) * fordPositiveUpperCoeff114) * Polynomial.X ^ 115 +
    Polynomial.C (Polynomial.C (1 / 116 : ℚ) * fordPositiveUpperCoeff115) * Polynomial.X ^ 116 +
    Polynomial.C (Polynomial.C (1 / 117 : ℚ) * fordPositiveUpperCoeff116) * Polynomial.X ^ 117 +
    Polynomial.C (Polynomial.C (1 / 118 : ℚ) * fordPositiveUpperCoeff117) * Polynomial.X ^ 118 +
    Polynomial.C (Polynomial.C (1 / 119 : ℚ) * fordPositiveUpperCoeff118) * Polynomial.X ^ 119 +
    Polynomial.C (Polynomial.C (1 / 120 : ℚ) * fordPositiveUpperCoeff119) * Polynomial.X ^ 120

def fordPositivePrimitiveBlock6 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 121 : ℚ) * fordPositiveUpperCoeff120) * Polynomial.X ^ 121 +
    Polynomial.C (Polynomial.C (1 / 122 : ℚ) * fordPositiveUpperCoeff121) * Polynomial.X ^ 122 +
    Polynomial.C (Polynomial.C (1 / 123 : ℚ) * fordPositiveUpperCoeff122) * Polynomial.X ^ 123 +
    Polynomial.C (Polynomial.C (1 / 124 : ℚ) * fordPositiveUpperCoeff123) * Polynomial.X ^ 124 +
    Polynomial.C (Polynomial.C (1 / 125 : ℚ) * fordPositiveUpperCoeff124) * Polynomial.X ^ 125 +
    Polynomial.C (Polynomial.C (1 / 126 : ℚ) * fordPositiveUpperCoeff125) * Polynomial.X ^ 126 +
    Polynomial.C (Polynomial.C (1 / 127 : ℚ) * fordPositiveUpperCoeff126) * Polynomial.X ^ 127 +
    Polynomial.C (Polynomial.C (1 / 128 : ℚ) * fordPositiveUpperCoeff127) * Polynomial.X ^ 128 +
    Polynomial.C (Polynomial.C (1 / 129 : ℚ) * fordPositiveUpperCoeff128) * Polynomial.X ^ 129 +
    Polynomial.C (Polynomial.C (1 / 130 : ℚ) * fordPositiveUpperCoeff129) * Polynomial.X ^ 130 +
    Polynomial.C (Polynomial.C (1 / 131 : ℚ) * fordPositiveUpperCoeff130) * Polynomial.X ^ 131 +
    Polynomial.C (Polynomial.C (1 / 132 : ℚ) * fordPositiveUpperCoeff131) * Polynomial.X ^ 132 +
    Polynomial.C (Polynomial.C (1 / 133 : ℚ) * fordPositiveUpperCoeff132) * Polynomial.X ^ 133 +
    Polynomial.C (Polynomial.C (1 / 134 : ℚ) * fordPositiveUpperCoeff133) * Polynomial.X ^ 134 +
    Polynomial.C (Polynomial.C (1 / 135 : ℚ) * fordPositiveUpperCoeff134) * Polynomial.X ^ 135 +
    Polynomial.C (Polynomial.C (1 / 136 : ℚ) * fordPositiveUpperCoeff135) * Polynomial.X ^ 136 +
    Polynomial.C (Polynomial.C (1 / 137 : ℚ) * fordPositiveUpperCoeff136) * Polynomial.X ^ 137 +
    Polynomial.C (Polynomial.C (1 / 138 : ℚ) * fordPositiveUpperCoeff137) * Polynomial.X ^ 138 +
    Polynomial.C (Polynomial.C (1 / 139 : ℚ) * fordPositiveUpperCoeff138) * Polynomial.X ^ 139 +
    Polynomial.C (Polynomial.C (1 / 140 : ℚ) * fordPositiveUpperCoeff139) * Polynomial.X ^ 140

def fordPositivePrimitiveBlock7 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 141 : ℚ) * fordPositiveUpperCoeff140) * Polynomial.X ^ 141 +
    Polynomial.C (Polynomial.C (1 / 142 : ℚ) * fordPositiveUpperCoeff141) * Polynomial.X ^ 142 +
    Polynomial.C (Polynomial.C (1 / 143 : ℚ) * fordPositiveUpperCoeff142) * Polynomial.X ^ 143 +
    Polynomial.C (Polynomial.C (1 / 144 : ℚ) * fordPositiveUpperCoeff143) * Polynomial.X ^ 144 +
    Polynomial.C (Polynomial.C (1 / 145 : ℚ) * fordPositiveUpperCoeff144) * Polynomial.X ^ 145 +
    Polynomial.C (Polynomial.C (1 / 146 : ℚ) * fordPositiveUpperCoeff145) * Polynomial.X ^ 146 +
    Polynomial.C (Polynomial.C (1 / 147 : ℚ) * fordPositiveUpperCoeff146) * Polynomial.X ^ 147 +
    Polynomial.C (Polynomial.C (1 / 148 : ℚ) * fordPositiveUpperCoeff147) * Polynomial.X ^ 148 +
    Polynomial.C (Polynomial.C (1 / 149 : ℚ) * fordPositiveUpperCoeff148) * Polynomial.X ^ 149 +
    Polynomial.C (Polynomial.C (1 / 150 : ℚ) * fordPositiveUpperCoeff149) * Polynomial.X ^ 150 +
    Polynomial.C (Polynomial.C (1 / 151 : ℚ) * fordPositiveUpperCoeff150) * Polynomial.X ^ 151 +
    Polynomial.C (Polynomial.C (1 / 152 : ℚ) * fordPositiveUpperCoeff151) * Polynomial.X ^ 152 +
    Polynomial.C (Polynomial.C (1 / 153 : ℚ) * fordPositiveUpperCoeff152) * Polynomial.X ^ 153 +
    Polynomial.C (Polynomial.C (1 / 154 : ℚ) * fordPositiveUpperCoeff153) * Polynomial.X ^ 154 +
    Polynomial.C (Polynomial.C (1 / 155 : ℚ) * fordPositiveUpperCoeff154) * Polynomial.X ^ 155 +
    Polynomial.C (Polynomial.C (1 / 156 : ℚ) * fordPositiveUpperCoeff155) * Polynomial.X ^ 156 +
    Polynomial.C (Polynomial.C (1 / 157 : ℚ) * fordPositiveUpperCoeff156) * Polynomial.X ^ 157 +
    Polynomial.C (Polynomial.C (1 / 158 : ℚ) * fordPositiveUpperCoeff157) * Polynomial.X ^ 158 +
    Polynomial.C (Polynomial.C (1 / 159 : ℚ) * fordPositiveUpperCoeff158) * Polynomial.X ^ 159 +
    Polynomial.C (Polynomial.C (1 / 160 : ℚ) * fordPositiveUpperCoeff159) * Polynomial.X ^ 160

def fordPositivePrimitiveBlock8 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 161 : ℚ) * fordPositiveUpperCoeff160) * Polynomial.X ^ 161 +
    Polynomial.C (Polynomial.C (1 / 162 : ℚ) * fordPositiveUpperCoeff161) * Polynomial.X ^ 162 +
    Polynomial.C (Polynomial.C (1 / 163 : ℚ) * fordPositiveUpperCoeff162) * Polynomial.X ^ 163 +
    Polynomial.C (Polynomial.C (1 / 164 : ℚ) * fordPositiveUpperCoeff163) * Polynomial.X ^ 164 +
    Polynomial.C (Polynomial.C (1 / 165 : ℚ) * fordPositiveUpperCoeff164) * Polynomial.X ^ 165 +
    Polynomial.C (Polynomial.C (1 / 166 : ℚ) * fordPositiveUpperCoeff165) * Polynomial.X ^ 166 +
    Polynomial.C (Polynomial.C (1 / 167 : ℚ) * fordPositiveUpperCoeff166) * Polynomial.X ^ 167 +
    Polynomial.C (Polynomial.C (1 / 168 : ℚ) * fordPositiveUpperCoeff167) * Polynomial.X ^ 168 +
    Polynomial.C (Polynomial.C (1 / 169 : ℚ) * fordPositiveUpperCoeff168) * Polynomial.X ^ 169 +
    Polynomial.C (Polynomial.C (1 / 170 : ℚ) * fordPositiveUpperCoeff169) * Polynomial.X ^ 170 +
    Polynomial.C (Polynomial.C (1 / 171 : ℚ) * fordPositiveUpperCoeff170) * Polynomial.X ^ 171 +
    Polynomial.C (Polynomial.C (1 / 172 : ℚ) * fordPositiveUpperCoeff171) * Polynomial.X ^ 172 +
    Polynomial.C (Polynomial.C (1 / 173 : ℚ) * fordPositiveUpperCoeff172) * Polynomial.X ^ 173 +
    Polynomial.C (Polynomial.C (1 / 174 : ℚ) * fordPositiveUpperCoeff173) * Polynomial.X ^ 174 +
    Polynomial.C (Polynomial.C (1 / 175 : ℚ) * fordPositiveUpperCoeff174) * Polynomial.X ^ 175 +
    Polynomial.C (Polynomial.C (1 / 176 : ℚ) * fordPositiveUpperCoeff175) * Polynomial.X ^ 176 +
    Polynomial.C (Polynomial.C (1 / 177 : ℚ) * fordPositiveUpperCoeff176) * Polynomial.X ^ 177 +
    Polynomial.C (Polynomial.C (1 / 178 : ℚ) * fordPositiveUpperCoeff177) * Polynomial.X ^ 178 +
    Polynomial.C (Polynomial.C (1 / 179 : ℚ) * fordPositiveUpperCoeff178) * Polynomial.X ^ 179 +
    Polynomial.C (Polynomial.C (1 / 180 : ℚ) * fordPositiveUpperCoeff179) * Polynomial.X ^ 180

def fordPositivePrimitiveBlock9 : FordBiPolynomial :=
  Polynomial.C (Polynomial.C (1 / 181 : ℚ) * fordPositiveUpperCoeff180) * Polynomial.X ^ 181 +
    Polynomial.C (Polynomial.C (1 / 182 : ℚ) * fordPositiveUpperCoeff181) * Polynomial.X ^ 182 +
    Polynomial.C (Polynomial.C (1 / 183 : ℚ) * fordPositiveUpperCoeff182) * Polynomial.X ^ 183 +
    Polynomial.C (Polynomial.C (1 / 184 : ℚ) * fordPositiveUpperCoeff183) * Polynomial.X ^ 184 +
    Polynomial.C (Polynomial.C (1 / 185 : ℚ) * fordPositiveUpperCoeff184) * Polynomial.X ^ 185 +
    Polynomial.C (Polynomial.C (1 / 186 : ℚ) * fordPositiveUpperCoeff185) * Polynomial.X ^ 186 +
    Polynomial.C (Polynomial.C (1 / 187 : ℚ) * fordPositiveUpperCoeff186) * Polynomial.X ^ 187 +
    Polynomial.C (Polynomial.C (1 / 188 : ℚ) * fordPositiveUpperCoeff187) * Polynomial.X ^ 188 +
    Polynomial.C (Polynomial.C (1 / 189 : ℚ) * fordPositiveUpperCoeff188) * Polynomial.X ^ 189 +
    Polynomial.C (Polynomial.C (1 / 190 : ℚ) * fordPositiveUpperCoeff189) * Polynomial.X ^ 190 +
    Polynomial.C (Polynomial.C (1 / 191 : ℚ) * fordPositiveUpperCoeff190) * Polynomial.X ^ 191 +
    Polynomial.C (Polynomial.C (1 / 192 : ℚ) * fordPositiveUpperCoeff191) * Polynomial.X ^ 192 +
    Polynomial.C (Polynomial.C (1 / 193 : ℚ) * fordPositiveUpperCoeff192) * Polynomial.X ^ 193 +
    Polynomial.C (Polynomial.C (1 / 194 : ℚ) * fordPositiveUpperCoeff193) * Polynomial.X ^ 194 +
    Polynomial.C (Polynomial.C (1 / 195 : ℚ) * fordPositiveUpperCoeff194) * Polynomial.X ^ 195 +
    Polynomial.C (Polynomial.C (1 / 196 : ℚ) * fordPositiveUpperCoeff195) * Polynomial.X ^ 196 +
    Polynomial.C (Polynomial.C (1 / 197 : ℚ) * fordPositiveUpperCoeff196) * Polynomial.X ^ 197 +
    Polynomial.C (Polynomial.C (1 / 198 : ℚ) * fordPositiveUpperCoeff197) * Polynomial.X ^ 198 +
    Polynomial.C (Polynomial.C (1 / 199 : ℚ) * fordPositiveUpperCoeff198) * Polynomial.X ^ 199

def fordNegativeUpperExplicit : FordBiPolynomial :=
  fordNegativeUpperBlock0 +
    fordNegativeUpperBlock1 +
    fordNegativeUpperBlock2

def fordPositiveUpperExplicit : FordBiPolynomial :=
  fordPositiveUpperBlock0 +
    fordPositiveUpperBlock1 +
    fordPositiveUpperBlock2 +
    fordPositiveUpperBlock3 +
    fordPositiveUpperBlock4 +
    fordPositiveUpperBlock5 +
    fordPositiveUpperBlock6 +
    fordPositiveUpperBlock7 +
    fordPositiveUpperBlock8 +
    fordPositiveUpperBlock9

def fordNegativePrimitiveExplicit : FordBiPolynomial :=
  fordNegativePrimitiveBlock0 +
    fordNegativePrimitiveBlock1 +
    fordNegativePrimitiveBlock2

def fordPositivePrimitiveExplicit : FordBiPolynomial :=
  fordPositivePrimitiveBlock0 +
    fordPositivePrimitiveBlock1 +
    fordPositivePrimitiveBlock2 +
    fordPositivePrimitiveBlock3 +
    fordPositivePrimitiveBlock4 +
    fordPositivePrimitiveBlock5 +
    fordPositivePrimitiveBlock6 +
    fordPositivePrimitiveBlock7 +
    fordPositivePrimitiveBlock8 +
    fordPositivePrimitiveBlock9

end

end GafniTao
