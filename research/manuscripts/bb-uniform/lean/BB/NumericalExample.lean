import BB.NumericalExampleCore

/-! Generated exact witnesses for every displayed baseline table entry.
Regenerate with scripts/generate_numerical_example.py. All certificates use norm_num. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace BB.Numerical

theorem exact_state_0 : qState 0=((1,2),((36/41),(-18/41))) := by
  norm_num [qState]

theorem exact_state_1 : qState 1=(((36/41),(-18/41)),((1296/1681),(162/1681))) := by
  rw [qState,exact_state_0]
  norm_num [qUpdate,qAlpha]

theorem exact_state_2 : qState 2=(((1296/1681),(162/1681)),((5832/11767),(-2916/11767))) := by
  rw [qState,exact_state_1]
  norm_num [qUpdate,qAlpha]

theorem exact_state_3 : qState 3=(((5832/11767),(-2916/11767)),((26244/435379),(839808/435379))) := by
  rw [qState,exact_state_2]
  norm_num [qUpdate,qAlpha]

theorem exact_state_4 : qState 4=(((26244/435379),(839808/435379)),((118098/3047653),(-15116544/3047653))) := by
  rw [qState,exact_state_3]
  norm_num [qUpdate,qAlpha]

theorem exact_state_5 : qState 5=(((118098/3047653),(-15116544/3047653)),((1088391168/31211014373),(136048896/31211014373))) := by
  rw [qState,exact_state_4]
  norm_num [qUpdate,qAlpha]

theorem exact_state_6 : qState 6=(((1088391168/31211014373),(136048896/31211014373)),((160489808068608/5113643805886693),(-1224440064/5113643805886693))) := by
  rw [qState,exact_state_5]
  norm_num [qUpdate,qAlpha]

theorem exact_state_7 : qState 7=(((160489808068608/5113643805886693),(-1224440064/5113643805886693)),((722204136308736/189204820817807641),(352638738432/189204820817807641))) := by
  rw [qState,exact_state_6]
  norm_num [qUpdate,qAlpha]

theorem exact_state_8 : qState 8=(((722204136308736/189204820817807641),(352638738432/189204820817807641)),((3249918613389312/1625257036262071689116855677),(-27262293279626489757696/1625257036262071689116855677))) := by
  rw [qState,exact_state_7]
  norm_num [qUpdate,qAlpha]

theorem exact_state_9 : qState 9=(((3249918613389312/1625257036262071689116855677),(-27262293279626489757696/1625257036262071689116855677)),((14624633760251904/3408419170396257477333237701010289),(514558555883597270234985136128/3408419170396257477333237701010289))) := by
  rw [qState,exact_state_8]
  norm_num [qUpdate,qAlpha]

theorem exact_state_10 : qState 10=(((14624633760251904/3408419170396257477333237701010289),(514558555883597270234985136128/3408419170396257477333237701010289)),((9262054005904750864229732450304/2398461766518603453117461345522216442430780859249),(-4631027002952375432114866225152/2398461766518603453117461345522216442430780859249))) := by
  rw [qState,exact_state_9]
  norm_num [qUpdate,qAlpha]

theorem denominator_pos_0 : (0:ℚ) < (qState 0).1.1^2+10*(qState 0).1.2^2 := by
  norm_num [exact_state_0]

theorem denominator_pos_1 : (0:ℚ) < (qState 1).1.1^2+10*(qState 1).1.2^2 := by
  norm_num [exact_state_1]

theorem denominator_pos_2 : (0:ℚ) < (qState 2).1.1^2+10*(qState 2).1.2^2 := by
  norm_num [exact_state_2]

theorem denominator_pos_3 : (0:ℚ) < (qState 3).1.1^2+10*(qState 3).1.2^2 := by
  norm_num [exact_state_3]

theorem denominator_pos_4 : (0:ℚ) < (qState 4).1.1^2+10*(qState 4).1.2^2 := by
  norm_num [exact_state_4]

theorem denominator_pos_5 : (0:ℚ) < (qState 5).1.1^2+10*(qState 5).1.2^2 := by
  norm_num [exact_state_5]

theorem denominator_pos_6 : (0:ℚ) < (qState 6).1.1^2+10*(qState 6).1.2^2 := by
  norm_num [exact_state_6]

theorem denominator_pos_7 : (0:ℚ) < (qState 7).1.1^2+10*(qState 7).1.2^2 := by
  norm_num [exact_state_7]

theorem denominator_pos_8 : (0:ℚ) < (qState 8).1.1^2+10*(qState 8).1.2^2 := by
  norm_num [exact_state_8]

theorem denominator_pos_9 : (0:ℚ) < (qState 9).1.1^2+10*(qState 9).1.2^2 := by
  norm_num [exact_state_9]

theorem all_displayed_denominators_pos (k : Fin 10) :
    (0:ℚ) < (qState k.val).1.1^2+10*(qState k.val).1.2^2 := by
  fin_cases k
  · exact denominator_pos_0
  · exact denominator_pos_1
  · exact denominator_pos_2
  · exact denominator_pos_3
  · exact denominator_pos_4
  · exact denominator_pos_5
  · exact denominator_pos_6
  · exact denominator_pos_7
  · exact denominator_pos_8
  · exact denominator_pos_9

theorem alpha_rounding_0 : Rounded (alpha 0) (152439/1250000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_0]

theorem alpha_rounding_1 : Rounded (alpha 1) (3571429/10000000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_1]

theorem alpha_rounding_2 : Rounded (alpha 2) (1097973/1250000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_2]

theorem alpha_rounding_3 : Rounded (alpha 3) (3571429/10000000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_3]

theorem alpha_rounding_4 : Rounded (alpha 4) (1000879/10000000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_4]

theorem alpha_rounding_5 : Rounded (alpha 5) (200011/2000000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_5]

theorem alpha_rounding_6 : Rounded (alpha 6) (1097973/1250000) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_6]

theorem alpha_rounding_7 : Rounded (alpha 7) (1999999999/2000000000) (1/20000000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_7]

theorem alpha_rounding_8 : Rounded (alpha 8) (4999989271/5000000000) (1/20000000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_8]

theorem alpha_rounding_9 : Rounded (alpha 9) (1/10) (1/20000000) := by
  norm_num [Rounded,alpha,qAlphaAt,qAlpha,exact_state_9]

theorem objective_rounding_0 : Rounded (objective 0) (197561/500000) (1/2000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_0]

theorem objective_rounding_1 : Rounded (objective 1) (297661/1000000) (1/2000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_1]

theorem objective_rounding_2 : Rounded (objective 2) (31473/250000) (1/2000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_2]

theorem objective_rounding_3 : Rounded (objective 3) (46963/250000) (1/2000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_3]

theorem objective_rounding_4 : Rounded (objective 4) (61543/50000) (1/200000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_4]

theorem objective_rounding_5 : Rounded (objective 5) (608979/1000000000) (1/2000000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_5]

theorem objective_rounding_6 : Rounded (objective 6) (492497/1000000000) (1/2000000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_6]

theorem objective_rounding_7 : Rounded (objective 7) (728493/100000000000) (1/200000000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_7]

theorem objective_rounding_8 : Rounded (objective 8) (70343/5000000000000000) (1/20000000000000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_8]

theorem objective_rounding_9 : Rounded (objective 9) (22791/20000000000000) (1/200000000000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_9]

theorem objective_rounding_10 : Rounded (objective 10) (764263/100000000000000000000000000000000000000000) (1/200000000000000000000000000000000000000000) := by
  norm_num [Rounded,objective,qObjective,qGradient,exact_state_10]

theorem norm_rounding_0 : Rounded (gradientNorm 0) (122711/125000) (1/2000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 0) (gradientNorm_sq 0)
  all_goals norm_num [qNormSq,qGradient,exact_state_0]

theorem norm_rounding_1 : Rounded (gradientNorm 1) (77697/100000) (1/2000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 1) (gradientNorm_sq 1)
  all_goals norm_num [qNormSq,qGradient,exact_state_1]

theorem norm_rounding_2 : Rounded (gradientNorm 2) (138531/250000) (1/2000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 2) (gradientNorm_sq 2)
  all_goals norm_num [qNormSq,qGradient,exact_state_2]

theorem norm_rounding_3 : Rounded (gradientNorm 3) (38597/20000) (1/200000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 3) (gradientNorm_sq 3)
  all_goals norm_num [qNormSq,qGradient,exact_state_3]

theorem norm_rounding_4 : Rounded (gradientNorm 4) (496021/100000) (1/200000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 4) (gradientNorm_sq 4)
  all_goals norm_num [qNormSq,qGradient,exact_state_4]

theorem norm_rounding_5 : Rounded (gradientNorm 5) (175717/5000000) (1/20000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 5) (gradientNorm_sq 5)
  all_goals norm_num [qNormSq,qGradient,exact_state_5]

theorem norm_rounding_6 : Rounded (gradientNorm 6) (156923/5000000) (1/20000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 6) (gradientNorm_sq 6)
  all_goals norm_num [qNormSq,qGradient,exact_state_6]

theorem norm_rounding_7 : Rounded (gradientNorm 7) (76341/20000000) (1/200000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 7) (gradientNorm_sq 7)
  all_goals norm_num [qNormSq,qGradient,exact_state_7]

theorem norm_rounding_8 : Rounded (gradientNorm 8) (167741/10000000000) (1/20000000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 8) (gradientNorm_sq 8)
  all_goals norm_num [qNormSq,qGradient,exact_state_8]

theorem norm_rounding_9 : Rounded (gradientNorm 9) (150967/1000000000) (1/2000000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 9) (gradientNorm_sq 9)
  all_goals norm_num [qNormSq,qGradient,exact_state_9]

theorem norm_rounding_10 : Rounded (gradientNorm 10) (431747/100000000000000000000000) (1/200000000000000000000000) := by
  apply powered_rounding 2 (gradientNorm_nonneg 10) (gradientNorm_sq 10)
  all_goals norm_num [qNormSq,qGradient,exact_state_10]

theorem energy_rounding_0 : Rounded (energy 0) (2124/3125) (1/2000000) := by
  apply powered_rounding 11 (energy_nonneg 0) (energy_power 0)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_0]

theorem energy_rounding_1 : Rounded (energy 1) (12727/31250) (1/2000000) := by
  apply powered_rounding 11 (energy_nonneg 1) (energy_power 1)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_1]

theorem energy_rounding_2 : Rounded (energy 2) (54139/250000) (1/2000000) := by
  apply powered_rounding 11 (energy_nonneg 2) (energy_power 2)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_2]

theorem energy_rounding_3 : Rounded (energy 3) (682321/100000000) (1/200000000) := by
  apply powered_rounding 11 (energy_nonneg 3) (energy_power 3)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_3]

theorem energy_rounding_4 : Rounded (energy 4) (362813/100000000) (1/200000000) := by
  apply powered_rounding 11 (energy_nonneg 4) (energy_power 4)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_4]

theorem energy_rounding_5 : Rounded (energy 5) (833213/1000000000) (1/2000000000) := by
  apply powered_rounding 11 (energy_nonneg 5) (energy_power 5)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_5]

theorem energy_rounding_6 : Rounded (energy 6) (23121/200000000) (1/2000000000) := by
  apply powered_rounding 11 (energy_nonneg 6) (energy_power 6)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_6]

theorem energy_rounding_7 : Rounded (energy 7) (364247/100000000000) (1/200000000000) := by
  apply powered_rounding 11 (energy_nonneg 7) (energy_power 7)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_7]

theorem energy_rounding_8 : Rounded (energy 8) (362847/5000000000000000000000000000) (1/20000000000000000000000000000) := by
  apply powered_rounding 11 (energy_nonneg 8) (energy_power 8)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_8]

theorem energy_rounding_9 : Rounded (energy 9) (53461/10000000000000000000000000000000000000) (1/200000000000000000000000000000000000000) := by
  apply powered_rounding 11 (energy_nonneg 9) (energy_power 9)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_9]

theorem energy_rounding_10 : Rounded (energy 10) (131467/10000000000000000000000000000000000000000) (1/20000000000000000000000000000000000000000) := by
  apply powered_rounding 11 (energy_nonneg 10) (energy_power 10)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_10]

theorem energyRatio_rounding_0 : Rounded (energyRatio 0) (749/1250) (1/2000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 0) (energyRatio_power 0)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_0,exact_state_1]

theorem energyRatio_rounding_1 : Rounded (energyRatio 1) (265867/500000) (1/2000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 1) (energyRatio_power 1)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_1,exact_state_2]

theorem energyRatio_rounding_2 : Rounded (energyRatio 2) (157539/5000000) (1/20000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 2) (energyRatio_power 2)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_2,exact_state_3]

theorem energyRatio_rounding_3 : Rounded (energyRatio 3) (265867/500000) (1/2000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 3) (energyRatio_power 3)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_3,exact_state_4]

theorem energyRatio_rounding_4 : Rounded (energyRatio 4) (229653/1000000) (1/2000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 4) (energyRatio_power 4)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_4,exact_state_5]

theorem energyRatio_rounding_5 : Rounded (energyRatio 5) (69373/500000) (1/2000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 5) (energyRatio_power 5)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_5,exact_state_6]

theorem energyRatio_rounding_6 : Rounded (energyRatio 6) (157539/5000000) (1/20000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 6) (energyRatio_power 6)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_6,exact_state_7]

theorem energyRatio_rounding_7 : Rounded (energyRatio 7) (3113/156250000000000000000) (1/20000000000000000000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 7) (energyRatio_power 7)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_7,exact_state_8]

theorem energyRatio_rounding_8 : Rounded (energyRatio 8) (736687/10000000000000000) (1/20000000000000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 8) (energyRatio_power 8)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_8,exact_state_9]

theorem energyRatio_rounding_9 : Rounded (energyRatio 9) (30739/12500000) (1/200000000) := by
  apply powered_rounding 11 (energyRatio_nonneg 9) (energyRatio_power 9)
  all_goals norm_num [qEnergyPower,qGradient,exact_state_9,exact_state_10]

def alphaCenter : Fin 10 → ℚ := ![(152439/1250000),(3571429/10000000),(1097973/1250000),(3571429/10000000),(1000879/10000000),(200011/2000000),(1097973/1250000),(1999999999/2000000000),(4999989271/5000000000),(1/10)]
def alphaRadius : Fin 10 → ℚ := ![(1/20000000),(1/20000000),(1/20000000),(1/20000000),(1/20000000),(1/20000000),(1/20000000),(1/20000000000),(1/20000000000),(1/20000000)]

theorem all_alpha_rounding (k : Fin 10) :
    Rounded (alpha k.val) (alphaCenter k) (alphaRadius k) := by
  fin_cases k
  · exact alpha_rounding_0
  · exact alpha_rounding_1
  · exact alpha_rounding_2
  · exact alpha_rounding_3
  · exact alpha_rounding_4
  · exact alpha_rounding_5
  · exact alpha_rounding_6
  · exact alpha_rounding_7
  · exact alpha_rounding_8
  · exact alpha_rounding_9

def objectiveCenter : Fin 11 → ℚ := ![(197561/500000),(297661/1000000),(31473/250000),(46963/250000),(61543/50000),(608979/1000000000),(492497/1000000000),(728493/100000000000),(70343/5000000000000000),(22791/20000000000000),(764263/100000000000000000000000000000000000000000)]
def objectiveRadius : Fin 11 → ℚ := ![(1/2000000),(1/2000000),(1/2000000),(1/2000000),(1/200000),(1/2000000000),(1/2000000000),(1/200000000000),(1/20000000000000000),(1/200000000000000),(1/200000000000000000000000000000000000000000)]

theorem all_objective_rounding (k : Fin 11) :
    Rounded (objective k.val) (objectiveCenter k) (objectiveRadius k) := by
  fin_cases k
  · exact objective_rounding_0
  · exact objective_rounding_1
  · exact objective_rounding_2
  · exact objective_rounding_3
  · exact objective_rounding_4
  · exact objective_rounding_5
  · exact objective_rounding_6
  · exact objective_rounding_7
  · exact objective_rounding_8
  · exact objective_rounding_9
  · exact objective_rounding_10

def normCenter : Fin 11 → ℚ := ![(122711/125000),(77697/100000),(138531/250000),(38597/20000),(496021/100000),(175717/5000000),(156923/5000000),(76341/20000000),(167741/10000000000),(150967/1000000000),(431747/100000000000000000000000)]
def normRadius : Fin 11 → ℚ := ![(1/2000000),(1/2000000),(1/2000000),(1/200000),(1/200000),(1/20000000),(1/20000000),(1/200000000),(1/20000000000),(1/2000000000),(1/200000000000000000000000)]

theorem all_norm_rounding (k : Fin 11) :
    Rounded (gradientNorm k.val) (normCenter k) (normRadius k) := by
  fin_cases k
  · exact norm_rounding_0
  · exact norm_rounding_1
  · exact norm_rounding_2
  · exact norm_rounding_3
  · exact norm_rounding_4
  · exact norm_rounding_5
  · exact norm_rounding_6
  · exact norm_rounding_7
  · exact norm_rounding_8
  · exact norm_rounding_9
  · exact norm_rounding_10

def energyCenter : Fin 11 → ℚ := ![(2124/3125),(12727/31250),(54139/250000),(682321/100000000),(362813/100000000),(833213/1000000000),(23121/200000000),(364247/100000000000),(362847/5000000000000000000000000000),(53461/10000000000000000000000000000000000000),(131467/10000000000000000000000000000000000000000)]
def energyRadius : Fin 11 → ℚ := ![(1/2000000),(1/2000000),(1/2000000),(1/200000000),(1/200000000),(1/2000000000),(1/2000000000),(1/200000000000),(1/20000000000000000000000000000),(1/200000000000000000000000000000000000000),(1/20000000000000000000000000000000000000000)]

theorem all_energy_rounding (k : Fin 11) :
    Rounded (energy k.val) (energyCenter k) (energyRadius k) := by
  fin_cases k
  · exact energy_rounding_0
  · exact energy_rounding_1
  · exact energy_rounding_2
  · exact energy_rounding_3
  · exact energy_rounding_4
  · exact energy_rounding_5
  · exact energy_rounding_6
  · exact energy_rounding_7
  · exact energy_rounding_8
  · exact energy_rounding_9
  · exact energy_rounding_10

def energyRatioCenter : Fin 10 → ℚ := ![(749/1250),(265867/500000),(157539/5000000),(265867/500000),(229653/1000000),(69373/500000),(157539/5000000),(3113/156250000000000000000),(736687/10000000000000000),(30739/12500000)]
def energyRatioRadius : Fin 10 → ℚ := ![(1/2000000),(1/2000000),(1/20000000),(1/2000000),(1/2000000),(1/2000000),(1/20000000),(1/20000000000000000000000),(1/20000000000000000),(1/200000000)]

theorem all_energyRatio_rounding (k : Fin 10) :
    Rounded (energyRatio k.val) (energyRatioCenter k) (energyRatioRadius k) := by
  fin_cases k
  · exact energyRatio_rounding_0
  · exact energyRatio_rounding_1
  · exact energyRatio_rounding_2
  · exact energyRatio_rounding_3
  · exact energyRatio_rounding_4
  · exact energyRatio_rounding_5
  · exact energyRatio_rounding_6
  · exact energyRatio_rounding_7
  · exact energyRatio_rounding_8
  · exact energyRatio_rounding_9

theorem ratio_bounded_0 : energyRatio 0 < (81/121:ℝ) := by
  exact (energyRatio_rounding_0).2.trans (by norm_num)

theorem ratio_bounded_1 : energyRatio 1 < (81/121:ℝ) := by
  exact (energyRatio_rounding_1).2.trans (by norm_num)

theorem ratio_bounded_2 : energyRatio 2 < (81/121:ℝ) := by
  exact (energyRatio_rounding_2).2.trans (by norm_num)

theorem ratio_bounded_3 : energyRatio 3 < (81/121:ℝ) := by
  exact (energyRatio_rounding_3).2.trans (by norm_num)

theorem ratio_bounded_4 : energyRatio 4 < (81/121:ℝ) := by
  exact (energyRatio_rounding_4).2.trans (by norm_num)

theorem ratio_bounded_5 : energyRatio 5 < (81/121:ℝ) := by
  exact (energyRatio_rounding_5).2.trans (by norm_num)

theorem ratio_bounded_6 : energyRatio 6 < (81/121:ℝ) := by
  exact (energyRatio_rounding_6).2.trans (by norm_num)

theorem ratio_bounded_7 : energyRatio 7 < (81/121:ℝ) := by
  exact (energyRatio_rounding_7).2.trans (by norm_num)

theorem ratio_bounded_8 : energyRatio 8 < (81/121:ℝ) := by
  exact (energyRatio_rounding_8).2.trans (by norm_num)

theorem ratio_bounded_9 : energyRatio 9 < (81/121:ℝ) := by
  exact (energyRatio_rounding_9).2.trans (by norm_num)

theorem all_displayed_ratios_bounded (k : Fin 10) : energyRatio k.val < (81/121:ℝ) := by
  fin_cases k
  · exact ratio_bounded_0
  · exact ratio_bounded_1
  · exact ratio_bounded_2
  · exact ratio_bounded_3
  · exact ratio_bounded_4
  · exact ratio_bounded_5
  · exact ratio_bounded_6
  · exact ratio_bounded_7
  · exact ratio_bounded_8
  · exact ratio_bounded_9

theorem objective_upward_arrows : objective 2 < objective 3 ∧
    objective 3 < objective 4 ∧ objective 8 < objective 9 := by
  norm_num [objective,qObjective,qGradient,exact_state_2,exact_state_3,exact_state_4,exact_state_8,exact_state_9]

theorem objective_increase_indices (k : Fin 10) :
    objective k.val < objective (k.val+1) ↔ k.val+1=3 ∨ k.val+1=4 ∨ k.val+1=9 := by
  fin_cases k
  · norm_num [objective,qObjective,qGradient,exact_state_0,exact_state_1]
  · norm_num [objective,qObjective,qGradient,exact_state_1,exact_state_2]
  · norm_num [objective,qObjective,qGradient,exact_state_2,exact_state_3]
  · norm_num [objective,qObjective,qGradient,exact_state_3,exact_state_4]
  · norm_num [objective,qObjective,qGradient,exact_state_4,exact_state_5]
  · norm_num [objective,qObjective,qGradient,exact_state_5,exact_state_6]
  · norm_num [objective,qObjective,qGradient,exact_state_6,exact_state_7]
  · norm_num [objective,qObjective,qGradient,exact_state_7,exact_state_8]
  · norm_num [objective,qObjective,qGradient,exact_state_8,exact_state_9]
  · norm_num [objective,qObjective,qGradient,exact_state_9,exact_state_10]

theorem objective_increase_ratio_3 : Rounded (objectiveRatio 2) (149217/100000) (1/200000) := by
  norm_num [Rounded,objectiveRatio,objective,qObjective,qGradient,exact_state_2,exact_state_3]

theorem gradient_increase_ratio_3 : Rounded (gradientRatio 2) (348271/100000) (1/200000) := by
  apply powered_rounding 2 (gradientRatio_nonneg 2) (gradientRatio_sq 2)
  all_goals norm_num [qNormSq,qGradient,exact_state_2,exact_state_3]

theorem objective_increase_ratio_4 : Rounded (objectiveRatio 3) (655229/100000) (1/200000) := by
  norm_num [Rounded,objectiveRatio,objective,qObjective,qGradient,exact_state_3,exact_state_4]

theorem gradient_increase_ratio_4 : Rounded (gradientRatio 3) (10281/4000) (1/200000) := by
  apply powered_rounding 2 (gradientRatio_nonneg 3) (gradientRatio_sq 3)
  all_goals norm_num [qNormSq,qGradient,exact_state_3,exact_state_4]

theorem objective_increase_ratio_9 : Rounded (objectiveRatio 8) (202499/2500) (1/20000) := by
  norm_num [Rounded,objectiveRatio,objective,qObjective,qGradient,exact_state_8,exact_state_9]

theorem gradient_increase_ratio_9 : Rounded (gradientRatio 8) (449999/50000) (1/200000) := by
  apply powered_rounding 2 (gradientRatio_nonneg 8) (gradientRatio_sq 8)
  all_goals norm_num [qNormSq,qGradient,exact_state_8,exact_state_9]

theorem displayed_contraction_rounding : Rounded (81/121:ℝ) (669421/1000000) (1/2000000) := by
  norm_num [Rounded]

end BB.Numerical
