import BernoulliRegular.BernoulliFast.Tactic

/-!
# Concrete Bernoulli values up to `B₁₀₀`

This file caches `bernoulli 0` and the even-indexed rational values through
`bernoulli 100` as `simp` theorems, proved by the certified
`bernoulli_decide` evaluator.
-/

namespace BernoulliRegular.BernoulliFast

@[simp] theorem bernoulli_0 : bernoulli 0 = (1 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_2 : bernoulli 2 = (1 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_4 : bernoulli 4 = (-1 / 30 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_6 : bernoulli 6 = (1 / 42 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_8 : bernoulli 8 = (-1 / 30 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_10 : bernoulli 10 = (5 / 66 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_12 : bernoulli 12 = (-691 / 2730 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_14 : bernoulli 14 = (7 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_16 : bernoulli 16 = (-3617 / 510 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_18 : bernoulli 18 = (43867 / 798 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_20 : bernoulli 20 = (-174611 / 330 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_22 : bernoulli 22 = (854513 / 138 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_24 : bernoulli 24 = (-236364091 / 2730 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_26 : bernoulli 26 = (8553103 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_28 : bernoulli 28 = (-23749461029 / 870 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_30 : bernoulli 30 = (8615841276005 / 14322 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_32 : bernoulli 32 = (-7709321041217 / 510 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_34 : bernoulli 34 = (2577687858367 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_36 : bernoulli 36 =
    (-26315271553053477373 / 1919190 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_38 : bernoulli 38 = (2929993913841559 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_40 : bernoulli 40 =
    (-261082718496449122051 / 13530 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_42 : bernoulli 42 =
    (1520097643918070802691 / 1806 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_44 : bernoulli 44 =
    (-27833269579301024235023 / 690 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_46 : bernoulli 46 =
    (596451111593912163277961 / 282 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_48 : bernoulli 48 =
    (-5609403368997817686249127547 / 46410 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_50 : bernoulli 50 =
    (495057205241079648212477525 / 66 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_52 : bernoulli 52 =
    (-801165718135489957347924991853 / 1590 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_54 : bernoulli 54 =
    (29149963634884862421418123812691 / 798 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_56 : bernoulli 56 =
    (-2479392929313226753685415739663229 / 870 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_58 : bernoulli 58 =
    (84483613348880041862046775994036021 / 354 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_60 : bernoulli 60 =
    (-1215233140483755572040304994079820246041491 / 56786730 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_62 : bernoulli 62 =
    (12300585434086858541953039857403386151 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_64 : bernoulli 64 =
    (-106783830147866529886385444979142647942017 / 510 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_66 : bernoulli 66 =
    (1472600022126335654051619428551932342241899101 / 64722 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_68 : bernoulli 68 =
    (-78773130858718728141909149208474606244347001 / 30 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_70 : bernoulli 70 =
    (1505381347333367003803076567377857208511438160235 / 4686 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_72 : bernoulli 72 =
    (-5827954961669944110438277244641067365282488301844260429 / 140100870 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_74 : bernoulli 74 =
    (34152417289221168014330073731472635186688307783087 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_76 : bernoulli 76 =
    (-24655088825935372707687196040585199904365267828865801 / 30 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_78 : bernoulli 78 =
    (414846365575400828295179035549542073492199375372400483487 / 3318 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_80 : bernoulli 80 =
    (-4603784299479457646935574969019046849794257872751288919656867 / 230010 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_82 : bernoulli 82 =
    (1677014149185145836823154509786269900207736027570253414881613 / 498 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_84 : bernoulli 84 =
    (-2024576195935290360231131160111731009989917391198090877281083932477 /
      3404310 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_86 : bernoulli 86 =
    (660714619417678653573847847426261496277830686653388931761996983 / 6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_88 : bernoulli 88 =
    (-1311426488674017507995511424019311843345750275572028644296919890574047 /
      61410 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_90 : bernoulli 90 =
    (1179057279021082799884123351249215083775254949669647116231545215727922535 /
      272118 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_92 : bernoulli 92 =
    (-1295585948207537527989427828538576749659341483719435143023316326829946247 /
      1410 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_94 : bernoulli 94 =
    (1220813806579744469607301679413201203958508415202696621436215105284649447 /
      6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_96 : bernoulli 96 =
    (-211600449597266513097597728109824233673043954389060234150638733420050668349987259 /
      4501770 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_98 : bernoulli 98 =
    (67908260672905495624051117546403605607342195728504487509073961249992947058239 /
      6 : ℚ) := by
  bernoulli_decide

@[simp] theorem bernoulli_100 : bernoulli 100 =
    (-94598037819122125295227433069493721872702841533066936133385696204311395415197247711 /
      33330 : ℚ) := by
  bernoulli_decide

end BernoulliRegular.BernoulliFast
