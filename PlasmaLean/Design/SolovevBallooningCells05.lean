/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningEvalCert

/-!
# Ballooning certificate: kernel-checked cells, part 5

52 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(1920/NT, 4096/NS)`. -/
theorem cn05_0 : cornerOK gdata (1920) (4096)
    [143983505, 104031108, 126915395, 50604329, 33137166, 5932701, 2874580] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 4096/NS)`. -/
theorem cn05_1 : cornerOK gdata (2048) (4096)
    [145458560, 104400442, 131601408, 51231873, 35156147, 6024260, 3127408] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 6144/NS)`. -/
theorem cn05_2 : cornerOK gdata (1920) (6144)
    [143983505, 104031108, 126915395, 50604329, 33137166, 5932701, 2874580] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 6144/NS)`. -/
theorem cn05_3 : cornerOK gdata (2048) (6144)
    [145458560, 104400442, 131601408, 51231873, 35156147, 6024260, 3127408] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 4096/NS)`. -/
theorem cn05_4 : cornerOK gdata (2176) (4096)
    [146076313, 104400442, 135501243, 51231873, 36976787, 6024260, 3365899] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 6144/NS)`. -/
theorem cn05_5 : cornerOK gdata (2176) (6144)
    [146076313, 104400442, 135501243, 51231873, 36976787, 6024260, 3365899] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 4096/NS)`. -/
theorem cn05_6 : cornerOK gdata (2304) (4096)
    [146076313, 103278121, 138670594, 51109971, 38622462, 6023814, 3589687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 6144/NS)`. -/
theorem cn05_7 : cornerOK gdata (2304) (6144)
    [146076313, 103278121, 138670594, 51109971, 38622462, 6023814, 3589687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2432/NT, 4096/NS)`. -/
theorem cn05_8 : cornerOK gdata (2432) (4096)
    [145952756, 100826637, 141219090, 50292013, 40099516, 5937748, 3794816] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2432/NT, 6144/NS)`. -/
theorem cn05_9 : cornerOK gdata (2432) (6144)
    [145952756, 100826637, 141219090, 50292013, 40099516, 5937748, 3794816] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 4096/NS)`. -/
theorem cn05_10 : cornerOK gdata (2560) (4096)
    [145318826, 97322313, 143225969, 48875953, 41396422, 5776625, 3983275] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 6144/NS)`. -/
theorem cn05_11 : cornerOK gdata (2560) (6144)
    [145318826, 97322313, 143225969, 48875953, 41396422, 5776625, 3983275] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2688/NT, 4096/NS)`. -/
theorem cn05_12 : cornerOK gdata (2688) (4096)
    [144275819, 92752292, 144819382, 46881566, 42499589, 5545624, 4145840] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2688/NT, 6144/NS)`. -/
theorem cn05_13 : cornerOK gdata (2688) (6144)
    [144275819, 92752292, 144819382, 46881566, 42499589, 5545624, 4145840] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 4096/NS)`. -/
theorem cn05_14 : cornerOK gdata (2816) (4096)
    [142707750, 87194754, 145708551, 44342184, 43387882, 5249458, 4284994] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 6144/NS)`. -/
theorem cn05_15 : cornerOK gdata (2816) (6144)
    [142707750, 87194754, 145708551, 44342184, 43387882, 5249458, 4284994] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 4096/NS)`. -/
theorem cn05_16 : cornerOK gdata (2944) (4096)
    [140702085, 80861183, 146077624, 41359915, 44055692, 4900188, 4399070] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 6144/NS)`. -/
theorem cn05_17 : cornerOK gdata (2944) (6144)
    [140702085, 80861183, 146077624, 41359915, 44055692, 4900188, 4399070] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 4096/NS)`. -/
theorem cn05_18 : cornerOK gdata (3072) (4096)
    [138468145, 73933842, 146077624, 38023628, 44516364, 4508737, 4488664] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 6144/NS)`. -/
theorem cn05_19 : cornerOK gdata (3072) (6144)
    [138468145, 73933842, 146077624, 38023628, 44516364, 4508737, 4488664] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3200/NT, 4096/NS)`. -/
theorem cn05_20 : cornerOK gdata (3200) (4096)
    [136062313, 66579702, 145951029, 34418985, 44797033, 4085427, 4555632] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3200/NT, 6144/NS)`. -/
theorem cn05_21 : cornerOK gdata (3200) (6144)
    [136062313, 66579702, 145951029, 34418985, 44797033, 4085427, 4555632] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 4096/NS)`. -/
theorem cn05_22 : cornerOK gdata (3328) (4096)
    [290422656, 144414364, 308660689, 71610364, 93371173, 8669452, 9073077] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 6144/NS)`. -/
theorem cn05_23 : cornerOK gdata (3328) (6144)
    [290422656, 144414364, 308660689, 71610364, 93371173, 8669452, 9073077] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 4096/NS)`. -/
theorem cn05_24 : cornerOK gdata (3584) (4096)
    [290422656, 144414364, 308660689, 71610364, 93371173, 8669452, 9073077] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 6144/NS)`. -/
theorem cn05_25 : cornerOK gdata (3584) (6144)
    [290422656, 144414364, 308660689, 71610364, 93371173, 8669452, 9073077] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 4096/NS)`. -/
theorem cn05_26 : cornerOK gdata (3840) (4096)
    [264976089, 104740110, 287848545, 52586857, 88556951, 6381819, 8740305] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 6144/NS)`. -/
theorem cn05_27 : cornerOK gdata (3840) (6144)
    [264976089, 104740110, 287848545, 52586857, 88556951, 6381819, 8740305] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 4096/NS)`. -/
theorem cn05_28 : cornerOK gdata (4096) (4096)
    [242887965, 69917053, 267851474, 35266314, 83418926, 4335353, 8333037] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 6144/NS)`. -/
theorem cn05_29 : cornerOK gdata (4096) (6144)
    [242887965, 69917053, 267851474, 35266314, 83418926, 4335353, 8333037] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 6144/NS)`. -/
theorem cn05_30 : cornerOK gdata (-4096) (6144)
    [225065881, 63588556, 160796458, 27901924, 40111826, 3403325, 3095368] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 6144/NS)`. -/
theorem cn05_31 : cornerOK gdata (-3840) (6144)
    [255641849, 93395103, 182094810, 40899081, 44738230, 4892348, 3374378] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 7168/NS)`. -/
theorem cn05_32 : cornerOK gdata (-4096) (7168)
    [275157500, 75676359, 188703969, 32717784, 46253233, 3948160, 3418741] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 7168/NS)`. -/
theorem cn05_33 : cornerOK gdata (-3840) (7168)
    [313532178, 111311475, 214591662, 48218866, 51749419, 5725528, 3737750] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 8192/NS)`. -/
theorem cn05_34 : cornerOK gdata (-4096) (8192)
    [275157500, 75676359, 188703969, 32717784, 46253233, 3948160, 3418741] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 8192/NS)`. -/
theorem cn05_35 : cornerOK gdata (-3840) (8192)
    [313532178, 111311475, 214591662, 48218866, 51749419, 5725528, 3737750] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 6144/NS)`. -/
theorem cn05_36 : cornerOK gdata (-3584) (6144)
    [291064651, 130838632, 206099967, 56156749, 49586269, 6702311, 3647999] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 7168/NS)`. -/
theorem cn05_37 : cornerOK gdata (-3584) (7168)
    [357970945, 157063832, 244034963, 66873932, 57536103, 7894459, 4055043] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 8192/NS)`. -/
theorem cn05_38 : cornerOK gdata (-3584) (8192)
    [357970945, 157063832, 244034963, 66873932, 57536103, 7894459, 4055043] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 6144/NS)`. -/
theorem cn05_39 : cornerOK gdata (-3328) (6144)
    [330602737, 178853962, 232533210, 75979019, 54576174, 9063763, 3903670] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 7168/NS)`. -/
theorem cn05_40 : cornerOK gdata (-3328) (7168)
    [407685197, 214940141, 276752188, 90766324, 63549357, 10692976, 4355241] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 8192/NS)`. -/
theorem cn05_41 : cornerOK gdata (-3328) (8192)
    [407685197, 214940141, 276752188, 90766324, 63549357, 10692976, 4355241] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 6144/NS)`. -/
theorem cn05_42 : cornerOK gdata (-3072) (6144)
    [372577716, 229293334, 260141727, 96438610, 59295966, 11500938, 4121731] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 7168/NS)`. -/
theorem cn05_43 : cornerOK gdata (-3072) (7168)
    [460422663, 275927451, 311298275, 115446852, 69298478, 13583424, 4618227] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 8192/NS)`. -/
theorem cn05_44 : cornerOK gdata (-3072) (8192)
    [460422663, 275927451, 311298275, 115446852, 69298478, 13583424, 4618227] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 6144/NS)`. -/
theorem cn05_45 : cornerOK gdata (-2816) (6144)
    [414703449, 277552058, 286619232, 115588565, 63281845, 13777889, 4282427] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 7168/NS)`. -/
theorem cn05_46 : cornerOK gdata (-2816) (7168)
    [513785507, 334827606, 345044306, 138683637, 74262893, 16303462, 4832526] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 8192/NS)`. -/
theorem cn05_47 : cornerOK gdata (-2816) (8192)
    [513785507, 334827606, 345044306, 138683637, 74262893, 16303462, 4832526] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 6144/NS)`. -/
theorem cn05_48 : cornerOK gdata (-2560) (6144)
    [547274946, 291639393, 350681840, 119602229, 79567278, 13777889, 5711629] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 7168/NS)`. -/
theorem cn05_49 : cornerOK gdata (-2560) (7168)
    [513785507, 334827606, 345044306, 138683637, 74262893, 16303462, 4832526] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 8192/NS)`. -/
theorem cn05_50 : cornerOK gdata (-2560) (8192)
    [547274946, 334827606, 350681840, 138683637, 79567278, 16303462, 5711629] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 6144/NS)`. -/
theorem cn05_51 : cornerOK gdata (-2432) (6144)
    [547274946, 293286012, 350681840, 119602229, 79567278, 13577322, 5711629] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 8192/NS)`. -/
theorem cn05_52 : cornerOK gdata (-2432) (8192)
    [547274946, 293286012, 350681840, 119602229, 79567278, 13577322, 5711629] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 6144/NS)`. -/
theorem cn05_53 : cornerOK gdata (-2304) (6144)
    [530932539, 293286012, 338497212, 119395315, 75714096, 13533815, 5291440] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 8192/NS)`. -/
theorem cn05_54 : cornerOK gdata (-2304) (8192)
    [530932539, 293286012, 338497212, 119395315, 75714096, 13533815, 5291440] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 6144/NS)`. -/
theorem cn05_55 : cornerOK gdata (-2176) (6144)
    [510173559, 290116039, 323896518, 117226302, 71377090, 13267373, 4851011] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 8192/NS)`. -/
theorem cn05_56 : cornerOK gdata (-2176) (8192)
    [510173559, 290116039, 323896518, 117226302, 71377090, 13267373, 4851011] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 6144/NS)`. -/
theorem cn05_57 : cornerOK gdata (-2048) (6144)
    [485090274, 282088327, 306999111, 113154207, 66616894, 12784757, 4400324] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 8192/NS)`. -/
theorem cn05_58 : cornerOK gdata (-2048) (8192)
    [485090274, 282088327, 306999111, 113154207, 66616894, 12784757, 4400324] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 6144/NS)`. -/
theorem cn05_59 : cornerOK gdata (-1920) (6144)
    [456100365, 269299148, 288007822, 107290559, 61496517, 12097485, 3942986] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 8192/NS)`. -/
theorem cn05_60 : cornerOK gdata (-1920) (8192)
    [456100365, 269299148, 288007822, 107290559, 61496517, 12097485, 3942986] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 6144/NS)`. -/
theorem cn05_61 : cornerOK gdata (-1792) (6144)
    [424009180, 252832755, 267314409, 100180779, 56130767, 11259252, 3490195] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 8192/NS)`. -/
theorem cn05_62 : cornerOK gdata (-1792) (8192)
    [424009180, 252832755, 267314409, 100180779, 56130767, 11259252, 3490195] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 6144/NS)`. -/
theorem cn05_63 : cornerOK gdata (-1664) (6144)
    [390424778, 235576602, 246667215, 93500371, 50784332, 10412299, 3053813] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 8192/NS)`. -/
theorem cn05_64 : cornerOK gdata (-1664) (8192)
    [390424778, 235576602, 246667215, 93500371, 50784332, 10412299, 3053813] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 6144/NS)`. -/
theorem cn05_65 : cornerOK gdata (-1536) (6144)
    [354731342, 217327049, 224726773, 86113372, 45479073, 9542949, 2641652] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 8192/NS)`. -/
theorem cn05_66 : cornerOK gdata (-1536) (8192)
    [354731342, 217327049, 224726773, 86113372, 45479073, 9542949, 2641652] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 6144/NS)`. -/
theorem cn05_67 : cornerOK gdata (-1408) (6144)
    [317825528, 199379045, 202263759, 78314141, 40198649, 8686099, 2267897] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 8192/NS)`. -/
theorem cn05_68 : cornerOK gdata (-1408) (8192)
    [317825528, 199379045, 202263759, 78314141, 40198649, 8686099, 2267897] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 6144/NS)`. -/
theorem cn05_69 : cornerOK gdata (-1280) (6144)
    [280487247, 180146114, 179240349, 70204620, 35024037, 7798873, 1942577] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 8192/NS)`. -/
theorem cn05_70 : cornerOK gdata (-1280) (8192)
    [280487247, 180146114, 179240349, 70204620, 35024037, 7798873, 1942577] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 6144/NS)`. -/
theorem cn05_71 : cornerOK gdata (-1152) (6144)
    [243864271, 160132235, 156452365, 61942198, 30060975, 6902040, 1648228] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 8192/NS)`. -/
theorem cn05_72 : cornerOK gdata (-1152) (8192)
    [243864271, 160132235, 156452365, 61942198, 30060975, 6902040, 1648228] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 6144/NS)`. -/
theorem cn05_73 : cornerOK gdata (-1024) (6144)
    [211580709, 139848740, 134391131, 53705555, 25366010, 6013419, 1383292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 8192/NS)`. -/
theorem cn05_74 : cornerOK gdata (-1024) (8192)
    [211580709, 139848740, 134391131, 53705555, 25366010, 6013419, 1383292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 6144/NS)`. -/
theorem cn05_75 : cornerOK gdata (-896) (6144)
    [181502458, 119924868, 113497676, 45716032, 21046605, 5146431, 1149139] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 8192/NS)`. -/
theorem cn05_76 : cornerOK gdata (-896) (8192)
    [181502458, 119924868, 113497676, 45716032, 21046605, 5146431, 1149139] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 6144/NS)`. -/
theorem cn05_77 : cornerOK gdata (-768) (6144)
    [513856364, 344495169, 320983347, 134632146, 60976861, 15344008, 3183540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 8192/NS)`. -/
theorem cn05_78 : cornerOK gdata (-768) (8192)
    [513856364, 344495169, 320983347, 134632146, 60976861, 15344008, 3183540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 6144/NS)`. -/
theorem cn05_79 : cornerOK gdata (-512) (6144)
    [513856364, 344495169, 320983347, 134632146, 60976861, 15344008, 3183540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 8192/NS)`. -/
theorem cn05_80 : cornerOK gdata (-512) (8192)
    [513856364, 344495169, 320983347, 134632146, 60976861, 15344008, 3183540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 6144/NS)`. -/
theorem cn05_81 : cornerOK gdata (-256) (6144)
    [366226709, 227014942, 233034005, 87790905, 45235039, 9894030, 2461402] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 8192/NS)`. -/
theorem cn05_82 : cornerOK gdata (-256) (8192)
    [366226709, 227014942, 233034005, 87790905, 45235039, 9894030, 2461402] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 6144/NS)`. -/
theorem cn05_83 : cornerOK gdata (0) (6144)
    [265060907, 165566494, 175867170, 65763858, 34856654, 7340414, 1987820] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 8192/NS)`. -/
theorem cn05_84 : cornerOK gdata (0) (8192)
    [265060907, 165566494, 175867170, 65763858, 34856654, 7340414, 1987820] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 6144/NS)`. -/
theorem cn05_85 : cornerOK gdata (256) (6144)
    [325903824, 240574679, 231109927, 94496052, 46997488, 10833498, 2792180] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 8192/NS)`. -/
theorem cn05_86 : cornerOK gdata (256) (8192)
    [325903824, 240574679, 231109927, 94496052, 46997488, 10833498, 2792180] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 6144/NS)`. -/
theorem cn05_87 : cornerOK gdata (512) (6144)
    [402238224, 311469147, 287099883, 125350396, 60910696, 14487758, 3881271] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 8192/NS)`. -/
theorem cn05_88 : cornerOK gdata (512) (8192)
    [402238224, 311469147, 287099883, 125350396, 60910696, 14487758, 3881271] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 6144/NS)`. -/
theorem cn05_89 : cornerOK gdata (768) (6144)
    [402238224, 311469147, 287099883, 125350396, 60910696, 14487758, 3881271] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 8192/NS)`. -/
theorem cn05_90 : cornerOK gdata (768) (8192)
    [402238224, 311469147, 287099883, 125350396, 60910696, 14487758, 3881271] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 6144/NS)`. -/
theorem cn05_91 : cornerOK gdata (896) (6144)
    [108895715, 80236481, 79135066, 33467826, 17827066, 3868622, 1246997] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 8192/NS)`. -/
theorem cn05_92 : cornerOK gdata (896) (8192)
    [108895715, 80236481, 79135066, 33467826, 17827066, 3868622, 1246997] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 6144/NS)`. -/
theorem cn05_93 : cornerOK gdata (1024) (6144)
    [116458037, 86117483, 87614884, 37028003, 20148570, 4259212, 1439020] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 8192/NS)`. -/
theorem cn05_94 : cornerOK gdata (1024) (8192)
    [116458037, 86117483, 87614884, 37028003, 20148570, 4259212, 1439020] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 6144/NS)`. -/
theorem cn05_95 : cornerOK gdata (1152) (6144)
    [123616278, 91119326, 95928974, 40303542, 22468330, 4614220, 1636866] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 8192/NS)`. -/
theorem cn05_96 : cornerOK gdata (1152) (8192)
    [123616278, 91119326, 95928974, 40303542, 22468330, 4614220, 1636866] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 6144/NS)`. -/
theorem cn05_97 : cornerOK gdata (1280) (6144)
    [533739999, 421938312, 433902404, 187577208, 102732224, 21424961, 7568812] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 8192/NS)`. -/
theorem cn05_98 : cornerOK gdata (1280) (8192)
    [533739999, 421938312, 433902404, 187577208, 102732224, 21424961, 7568812] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 6144/NS)`. -/
theorem cn05_99 : cornerOK gdata (1536) (6144)
    [533739999, 433017337, 454542236, 197168158, 111923751, 22965449, 8694887] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 8192/NS)`. -/
theorem cn05_100 : cornerOK gdata (1536) (8192)
    [533739999, 433017337, 454542236, 197168158, 111923751, 22965449, 8694887] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 6144/NS)`. -/
theorem cn05_101 : cornerOK gdata (1792) (6144)
    [533143832, 433017337, 454542236, 197168158, 111923751, 22965449, 8694887] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 8192/NS)`. -/
theorem cn05_102 : cornerOK gdata (1792) (8192)
    [533143832, 433017337, 454542236, 197168158, 111923751, 22965449, 8694887] = true := by
  bl_cert

/-- Kernel-checked box `[1920, 2048]/NT × [4096, 6144]/NS`. -/
theorem cov258 : Cover gdata (1920) (2048) (4096) (6144) := by
  ballooning_cover "Q:cn05_0,cn05_1,cn05_2,cn05_3"

/-- Kernel-checked box `[2048, 2176]/NT × [4096, 6144]/NS`. -/
theorem cov259 : Cover gdata (2048) (2176) (4096) (6144) := by
  ballooning_cover "Q:cn05_1,cn05_4,cn05_3,cn05_5"

/-- Kernel-checked box `[2176, 2304]/NT × [4096, 6144]/NS`. -/
theorem cov260 : Cover gdata (2176) (2304) (4096) (6144) := by
  ballooning_cover "Q:cn05_4,cn05_6,cn05_5,cn05_7"

/-- Kernel-checked box `[2304, 2432]/NT × [4096, 6144]/NS`. -/
theorem cov261 : Cover gdata (2304) (2432) (4096) (6144) := by
  ballooning_cover "Q:cn05_6,cn05_8,cn05_7,cn05_9"

/-- Kernel-checked box `[2432, 2560]/NT × [4096, 6144]/NS`. -/
theorem cov262 : Cover gdata (2432) (2560) (4096) (6144) := by
  ballooning_cover "Q:cn05_8,cn05_10,cn05_9,cn05_11"

/-- Kernel-checked box `[2560, 2688]/NT × [4096, 6144]/NS`. -/
theorem cov263 : Cover gdata (2560) (2688) (4096) (6144) := by
  ballooning_cover "Q:cn05_10,cn05_12,cn05_11,cn05_13"

/-- Kernel-checked box `[2688, 2816]/NT × [4096, 6144]/NS`. -/
theorem cov264 : Cover gdata (2688) (2816) (4096) (6144) := by
  ballooning_cover "Q:cn05_12,cn05_14,cn05_13,cn05_15"

/-- Kernel-checked box `[2816, 2944]/NT × [4096, 6144]/NS`. -/
theorem cov265 : Cover gdata (2816) (2944) (4096) (6144) := by
  ballooning_cover "Q:cn05_14,cn05_16,cn05_15,cn05_17"

/-- Kernel-checked box `[2944, 3072]/NT × [4096, 6144]/NS`. -/
theorem cov266 : Cover gdata (2944) (3072) (4096) (6144) := by
  ballooning_cover "Q:cn05_16,cn05_18,cn05_17,cn05_19"

/-- Kernel-checked box `[3072, 3200]/NT × [4096, 6144]/NS`. -/
theorem cov267 : Cover gdata (3072) (3200) (4096) (6144) := by
  ballooning_cover "Q:cn05_18,cn05_20,cn05_19,cn05_21"

/-- Kernel-checked box `[3200, 3328]/NT × [4096, 6144]/NS`. -/
theorem cov268 : Cover gdata (3200) (3328) (4096) (6144) := by
  ballooning_cover "Q:cn05_20,cn05_22,cn05_21,cn05_23"

/-- Kernel-checked box `[3328, 3584]/NT × [4096, 6144]/NS`. -/
theorem cov269 : Cover gdata (3328) (3584) (4096) (6144) := by
  ballooning_cover "Q:cn05_22,cn05_24,cn05_23,cn05_25"

/-- Kernel-checked box `[3584, 3840]/NT × [4096, 6144]/NS`. -/
theorem cov270 : Cover gdata (3584) (3840) (4096) (6144) := by
  ballooning_cover "Q:cn05_24,cn05_26,cn05_25,cn05_27"

/-- Kernel-checked box `[3840, 4096]/NT × [4096, 6144]/NS`. -/
theorem cov271 : Cover gdata (3840) (4096) (4096) (6144) := by
  ballooning_cover "Q:cn05_26,cn05_28,cn05_27,cn05_29"

/-- Kernel-checked box `[-4096, -3840]/NT × [6144, 7168]/NS`. -/
theorem cov272 : Cover gdata (-4096) (-3840) (6144) (7168) := by
  ballooning_cover "Q:cn05_30,cn05_31,cn05_32,cn05_33"

/-- Kernel-checked box `[-4096, -3840]/NT × [7168, 8192]/NS`. -/
theorem cov273 : Cover gdata (-4096) (-3840) (7168) (8192) := by
  ballooning_cover "Q:cn05_32,cn05_33,cn05_34,cn05_35"

/-- Kernel-checked box `[-3840, -3584]/NT × [6144, 7168]/NS`. -/
theorem cov274 : Cover gdata (-3840) (-3584) (6144) (7168) := by
  ballooning_cover "Q:cn05_31,cn05_36,cn05_33,cn05_37"

/-- Kernel-checked box `[-3840, -3584]/NT × [7168, 8192]/NS`. -/
theorem cov275 : Cover gdata (-3840) (-3584) (7168) (8192) := by
  ballooning_cover "Q:cn05_33,cn05_37,cn05_35,cn05_38"

/-- Kernel-checked box `[-3584, -3328]/NT × [6144, 7168]/NS`. -/
theorem cov276 : Cover gdata (-3584) (-3328) (6144) (7168) := by
  ballooning_cover "Q:cn05_36,cn05_39,cn05_37,cn05_40"

/-- Kernel-checked box `[-3584, -3328]/NT × [7168, 8192]/NS`. -/
theorem cov277 : Cover gdata (-3584) (-3328) (7168) (8192) := by
  ballooning_cover "Q:cn05_37,cn05_40,cn05_38,cn05_41"

/-- Kernel-checked box `[-3328, -3072]/NT × [6144, 7168]/NS`. -/
theorem cov278 : Cover gdata (-3328) (-3072) (6144) (7168) := by
  ballooning_cover "Q:cn05_39,cn05_42,cn05_40,cn05_43"

/-- Kernel-checked box `[-3328, -3072]/NT × [7168, 8192]/NS`. -/
theorem cov279 : Cover gdata (-3328) (-3072) (7168) (8192) := by
  ballooning_cover "Q:cn05_40,cn05_43,cn05_41,cn05_44"

/-- Kernel-checked box `[-3072, -2816]/NT × [6144, 7168]/NS`. -/
theorem cov280 : Cover gdata (-3072) (-2816) (6144) (7168) := by
  ballooning_cover "Q:cn05_42,cn05_45,cn05_43,cn05_46"

/-- Kernel-checked box `[-3072, -2816]/NT × [7168, 8192]/NS`. -/
theorem cov281 : Cover gdata (-3072) (-2816) (7168) (8192) := by
  ballooning_cover "Q:cn05_43,cn05_46,cn05_44,cn05_47"

/-- Kernel-checked box `[-2816, -2560]/NT × [6144, 7168]/NS`. -/
theorem cov282 : Cover gdata (-2816) (-2560) (6144) (7168) := by
  ballooning_cover "Q:cn05_45,cn05_48,cn05_46,cn05_49"

/-- Kernel-checked box `[-2816, -2560]/NT × [7168, 8192]/NS`. -/
theorem cov283 : Cover gdata (-2816) (-2560) (7168) (8192) := by
  ballooning_cover "Q:cn05_46,cn05_49,cn05_47,cn05_50"

/-- Kernel-checked box `[-2560, -2432]/NT × [6144, 8192]/NS`. -/
theorem cov284 : Cover gdata (-2560) (-2432) (6144) (8192) := by
  ballooning_cover "Q:cn05_48,cn05_51,cn05_50,cn05_52"

/-- Kernel-checked box `[-2432, -2304]/NT × [6144, 8192]/NS`. -/
theorem cov285 : Cover gdata (-2432) (-2304) (6144) (8192) := by
  ballooning_cover "Q:cn05_51,cn05_53,cn05_52,cn05_54"

/-- Kernel-checked box `[-2304, -2176]/NT × [6144, 8192]/NS`. -/
theorem cov286 : Cover gdata (-2304) (-2176) (6144) (8192) := by
  ballooning_cover "Q:cn05_53,cn05_55,cn05_54,cn05_56"

/-- Kernel-checked box `[-2176, -2048]/NT × [6144, 8192]/NS`. -/
theorem cov287 : Cover gdata (-2176) (-2048) (6144) (8192) := by
  ballooning_cover "Q:cn05_55,cn05_57,cn05_56,cn05_58"

/-- Kernel-checked box `[-2048, -1920]/NT × [6144, 8192]/NS`. -/
theorem cov288 : Cover gdata (-2048) (-1920) (6144) (8192) := by
  ballooning_cover "Q:cn05_57,cn05_59,cn05_58,cn05_60"

/-- Kernel-checked box `[-1920, -1792]/NT × [6144, 8192]/NS`. -/
theorem cov289 : Cover gdata (-1920) (-1792) (6144) (8192) := by
  ballooning_cover "Q:cn05_59,cn05_61,cn05_60,cn05_62"

/-- Kernel-checked box `[-1792, -1664]/NT × [6144, 8192]/NS`. -/
theorem cov290 : Cover gdata (-1792) (-1664) (6144) (8192) := by
  ballooning_cover "Q:cn05_61,cn05_63,cn05_62,cn05_64"

/-- Kernel-checked box `[-1664, -1536]/NT × [6144, 8192]/NS`. -/
theorem cov291 : Cover gdata (-1664) (-1536) (6144) (8192) := by
  ballooning_cover "Q:cn05_63,cn05_65,cn05_64,cn05_66"

/-- Kernel-checked box `[-1536, -1408]/NT × [6144, 8192]/NS`. -/
theorem cov292 : Cover gdata (-1536) (-1408) (6144) (8192) := by
  ballooning_cover "Q:cn05_65,cn05_67,cn05_66,cn05_68"

/-- Kernel-checked box `[-1408, -1280]/NT × [6144, 8192]/NS`. -/
theorem cov293 : Cover gdata (-1408) (-1280) (6144) (8192) := by
  ballooning_cover "Q:cn05_67,cn05_69,cn05_68,cn05_70"

/-- Kernel-checked box `[-1280, -1152]/NT × [6144, 8192]/NS`. -/
theorem cov294 : Cover gdata (-1280) (-1152) (6144) (8192) := by
  ballooning_cover "Q:cn05_69,cn05_71,cn05_70,cn05_72"

/-- Kernel-checked box `[-1152, -1024]/NT × [6144, 8192]/NS`. -/
theorem cov295 : Cover gdata (-1152) (-1024) (6144) (8192) := by
  ballooning_cover "Q:cn05_71,cn05_73,cn05_72,cn05_74"

/-- Kernel-checked box `[-1024, -896]/NT × [6144, 8192]/NS`. -/
theorem cov296 : Cover gdata (-1024) (-896) (6144) (8192) := by
  ballooning_cover "Q:cn05_73,cn05_75,cn05_74,cn05_76"

/-- Kernel-checked box `[-896, -768]/NT × [6144, 8192]/NS`. -/
theorem cov297 : Cover gdata (-896) (-768) (6144) (8192) := by
  ballooning_cover "Q:cn05_75,cn05_77,cn05_76,cn05_78"

/-- Kernel-checked box `[-768, -512]/NT × [6144, 8192]/NS`. -/
theorem cov298 : Cover gdata (-768) (-512) (6144) (8192) := by
  ballooning_cover "Q:cn05_77,cn05_79,cn05_78,cn05_80"

/-- Kernel-checked box `[-512, -256]/NT × [6144, 8192]/NS`. -/
theorem cov299 : Cover gdata (-512) (-256) (6144) (8192) := by
  ballooning_cover "Q:cn05_79,cn05_81,cn05_80,cn05_82"

/-- Kernel-checked box `[-256, 0]/NT × [6144, 8192]/NS`. -/
theorem cov300 : Cover gdata (-256) (0) (6144) (8192) := by
  ballooning_cover "Q:cn05_81,cn05_83,cn05_82,cn05_84"

/-- Kernel-checked box `[0, 256]/NT × [6144, 8192]/NS`. -/
theorem cov301 : Cover gdata (0) (256) (6144) (8192) := by
  ballooning_cover "Q:cn05_83,cn05_85,cn05_84,cn05_86"

/-- Kernel-checked box `[256, 512]/NT × [6144, 8192]/NS`. -/
theorem cov302 : Cover gdata (256) (512) (6144) (8192) := by
  ballooning_cover "Q:cn05_85,cn05_87,cn05_86,cn05_88"

/-- Kernel-checked box `[512, 768]/NT × [6144, 8192]/NS`. -/
theorem cov303 : Cover gdata (512) (768) (6144) (8192) := by
  ballooning_cover "Q:cn05_87,cn05_89,cn05_88,cn05_90"

/-- Kernel-checked box `[768, 896]/NT × [6144, 8192]/NS`. -/
theorem cov304 : Cover gdata (768) (896) (6144) (8192) := by
  ballooning_cover "Q:cn05_89,cn05_91,cn05_90,cn05_92"

/-- Kernel-checked box `[896, 1024]/NT × [6144, 8192]/NS`. -/
theorem cov305 : Cover gdata (896) (1024) (6144) (8192) := by
  ballooning_cover "Q:cn05_91,cn05_93,cn05_92,cn05_94"

/-- Kernel-checked box `[1024, 1152]/NT × [6144, 8192]/NS`. -/
theorem cov306 : Cover gdata (1024) (1152) (6144) (8192) := by
  ballooning_cover "Q:cn05_93,cn05_95,cn05_94,cn05_96"

/-- Kernel-checked box `[1152, 1280]/NT × [6144, 8192]/NS`. -/
theorem cov307 : Cover gdata (1152) (1280) (6144) (8192) := by
  ballooning_cover "Q:cn05_95,cn05_97,cn05_96,cn05_98"

/-- Kernel-checked box `[1280, 1536]/NT × [6144, 8192]/NS`. -/
theorem cov308 : Cover gdata (1280) (1536) (6144) (8192) := by
  ballooning_cover "Q:cn05_97,cn05_99,cn05_98,cn05_100"

/-- Kernel-checked box `[1536, 1792]/NT × [6144, 8192]/NS`. -/
theorem cov309 : Cover gdata (1536) (1792) (6144) (8192) := by
  ballooning_cover "Q:cn05_99,cn05_101,cn05_100,cn05_102"

end PlasmaLean.Design.SolovevBallooning
