/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 6

51 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (evaluation certificate `ballooning_box`: one kernel leaf per ball
operation) and refers to its corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(1792/NT, 6144/NS)`. -/
theorem cn06_0 : cornerOK gdata (1792) (6144)
    [512281934, 433921429, 459118020, 200039207, 117463815, 23698461, 9564081] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 6144/NS)`. -/
theorem cn06_1 : cornerOK gdata (2048) (6144)
    [512281934, 433921429, 459118020, 200039207, 119356006, 23698461, 10133907] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 8192/NS)`. -/
theorem cn06_2 : cornerOK gdata (1792) (8192)
    [512281934, 433921429, 459118020, 200039207, 117463815, 23698461, 9564081] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 8192/NS)`. -/
theorem cn06_3 : cornerOK gdata (2048) (8192)
    [512281934, 433921429, 459118020, 200039207, 119356006, 23698461, 10133907] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 6144/NS)`. -/
theorem cn06_4 : cornerOK gdata (2304) (6144)
    [477376812, 410214066, 447644147, 191634497, 119356006, 22935599, 10453853] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 8192/NS)`. -/
theorem cn06_5 : cornerOK gdata (2304) (8192)
    [477376812, 410214066, 447644147, 191634497, 119356006, 22935599, 10453853] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 6144/NS)`. -/
theorem cn06_6 : cornerOK gdata (2560) (6144)
    [435447060, 368564753, 426116499, 174515264, 118243992, 21008787, 10575687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 8192/NS)`. -/
theorem cn06_7 : cornerOK gdata (2560) (8192)
    [435447060, 368564753, 426116499, 174515264, 118243992, 21008787, 10575687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 6144/NS)`. -/
theorem cn06_8 : cornerOK gdata (2816) (6144)
    [393788832, 317212457, 401484902, 152228666, 115410291, 18386766, 10575687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 8192/NS)`. -/
theorem cn06_9 : cornerOK gdata (2816) (8192)
    [393788832, 317212457, 401484902, 152228666, 115410291, 18386766, 10575687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 6144/NS)`. -/
theorem cn06_10 : cornerOK gdata (3072) (6144)
    [353033072, 260668009, 375534613, 126787525, 111376352, 15346535, 10485411] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 8192/NS)`. -/
theorem cn06_11 : cornerOK gdata (3072) (8192)
    [353033072, 260668009, 375534613, 126787525, 111376352, 15346535, 10485411] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 6144/NS)`. -/
theorem cn06_12 : cornerOK gdata (3328) (6144)
    [315512243, 204221047, 348228785, 100693674, 106206713, 12211017, 10232046] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 8192/NS)`. -/
theorem cn06_13 : cornerOK gdata (3328) (8192)
    [315512243, 204221047, 348228785, 100693674, 106206713, 12211017, 10232046] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 6144/NS)`. -/
theorem cn06_14 : cornerOK gdata (3584) (6144)
    [282481627, 155195109, 321760458, 77587717, 100459406, 9413622, 9861943] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 8192/NS)`. -/
theorem cn06_15 : cornerOK gdata (3584) (8192)
    [282481627, 155195109, 321760458, 77587717, 100459406, 9413622, 9861943] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 6144/NS)`. -/
theorem cn06_16 : cornerOK gdata (3840) (6144)
    [254206942, 111290105, 296609975, 56451737, 94355294, 6858555, 9407091] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 8192/NS)`. -/
theorem cn06_17 : cornerOK gdata (3840) (8192)
    [254206942, 111290105, 296609975, 56451737, 94355294, 6858555, 9407091] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 6144/NS)`. -/
theorem cn06_18 : cornerOK gdata (4096) (6144)
    [230326821, 73731705, 273190137, 37784979, 88163740, 4655198, 8898572] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 8192/NS)`. -/
theorem cn06_19 : cornerOK gdata (4096) (8192)
    [230326821, 73731705, 273190137, 37784979, 88163740, 4655198, 8898572] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 8192/NS)`. -/
theorem cn06_20 : cornerOK gdata (-4096) (8192)
    [336704740, 89872105, 221678615, 38298175, 53290700, 4575697, 3782461] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 8192/NS)`. -/
theorem cn06_21 : cornerOK gdata (-3840) (8192)
    [384757947, 132370807, 253086051, 56771300, 59801516, 6697648, 4147937] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 9216/NS)`. -/
theorem cn06_22 : cornerOK gdata (-4096) (9216)
    [412648668, 106660341, 260984956, 44795853, 61421046, 5303742, 4217959] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 9216/NS)`. -/
theorem cn06_23 : cornerOK gdata (-3840) (9216)
    [472636738, 157378811, 299026226, 66808654, 69103617, 7838251, 4630122] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 10240/NS)`. -/
theorem cn06_24 : cornerOK gdata (-4096) (10240)
    [506696680, 126562897, 308178166, 52386147, 70882623, 6153758, 4710973] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 10240/NS)`. -/
theorem cn06_25 : cornerOK gdata (-3840) (10240)
    [581856957, 187240069, 354495792, 78652463, 79985371, 9187051, 5180498] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 11264/NS)`. -/
theorem cn06_26 : cornerOK gdata (-4096) (11264)
    [624483252, 150567849, 365225355, 61264540, 81940657, 7150428, 5262698] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 11264/NS)`. -/
theorem cn06_27 : cornerOK gdata (-3840) (11264)
    [719203596, 223632229, 421758582, 92626109, 92742311, 10787196, 5797642] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 12288/NS)`. -/
theorem cn06_28 : cornerOK gdata (-4096) (12288)
    [624483252, 150567849, 365225355, 61264540, 81940657, 7150428, 5262698] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 12288/NS)`. -/
theorem cn06_29 : cornerOK gdata (-3840) (12288)
    [719203596, 223632229, 421758582, 92626109, 92742311, 10787196, 5797642] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 8192/NS)`. -/
theorem cn06_30 : cornerOK gdata (-3584) (8192)
    [440594637, 188006013, 289257418, 79491135, 66723028, 9295315, 4513783] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 9216/NS)`. -/
theorem cn06_31 : cornerOK gdata (-3584) (9216)
    [542680034, 224849251, 343439159, 94382361, 77368823, 10948591, 5043943] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 10240/NS)`. -/
theorem cn06_32 : cornerOK gdata (-3584) (10240)
    [669678108, 269074993, 409089143, 112054167, 89854931, 12916443, 5652315] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 11264/NS)`. -/
theorem cn06_33 : cornerOK gdata (-3584) (11264)
    [830023422, 323168112, 489033176, 133012731, 104563980, 15267716, 6336299] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 12288/NS)`. -/
theorem cn06_34 : cornerOK gdata (-3584) (12288)
    [830023422, 323168112, 489033176, 133012731, 104563980, 15267716, 6336299] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 8192/NS)`. -/
theorem cn06_35 : cornerOK gdata (-3328) (8192)
    [503004195, 257726391, 329807392, 108243584, 73961117, 12606489, 4863015] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 9216/NS)`. -/
theorem cn06_36 : cornerOK gdata (-3328) (9216)
    [621128067, 308666485, 393763795, 128914676, 86104260, 14868778, 5440292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 10240/NS)`. -/
theorem cn06_37 : cornerOK gdata (-3328) (10240)
    [768216962, 308666485, 425856477, 128914676, 97900551, 14868778, 6905372] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 11264/NS)`. -/
theorem cn06_38 : cornerOK gdata (-3328) (11264)
    [830023422, 323168112, 489033176, 133012731, 104563980, 15267716, 6336299] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 12288/NS)`. -/
theorem cn06_39 : cornerOK gdata (-3328) (12288)
    [830023422, 323168112, 489033176, 133012731, 104563980, 15267716, 6905372] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 8192/NS)`. -/
theorem cn06_40 : cornerOK gdata (-3072) (8192)
    [529490258, 257726391, 329807392, 108243584, 73961117, 12606489, 5404888] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 9216/NS)`. -/
theorem cn06_41 : cornerOK gdata (-3072) (9216)
    [621128067, 308666485, 393763795, 128914676, 86104260, 14868778, 5440292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 10240/NS)`. -/
theorem cn06_42 : cornerOK gdata (-3072) (10240)
    [756627124, 308666485, 416705326, 128914676, 94412684, 14868778, 6483579] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 10240/NS)`. -/
theorem cn06_43 : cornerOK gdata (-3264) (10240)
    [768216962, 206640206, 425856477, 80231926, 97900551, 8959218, 6905372] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 12288/NS)`. -/
theorem cn06_44 : cornerOK gdata (-3264) (12288)
    [768216962, 206640206, 425856477, 80231926, 97900551, 8959218, 6905372] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 10240/NS)`. -/
theorem cn06_45 : cornerOK gdata (-3200) (10240)
    [765601566, 217782245, 423490002, 84329938, 96911904, 9405461, 6779165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 12288/NS)`. -/
theorem cn06_46 : cornerOK gdata (-3200) (12288)
    [765601566, 217782245, 423490002, 84329938, 96911904, 9405461, 6779165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 10240/NS)`. -/
theorem cn06_47 : cornerOK gdata (-3136) (10240)
    [761670166, 228187247, 420397082, 88096647, 95739397, 9815494, 6637534] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 12288/NS)`. -/
theorem cn06_48 : cornerOK gdata (-3136) (12288)
    [761670166, 228187247, 420397082, 88096647, 95739397, 9815494, 6637534] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 12288/NS)`. -/
theorem cn06_49 : cornerOK gdata (-3072) (12288)
    [756627124, 237785467, 416705326, 91498244, 94412684, 10184799, 6483579] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 8192/NS)`. -/
theorem cn06_50 : cornerOK gdata (-3008) (8192)
    [529490258, 186471967, 311185353, 74903513, 73516628, 8340238, 5404888] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 10240/NS)`. -/
theorem cn06_51 : cornerOK gdata (-3008) (10240)
    [750705461, 246450257, 412555004, 94495009, 92964346, 10510360, 6320731] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 12288/NS)`. -/
theorem cn06_52 : cornerOK gdata (-3008) (12288)
    [750705461, 246450257, 412555004, 94495009, 92964346, 10510360, 6320731] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 8192/NS)`. -/
theorem cn06_53 : cornerOK gdata (-2944) (8192)
    [525152850, 192754890, 307735970, 77118556, 72316996, 8582057, 5272775] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 10240/NS)`. -/
theorem cn06_54 : cornerOK gdata (-2944) (10240)
    [743342904, 253981816, 407648406, 97018145, 91335938, 10785079, 6144889] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 12288/NS)`. -/
theorem cn06_55 : cornerOK gdata (-2944) (12288)
    [743342904, 253981816, 407648406, 97018145, 91335938, 10785079, 6144889] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 8192/NS)`. -/
theorem cn06_56 : cornerOK gdata (-2880) (8192)
    [519839685, 198140191, 303749885, 78934902, 70980533, 8781024, 5134854] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 10240/NS)`. -/
theorem cn06_57 : cornerOK gdata (-2880) (10240)
    [734310960, 260578444, 401855251, 99139989, 89508536, 11015006, 5955811] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 12288/NS)`. -/
theorem cn06_58 : cornerOK gdata (-2880) (12288)
    [734310960, 260578444, 401855251, 99139989, 89508536, 11015006, 5955811] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 8192/NS)`. -/
theorem cn06_59 : cornerOK gdata (-2816) (8192)
    [513226057, 202886103, 299016188, 80460892, 69468982, 8948147, 4984224] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 10240/NS)`. -/
theorem cn06_60 : cornerOK gdata (-2816) (10240)
    [724515321, 265951373, 395759789, 100765174, 87612762, 11192146, 5762413] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 12288/NS)`. -/
theorem cn06_61 : cornerOK gdata (-2816) (12288)
    [724515321, 265951373, 395759789, 100765174, 87612762, 11192146, 5762413] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 8192/NS)`. -/
theorem cn06_62 : cornerOK gdata (-2752) (8192)
    [506024464, 206756924, 294046229, 81601316, 67892662, 9072973, 4830801] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 10240/NS)`. -/
theorem cn06_63 : cornerOK gdata (-2752) (10240)
    [712863006, 270180251, 388727187, 101923217, 85516151, 11317977, 5557017] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 12288/NS)`. -/
theorem cn06_64 : cornerOK gdata (-2752) (12288)
    [712863006, 270180251, 388727187, 101923217, 85516151, 11317977, 5557017] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 8192/NS)`. -/
theorem cn06_65 : cornerOK gdata (-2688) (8192)
    [498033426, 209715824, 288672157, 82351293, 66229055, 9155804, 4667765] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 10240/NS)`. -/
theorem cn06_66 : cornerOK gdata (-2688) (10240)
    [700021772, 273086716, 381161695, 102559504, 83304819, 11388080, 5353486] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 12288/NS)`. -/
theorem cn06_67 : cornerOK gdata (-2688) (12288)
    [700021772, 273086716, 381161695, 102559504, 83304819, 11388080, 5353486] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2624/NT, 8192/NS)`. -/
theorem cn06_68 : cornerOK gdata (-2624) (8192)
    [488879711, 211736311, 282706383, 82709321, 64432507, 9196877, 4498105] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2624/NT, 10240/NS)`. -/
theorem cn06_69 : cornerOK gdata (-2624) (10240)
    [685438008, 274637344, 372740963, 102674772, 80935917, 11402134, 5151370] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2624/NT, 12288/NS)`. -/
theorem cn06_70 : cornerOK gdata (-2624) (12288)
    [685438008, 274637344, 372740963, 102674772, 80935917, 11402134, 5151370] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 8192/NS)`. -/
theorem cn06_71 : cornerOK gdata (-2560) (8192)
    [768612071, 381200915, 463679149, 152333445, 100568162, 17219991, 6640241] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 10240/NS)`. -/
theorem cn06_72 : cornerOK gdata (-2560) (10240)
    [768612071, 381200915, 463679149, 152333445, 100568162, 17219991, 6640241] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 12288/NS)`. -/
theorem cn06_73 : cornerOK gdata (-2560) (12288)
    [669110401, 274848114, 363508205, 102674772, 78455098, 11402134, 4942526] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 8192/NS)`. -/
theorem cn06_74 : cornerOK gdata (-2432) (8192)
    [768612071, 381321689, 463679149, 152333445, 100568162, 17219991, 6640241] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 10240/NS)`. -/
theorem cn06_75 : cornerOK gdata (-2432) (10240)
    [768612071, 381321689, 463679149, 152333445, 100568162, 17219991, 6640241] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2496/NT, 10240/NS)`. -/
theorem cn06_76 : cornerOK gdata (-2496) (10240)
    [650985628, 274848114, 353444099, 102288680, 75816236, 11362895, 4729339] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2496/NT, 12288/NS)`. -/
theorem cn06_77 : cornerOK gdata (-2496) (12288)
    [650985628, 274848114, 353444099, 102288680, 75816236, 11362895, 4729339] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 12288/NS)`. -/
theorem cn06_78 : cornerOK gdata (-2432) (12288)
    [631988705, 273835377, 343024378, 101435674, 73119466, 11271771, 4511673] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 8192/NS)`. -/
theorem cn06_79 : cornerOK gdata (-2304) (8192)
    [740919754, 381321689, 445481254, 151292546, 95368791, 17074827, 6140009] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 10240/NS)`. -/
theorem cn06_80 : cornerOK gdata (-2304) (10240)
    [990539448, 489144166, 565711979, 188028086, 113788612, 21086141, 6541510] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2368/NT, 10240/NS)`. -/
theorem cn06_81 : cornerOK gdata (-2368) (10240)
    [611414053, 271366359, 331678705, 100066107, 70258625, 11126659, 4290311] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2368/NT, 12288/NS)`. -/
theorem cn06_82 : cornerOK gdata (-2368) (12288)
    [611414053, 271366359, 331678705, 100066107, 70258625, 11126659, 4290311] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 12288/NS)`. -/
theorem cn06_83 : cornerOK gdata (-2304) (12288)
    [990539448, 489144166, 565711979, 188028086, 113788612, 21086141, 6541510] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 8192/NS)`. -/
theorem cn06_84 : cornerOK gdata (-2176) (8192)
    [707185759, 375110372, 424681776, 147755231, 89608383, 16648778, 5620334] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 10240/NS)`. -/
theorem cn06_85 : cornerOK gdata (-2176) (10240)
    [990539448, 489144166, 565711979, 188028086, 113788612, 21086141, 6541510] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 12288/NS)`. -/
theorem cn06_86 : cornerOK gdata (-2176) (12288)
    [990539448, 489144166, 565711979, 188028086, 113788612, 21086141, 6541510] = true := by
  bl_cert

/-- Kernel-checked box `[1792, 2048]/NT × [6144, 8192]/NS`. -/
theorem cov310 : Cover gdata (1792) (2048) (6144) (8192) := by
  ballooning_box "Q:cn06_0,cn06_1,cn06_2,cn06_3"

/-- Kernel-checked box `[2048, 2304]/NT × [6144, 8192]/NS`. -/
theorem cov311 : Cover gdata (2048) (2304) (6144) (8192) := by
  ballooning_box "Q:cn06_1,cn06_4,cn06_3,cn06_5"

/-- Kernel-checked box `[2304, 2560]/NT × [6144, 8192]/NS`. -/
theorem cov312 : Cover gdata (2304) (2560) (6144) (8192) := by
  ballooning_box "Q:cn06_4,cn06_6,cn06_5,cn06_7"

/-- Kernel-checked box `[2560, 2816]/NT × [6144, 8192]/NS`. -/
theorem cov313 : Cover gdata (2560) (2816) (6144) (8192) := by
  ballooning_box "Q:cn06_6,cn06_8,cn06_7,cn06_9"

/-- Kernel-checked box `[2816, 3072]/NT × [6144, 8192]/NS`. -/
theorem cov314 : Cover gdata (2816) (3072) (6144) (8192) := by
  ballooning_box "Q:cn06_8,cn06_10,cn06_9,cn06_11"

/-- Kernel-checked box `[3072, 3328]/NT × [6144, 8192]/NS`. -/
theorem cov315 : Cover gdata (3072) (3328) (6144) (8192) := by
  ballooning_box "Q:cn06_10,cn06_12,cn06_11,cn06_13"

/-- Kernel-checked box `[3328, 3584]/NT × [6144, 8192]/NS`. -/
theorem cov316 : Cover gdata (3328) (3584) (6144) (8192) := by
  ballooning_box "Q:cn06_12,cn06_14,cn06_13,cn06_15"

/-- Kernel-checked box `[3584, 3840]/NT × [6144, 8192]/NS`. -/
theorem cov317 : Cover gdata (3584) (3840) (6144) (8192) := by
  ballooning_box "Q:cn06_14,cn06_16,cn06_15,cn06_17"

/-- Kernel-checked box `[3840, 4096]/NT × [6144, 8192]/NS`. -/
theorem cov318 : Cover gdata (3840) (4096) (6144) (8192) := by
  ballooning_box "Q:cn06_16,cn06_18,cn06_17,cn06_19"

/-- Kernel-checked box `[-4096, -3840]/NT × [8192, 9216]/NS`. -/
theorem cov319 : Cover gdata (-4096) (-3840) (8192) (9216) := by
  ballooning_box "Q:cn06_20,cn06_21,cn06_22,cn06_23"

/-- Kernel-checked box `[-4096, -3840]/NT × [9216, 10240]/NS`. -/
theorem cov320 : Cover gdata (-4096) (-3840) (9216) (10240) := by
  ballooning_box "Q:cn06_22,cn06_23,cn06_24,cn06_25"

/-- Kernel-checked box `[-4096, -3840]/NT × [10240, 11264]/NS`. -/
theorem cov321 : Cover gdata (-4096) (-3840) (10240) (11264) := by
  ballooning_box "Q:cn06_24,cn06_25,cn06_26,cn06_27"

/-- Kernel-checked box `[-4096, -3840]/NT × [11264, 12288]/NS`. -/
theorem cov322 : Cover gdata (-4096) (-3840) (11264) (12288) := by
  ballooning_box "Q:cn06_26,cn06_27,cn06_28,cn06_29"

/-- Kernel-checked box `[-3840, -3584]/NT × [8192, 9216]/NS`. -/
theorem cov323 : Cover gdata (-3840) (-3584) (8192) (9216) := by
  ballooning_box "Q:cn06_21,cn06_30,cn06_23,cn06_31"

/-- Kernel-checked box `[-3840, -3584]/NT × [9216, 10240]/NS`. -/
theorem cov324 : Cover gdata (-3840) (-3584) (9216) (10240) := by
  ballooning_box "Q:cn06_23,cn06_31,cn06_25,cn06_32"

/-- Kernel-checked box `[-3840, -3584]/NT × [10240, 11264]/NS`. -/
theorem cov325 : Cover gdata (-3840) (-3584) (10240) (11264) := by
  ballooning_box "Q:cn06_25,cn06_32,cn06_27,cn06_33"

/-- Kernel-checked box `[-3840, -3584]/NT × [11264, 12288]/NS`. -/
theorem cov326 : Cover gdata (-3840) (-3584) (11264) (12288) := by
  ballooning_box "Q:cn06_27,cn06_33,cn06_29,cn06_34"

/-- Kernel-checked box `[-3584, -3328]/NT × [8192, 9216]/NS`. -/
theorem cov327 : Cover gdata (-3584) (-3328) (8192) (9216) := by
  ballooning_box "Q:cn06_30,cn06_35,cn06_31,cn06_36"

/-- Kernel-checked box `[-3584, -3328]/NT × [9216, 10240]/NS`. -/
theorem cov328 : Cover gdata (-3584) (-3328) (9216) (10240) := by
  ballooning_box "Q:cn06_31,cn06_36,cn06_32,cn06_37"

/-- Kernel-checked box `[-3584, -3328]/NT × [10240, 11264]/NS`. -/
theorem cov329 : Cover gdata (-3584) (-3328) (10240) (11264) := by
  ballooning_box "Q:cn06_32,cn06_37,cn06_33,cn06_38"

/-- Kernel-checked box `[-3584, -3328]/NT × [11264, 12288]/NS`. -/
theorem cov330 : Cover gdata (-3584) (-3328) (11264) (12288) := by
  ballooning_box "Q:cn06_33,cn06_38,cn06_34,cn06_39"

/-- Kernel-checked box `[-3328, -3072]/NT × [8192, 9216]/NS`. -/
theorem cov331 : Cover gdata (-3328) (-3072) (8192) (9216) := by
  ballooning_box "Q:cn06_35,cn06_40,cn06_36,cn06_41"

/-- Kernel-checked box `[-3328, -3072]/NT × [9216, 10240]/NS`. -/
theorem cov332 : Cover gdata (-3328) (-3072) (9216) (10240) := by
  ballooning_box "Q:cn06_36,cn06_41,cn06_37,cn06_42"

/-- Kernel-checked box `[-3328, -3264]/NT × [10240, 12288]/NS`. -/
theorem cov333 : Cover gdata (-3328) (-3264) (10240) (12288) := by
  ballooning_box "Q:cn06_37,cn06_43,cn06_39,cn06_44"

/-- Kernel-checked box `[-3264, -3200]/NT × [10240, 12288]/NS`. -/
theorem cov334 : Cover gdata (-3264) (-3200) (10240) (12288) := by
  ballooning_box "Q:cn06_43,cn06_45,cn06_44,cn06_46"

/-- Kernel-checked box `[-3200, -3136]/NT × [10240, 12288]/NS`. -/
theorem cov335 : Cover gdata (-3200) (-3136) (10240) (12288) := by
  ballooning_box "Q:cn06_45,cn06_47,cn06_46,cn06_48"

/-- Kernel-checked box `[-3136, -3072]/NT × [10240, 12288]/NS`. -/
theorem cov336 : Cover gdata (-3136) (-3072) (10240) (12288) := by
  ballooning_box "Q:cn06_47,cn06_42,cn06_48,cn06_49"

/-- Kernel-checked box `[-3072, -3008]/NT × [8192, 10240]/NS`. -/
theorem cov337 : Cover gdata (-3072) (-3008) (8192) (10240) := by
  ballooning_box "Q:cn06_40,cn06_50,cn06_42,cn06_51"

/-- Kernel-checked box `[-3072, -3008]/NT × [10240, 12288]/NS`. -/
theorem cov338 : Cover gdata (-3072) (-3008) (10240) (12288) := by
  ballooning_box "Q:cn06_42,cn06_51,cn06_49,cn06_52"

/-- Kernel-checked box `[-3008, -2944]/NT × [8192, 10240]/NS`. -/
theorem cov339 : Cover gdata (-3008) (-2944) (8192) (10240) := by
  ballooning_box "Q:cn06_50,cn06_53,cn06_51,cn06_54"

/-- Kernel-checked box `[-3008, -2944]/NT × [10240, 12288]/NS`. -/
theorem cov340 : Cover gdata (-3008) (-2944) (10240) (12288) := by
  ballooning_box "Q:cn06_51,cn06_54,cn06_52,cn06_55"

/-- Kernel-checked box `[-2944, -2880]/NT × [8192, 10240]/NS`. -/
theorem cov341 : Cover gdata (-2944) (-2880) (8192) (10240) := by
  ballooning_box "Q:cn06_53,cn06_56,cn06_54,cn06_57"

/-- Kernel-checked box `[-2944, -2880]/NT × [10240, 12288]/NS`. -/
theorem cov342 : Cover gdata (-2944) (-2880) (10240) (12288) := by
  ballooning_box "Q:cn06_54,cn06_57,cn06_55,cn06_58"

/-- Kernel-checked box `[-2880, -2816]/NT × [8192, 10240]/NS`. -/
theorem cov343 : Cover gdata (-2880) (-2816) (8192) (10240) := by
  ballooning_box "Q:cn06_56,cn06_59,cn06_57,cn06_60"

/-- Kernel-checked box `[-2880, -2816]/NT × [10240, 12288]/NS`. -/
theorem cov344 : Cover gdata (-2880) (-2816) (10240) (12288) := by
  ballooning_box "Q:cn06_57,cn06_60,cn06_58,cn06_61"

/-- Kernel-checked box `[-2816, -2752]/NT × [8192, 10240]/NS`. -/
theorem cov345 : Cover gdata (-2816) (-2752) (8192) (10240) := by
  ballooning_box "Q:cn06_59,cn06_62,cn06_60,cn06_63"

/-- Kernel-checked box `[-2816, -2752]/NT × [10240, 12288]/NS`. -/
theorem cov346 : Cover gdata (-2816) (-2752) (10240) (12288) := by
  ballooning_box "Q:cn06_60,cn06_63,cn06_61,cn06_64"

/-- Kernel-checked box `[-2752, -2688]/NT × [8192, 10240]/NS`. -/
theorem cov347 : Cover gdata (-2752) (-2688) (8192) (10240) := by
  ballooning_box "Q:cn06_62,cn06_65,cn06_63,cn06_66"

/-- Kernel-checked box `[-2752, -2688]/NT × [10240, 12288]/NS`. -/
theorem cov348 : Cover gdata (-2752) (-2688) (10240) (12288) := by
  ballooning_box "Q:cn06_63,cn06_66,cn06_64,cn06_67"

/-- Kernel-checked box `[-2688, -2624]/NT × [8192, 10240]/NS`. -/
theorem cov349 : Cover gdata (-2688) (-2624) (8192) (10240) := by
  ballooning_box "Q:cn06_65,cn06_68,cn06_66,cn06_69"

/-- Kernel-checked box `[-2688, -2624]/NT × [10240, 12288]/NS`. -/
theorem cov350 : Cover gdata (-2688) (-2624) (10240) (12288) := by
  ballooning_box "Q:cn06_66,cn06_69,cn06_67,cn06_70"

/-- Kernel-checked box `[-2624, -2560]/NT × [8192, 10240]/NS`. -/
theorem cov351 : Cover gdata (-2624) (-2560) (8192) (10240) := by
  ballooning_box "Q:cn06_68,cn06_71,cn06_69,cn06_72"

/-- Kernel-checked box `[-2624, -2560]/NT × [10240, 12288]/NS`. -/
theorem cov352 : Cover gdata (-2624) (-2560) (10240) (12288) := by
  ballooning_box "Q:cn06_69,cn06_72,cn06_70,cn06_73"

/-- Kernel-checked box `[-2560, -2432]/NT × [8192, 10240]/NS`. -/
theorem cov353 : Cover gdata (-2560) (-2432) (8192) (10240) := by
  ballooning_box "Q:cn06_71,cn06_74,cn06_72,cn06_75"

/-- Kernel-checked box `[-2560, -2496]/NT × [10240, 12288]/NS`. -/
theorem cov354 : Cover gdata (-2560) (-2496) (10240) (12288) := by
  ballooning_box "Q:cn06_72,cn06_76,cn06_73,cn06_77"

/-- Kernel-checked box `[-2496, -2432]/NT × [10240, 12288]/NS`. -/
theorem cov355 : Cover gdata (-2496) (-2432) (10240) (12288) := by
  ballooning_box "Q:cn06_76,cn06_75,cn06_77,cn06_78"

/-- Kernel-checked box `[-2432, -2304]/NT × [8192, 10240]/NS`. -/
theorem cov356 : Cover gdata (-2432) (-2304) (8192) (10240) := by
  ballooning_box "Q:cn06_74,cn06_79,cn06_75,cn06_80"

/-- Kernel-checked box `[-2432, -2368]/NT × [10240, 12288]/NS`. -/
theorem cov357 : Cover gdata (-2432) (-2368) (10240) (12288) := by
  ballooning_box "Q:cn06_75,cn06_81,cn06_78,cn06_82"

/-- Kernel-checked box `[-2368, -2304]/NT × [10240, 12288]/NS`. -/
theorem cov358 : Cover gdata (-2368) (-2304) (10240) (12288) := by
  ballooning_box "Q:cn06_81,cn06_80,cn06_82,cn06_83"

/-- Kernel-checked box `[-2304, -2176]/NT × [8192, 10240]/NS`. -/
theorem cov359 : Cover gdata (-2304) (-2176) (8192) (10240) := by
  ballooning_box "Q:cn06_79,cn06_84,cn06_80,cn06_85"

/-- Kernel-checked box `[-2304, -2176]/NT × [10240, 12288]/NS`. -/
theorem cov360 : Cover gdata (-2304) (-2176) (10240) (12288) := by
  ballooning_box "Q:cn06_80,cn06_85,cn06_83,cn06_86"

end PlasmaLean.Design.SolovevBallooning
