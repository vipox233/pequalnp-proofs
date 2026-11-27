import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27511_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (W gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hfold : W (g :: gs) w = W gs (step w g) := rfl
    rw [hfold]
    have hlen : i < (step w g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [ih (step w g) hlen]
    simp only [step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

lemma W_getD_add (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs.get ⟨j, hj⟩).inputs, i < w.length + j) :
    (W gs w).getD (w.length + j) false =
      (gs.get ⟨j, hj⟩).op.eval ((gs.get ⟨j, hj⟩).inputs.map fun i => (W gs w).getD i false) := by
  induction gs generalizing w j with
  | nil => cases hj
  | cons g gs ih =>
    have hfold : W (g :: gs) w = W gs (step w g) := rfl
    rw [hfold]
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hin ⊢
      have hlen : w.length < (step w g).length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      rw [W_getD_lt gs (step w g) w.length hlen]
      have hget0 : (g :: gs).get ⟨0, hj⟩ = g := rfl
      rw [hget0] at hin ⊢
      have hstep : (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl _)]
        simp
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil : i < w.length := hin i hi
      rw [W_getD_lt gs (step w g) i (by simp only [step, List.length_append, List.length_singleton]; omega)]
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hil]
    | succ j' =>
      have hj' : j' < gs.length := by simp at hj; omega
      have hgetS : (g :: gs).get ⟨j' + 1, hj⟩ = gs.get ⟨j', hj'⟩ := rfl
      rw [hgetS] at hin ⊢
      have hrew : w.length + (j' + 1) = (step w g).length + j' := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      rw [hrew]
      exact ih (step w g) j' hj' (fun i hi => by
        have := hin i hi
        simp only [step, List.length_append, List.length_singleton]
        omega)

def wireVal (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_lt9 (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
    wireVal C x i.val = x i := by
  unfold wireVal
  rw [wires_eq_W, W_getD_lt C.gates (List.ofFn x) i.val (by simp [i.isLt])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

lemma wireVal_nat (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) (hw : w < 9) :
    wireVal C x w = x ⟨w, hw⟩ :=
  wireVal_lt9 C x ⟨w, hw⟩

lemma wireVal_gate (C : Circuit) (x : Fin 9 → Bool) (j : Fin C.gates.length)
    (hin : ∀ i ∈ (C.gates.get j).inputs, i < 9 + j.val) :
    wireVal C x (9 + j.val) =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wireVal C x)) := by
  unfold wireVal
  rw [wires_eq_W]
  have hlen : (List.ofFn x).length = 9 := by simp
  have h := W_getD_add C.gates (List.ofFn x) j.val j.isLt (by rw [hlen]; exact hin)
  rw [hlen] at h
  exact h

def Restricted (x : Fin 9 → Bool) : Prop := x 0 = false

def IsConst (C : Circuit) (w : ℕ) : Prop :=
  ∀ x y : Fin 9 → Bool, Restricted x → Restricted y → wireVal C x w = wireVal C y w

def NormalGate (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])

lemma normal_inputs_lt {C : Circuit} (hNF : NormalGate C) (j : Fin C.gates.length) :
    ∀ i ∈ (C.gates.get j).inputs, i < 9 + j.val := by
  rcases hNF j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
  · intro i hi; rw [hin] at hi; simp at hi; omega
  · intro i hi; rw [hin] at hi; simp at hi; rcases hi with rfl | rfl <;> omega

lemma normal_inputs_len {C : Circuit} (hNF : NormalGate C) (j : Fin C.gates.length) :
    (C.gates.get j).inputs.length ≤ 2 := by
  rcases hNF j with ⟨_, a, _, hin⟩ | ⟨_, a, b, _, _, hin⟩
  · rw [hin]; simp
  · rw [hin]; simp

def V8 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8}

lemma V8_card : V8.card = 8 := by decide

lemma V8_essential (v : ℕ) (hv : v ∈ V8) :
    ∃ x y : Fin 9 → Bool, Restricted x ∧ Restricted y ∧
      (∀ i : Fin 9, i.val ≠ v → x i = y i) ∧ pm3 x ≠ pm3 y := by
  simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun i => decide (i = 3 ∨ i = 8), fun i => decide (i = 1 ∨ i = 3 ∨ i = 8),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 3 ∨ i = 7), fun i => decide (i = 2 ∨ i = 3 ∨ i = 7),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 1 ∨ i = 8), fun i => decide (i = 1 ∨ i = 3 ∨ i = 8),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 2 ∨ i = 6), fun i => decide (i = 2 ∨ i = 4 ∨ i = 6),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 1 ∨ i = 6), fun i => decide (i = 1 ∨ i = 5 ∨ i = 6),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 1 ∨ i = 5), fun i => decide (i = 1 ∨ i = 5 ∨ i = 6),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 2 ∨ i = 3), fun i => decide (i = 2 ∨ i = 3 ∨ i = 7),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 1 ∨ i = 3), fun i => decide (i = 1 ∨ i = 3 ∨ i = 8),
      by rfl, by rfl, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all

def modWitArr : Array ℕ := #[
  0, 0, 0, 4043111426, 0, 4176672772, 4176082948, 2969106438,
  0, 4109562888, 4042585090, 2499081226, 3790795272, 4042453516, 4041338892, 2431709198,
  0, 3907841025, 3974753296, 3773623314, 3806980368, 3907184660, 3907643668, 2699618326,
  3806585616, 3840074776, 3840009240, 2229593114, 3286491928, 3772965404, 3772899612, 2162221086,
  0, 3705330720, 3705265184, 3504135202, 3537623840, 3638221348, 3638155556, 2430130214,
  3537097504, 3570586664, 3570521128, 3235173417, 3251884840, 3503477292, 3503411500, 1087426605,
  3385576224, 3435842608, 3435777072, 3234647090, 3268135728, 3368733236, 3368667444, 2160642102,
  3267609392, 3301098552, 3301033016, 3234120754, 2193867572, 3233989180, 3233923388, 2160115766,
  0, 3166092352, 3032267778, 2965158978, 2997465604, 3098720324, 3098130500, 683194437,
  2998318656, 3031873096, 2964632642, 2696197193, 2712842824, 2964501068, 2963386444, 548450381,
  2846271808, 2896604240, 2896800848, 2695670866, 2729027920, 2829232212, 2829691220, 145270869,
  2728830544, 2762384984, 2762056792, 77898841, 2208539480, 2695012956, 2694947164, 10526813,
  2610863680, 2627640928, 2627312736, 2426182754, 2459671392, 2560268900, 2560203108, 144218213,
  2459342432, 2492896872, 2492568680, 2157220969, 2173932392, 2425524844, 2425459052, 9474157,
  2307821152, 2358152816, 2357824624, 2156694642, 2190183280, 2290780788, 2290714996, 2156431474,
  2189854320, 2223408760, 2223080568, 2156168306, 2189656944, 2156036732, 2155970940, 8421485,
  0, 1820097537, 2087550080, 1887206530, 1769107972, 2020767876, 2020178052, 813201542,
  1919251072, 1953657992, 1952806024, 343176330, 1634890376, 1886548620, 1885433996, 275804302,
  1768779136, 1751936129, 1819110800, 1617718418, 1651075472, 1751279764, 1751738772, 543713430,
  1650812304, 1684169880, 1684366744, 73688218, 1130587032, 1617060508, 1616994716, 6316190,
  1532845440, 1549425824, 1549622688, 1348230306, 1381718944, 1482316452, 1482250660, 274225318,
  1381324192, 1414681768, 1414878632, 1079268521, 1095979944, 1347572396, 1347506604, 1079005353,
  1229802912, 1279937712, 1280134576, 1078742194, 1112230832, 1212828340, 1212762548, 4737206,
  1111836080, 1145193656, 1145390520, 1078215858, 37962676, 1078084284, 1078018492, 4210870,
  908932736, 1010187456, 1009597632, 809254082, 841560708, 942815428, 942225604, 540555459,
  842413760, 875968200, 874853576, 540292297, 556937928, 808596172, 807481548, 271593675,
  690826688, 740699344, 741158352, 539765970, 573123024, 673327316, 673786324, 136849619,
  572991440, 606480088, 606414296, 539239634, 52634584, 539108060, 539042268, 2105563,
  455024576, 471736032, 471670240, 270277858, 303766496, 404364004, 404298212, 1579235,
  303503328, 336991976, 336926184, 1316073, 18027496, 269619948, 269554156, 1052905,
  151982048, 202247920, 202182128, 789746, 34278384, 134875892, 134810100, 526578,
  34015216, 67503864, 67438072, 263410, 33752048, 131836, 66044, 0
]

def mask2fn (m : ℕ) : Fin 9 → Bool :=
  fun i => if i.val = 0 then false else m.testBit (i.val - 1)

lemma mask2fn_restricted (m : ℕ) : Restricted (mask2fn m) := by
  simp [Restricted, mask2fn]

def f8Bit (m : ℕ) : Bool :=
  (m.testBit 0 && m.testBit 2 && m.testBit 7) ||
  (m.testBit 0 && m.testBit 4 && m.testBit 5) ||
  (m.testBit 1 && m.testBit 2 && m.testBit 6) ||
  (m.testBit 1 && m.testBit 3 && m.testBit 5)

lemma f8Bit_eq_pm3 (m : ℕ) : f8Bit m = pm3 (mask2fn m) := by
  simp [f8Bit, pm3, mask2fn]

def pop8 (m : ℕ) : ℕ :=
  (List.range 8).countP fun b => m.testBit b

def checkModOne (S : ℕ) : Bool :=
  if 2 ≤ pop8 S && pop8 S ≤ 7 then
    let p := modWitArr.getD S 0
    let a := p % 256
    let c0 := (p / 256) % 256
    let c1 := (p / 65536) % 256
    let c2 := (p / 16777216) % 256
    ((a &&& S) == a) &&
    ((c0 &&& S) == 0) &&
    ((c1 &&& S) == 0) &&
    ((c2 &&& S) == 0) &&
    (f8Bit c0 != f8Bit (S ||| c0)) &&
    (f8Bit (a ||| c1) != f8Bit c1) &&
    (f8Bit (a ||| c2) != f8Bit (S ||| c2))
  else true

set_option maxRecDepth 20000 in
lemma checkModAll : (List.range 256).all checkModOne = true := by decide +kernel

lemma testBit_and_eq_self {a S b : ℕ} (h : (a &&& S) = a) (hb : a.testBit b = true) :
    S.testBit b = true := by
  have h1 := congrArg (fun n => n.testBit b) h
  simp only [Nat.testBit_and, hb, Bool.true_and] at h1
  exact h1

lemma testBit_and_eq_zero {c S b : ℕ} (h : (c &&& S) = 0) (hs : S.testBit b = true) :
    c.testBit b = false := by
  have h1 := congrArg (fun n => n.testBit b) h
  simp only [Nat.testBit_and, hs, Bool.and_true, Nat.zero_testBit] at h1
  exact h1

def finsetToMask (S : Finset ℕ) : ℕ :=
  (List.range 8).foldl (fun acc b => if b + 1 ∈ S then acc ||| 2 ^ b else acc) 0

lemma finsetToMask_lt (S : Finset ℕ) : finsetToMask S < 256 := by
  have haux : ∀ l : List ℕ, (∀ b ∈ l, b < 8) → ∀ acc : ℕ, acc < 2 ^ 8 →
      (l.foldl (fun a b => if b + 1 ∈ S then a ||| 2 ^ b else a) acc) < 2 ^ 8 := by
    intro l
    induction l with
    | nil => intro _ acc hacc; exact hacc
    | cons b bs ih =>
      intro hlt acc hacc
      simp only [List.foldl_cons]
      apply ih (fun x hx => hlt x (List.mem_cons_of_mem b hx))
      split_ifs
      · apply Nat.or_lt_two_pow hacc
        exact Nat.pow_lt_pow_right (by omega) (hlt b (List.mem_cons_self ..))
      · exact hacc
  exact haux (List.range 8) (fun b hb => List.mem_range.mp hb) 0 (by decide)

lemma foldl_or_pow_testBit (S : Finset ℕ) :
    ∀ l : List ℕ, ∀ acc k : ℕ,
      (l.foldl (fun a b => if b + 1 ∈ S then a ||| 2 ^ b else a) acc).testBit k =
        (decide (k ∈ l ∧ k + 1 ∈ S) || acc.testBit k) := by
  intro l
  induction l with
  | nil => intro acc k; simp
  | cons b bs ih =>
    intro acc k
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hbS : b + 1 ∈ S
    · rw [if_pos hbS, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases hkb : k = b
      · subst hkb; simp [hbS]
      · simp [hkb, Ne.symm hkb]
    · rw [if_neg hbS]
      by_cases hkb : k = b
      · subst hkb; simp [hbS]
      · simp [hkb]

lemma finsetToMask_testBit (S : Finset ℕ) (b : ℕ) (hb : b < 8) :
    (finsetToMask S).testBit b = decide (b + 1 ∈ S) := by
  unfold finsetToMask
  rw [foldl_or_pow_testBit]
  have hmem : b ∈ List.range 8 := List.mem_range.mpr hb
  simp [hmem]

lemma pop8_finsetToMask (S : Finset ℕ) (hsub : S ⊆ V8) : pop8 (finsetToMask S) = S.card := by
  unfold pop8
  have h1 : (List.range 8).countP (fun b => (finsetToMask S).testBit b) =
      (List.range 8).countP (fun b => decide (b + 1 ∈ S)) := by
    apply List.countP_congr
    intro b hb
    rw [finsetToMask_testBit S b (List.mem_range.mp hb)]
  rw [h1]
  have h2 : (List.range 8).countP (fun b => decide (b + 1 ∈ S)) =
      ((Finset.range 8).filter fun b => b + 1 ∈ S).card := by
    rw [List.countP_eq_length_filter]
    have hnd : ((List.range 8).filter fun b => decide (b + 1 ∈ S)).Nodup :=
      List.Nodup.filter _ List.nodup_range
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext b
    simp [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter, Finset.mem_range]
  rw [h2]
  have himg : ((Finset.range 8).filter fun b => b + 1 ∈ S).image (· + 1) = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨b, ⟨_, hmem⟩, rfl⟩; exact hmem
    · intro hx
      have hxV : x ∈ V8 := hsub hx
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hxV
      refine ⟨x - 1, ⟨by omega, ?_⟩, by omega⟩
      have : x - 1 + 1 = x := by omega
      rwa [this]
  have hci := Finset.card_image_of_injective ((Finset.range 8).filter fun b => b + 1 ∈ S) (f := (· + 1)) (fun a b h => by dsimp at h; omega)
  rw [himg] at hci
  exact hci.symm

lemma no_module_f8_refute (S : Finset ℕ) (hsub : S ⊆ V8) (hge : 2 ≤ S.card) (hle : S.card ≤ 7)
    (φ : (Fin 9 → Bool) → Bool)
    (hφS : ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
      (∀ i : Fin 9, i.val ∈ S → x i = y i) → φ x = φ y)
    (hfact : ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
      (∀ i : Fin 9, i.val ∈ V8 → i.val ∉ S → x i = y i) → φ x = φ y → pm3 x = pm3 y) : False := by
  let mS := finsetToMask S
  have hmS_lt : mS < 256 := finsetToMask_lt S
  have hpop : pop8 mS = S.card := pop8_finsetToMask S hsub
  have hchk : checkModOne mS = true :=
    List.all_eq_true.mp checkModAll mS (List.mem_range.mpr hmS_lt)
  unfold checkModOne at hchk
  have hcond : (2 ≤ pop8 mS && pop8 mS ≤ 7) = true := by
    rw [hpop]
    simp [hge, hle]
  rw [hcond] at hchk
  simp only [ite_true] at hchk
  set p := modWitArr.getD mS 0
  set a := p % 256
  set c0 := (p / 256) % 256
  set c1 := (p / 65536) % 256
  set c2 := (p / 16777216) % 256
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hchk
  obtain ⟨⟨⟨⟨⟨⟨haS, hc0S⟩, hc1S⟩, hc2S⟩, hdiff0⟩, hdiff1⟩, hdiff2⟩ := hchk
  have hS_bit : ∀ i : Fin 9, i.val ∈ V8 → (mS.testBit (i.val - 1) = true ↔ i.val ∈ S) := by
    intro i hi
    have hlt : i.val - 1 < 8 := by simp [V8] at hi; omega
    have hadd : i.val - 1 + 1 = i.val := by simp [V8] at hi; omega
    rw [finsetToMask_testBit S (i.val - 1) hlt, hadd, decide_eq_true_eq]
  have hS_of_mem : ∀ i : Fin 9, i.val ∈ S → mS.testBit (i.val - 1) = true := by
    intro i hi
    exact (hS_bit i (hsub hi)).mpr hi
  have hagree_S : ∀ m c : ℕ, (c &&& mS) = 0 →
      ∀ i : Fin 9, i.val ∈ S → mask2fn (m ||| c) i = mask2fn m i := by
    intro m c hc i hi
    have hi0 : i.val ≠ 0 := by have := hsub hi; simp [V8] at this; omega
    simp only [mask2fn, hi0, ite_false, Nat.testBit_or]
    have hcb : c.testBit (i.val - 1) = false := testBit_and_eq_zero hc (hS_of_mem i hi)
    rw [hcb, Bool.or_false]
  have hagree_out : ∀ m c : ℕ, (m &&& mS) = m →
      ∀ i : Fin 9, i.val ∈ V8 → i.val ∉ S → mask2fn (m ||| c) i = mask2fn c i := by
    intro m c hm i hi hni
    have hi0 : i.val ≠ 0 := by simp [V8] at hi; omega
    simp only [mask2fn, hi0, ite_false, Nat.testBit_or]
    have hmb : m.testBit (i.val - 1) = false := by
      cases h : m.testBit (i.val - 1)
      · rfl
      · have hs := testBit_and_eq_self hm h
        exact absurd ((hS_bit i hi).mp hs) hni
    rw [hmb, Bool.false_or]
  have hmS_self : (mS &&& mS) = mS := Nat.and_self mS
  have hφ_c0 : φ (mask2fn c0) = φ (mask2fn 0) :=
    hφS _ _ (mask2fn_restricted _) (mask2fn_restricted _) (fun i hi => by
      have h := hagree_S 0 c0 hc0S i hi
      simpa using h)
  have hφ_c1 : φ (mask2fn c1) = φ (mask2fn 0) :=
    hφS _ _ (mask2fn_restricted _) (mask2fn_restricted _) (fun i hi => by
      have h := hagree_S 0 c1 hc1S i hi
      simpa using h)
  have hφ_Sc0 : φ (mask2fn (mS ||| c0)) = φ (mask2fn mS) :=
    hφS _ _ (mask2fn_restricted _) (mask2fn_restricted _) (hagree_S mS c0 hc0S)
  have hφ_Sc2 : φ (mask2fn (mS ||| c2)) = φ (mask2fn mS) :=
    hφS _ _ (mask2fn_restricted _) (mask2fn_restricted _) (hagree_S mS c2 hc2S)
  have hφ_ac1 : φ (mask2fn (a ||| c1)) = φ (mask2fn a) :=
    hφS _ _ (mask2fn_restricted _) (mask2fn_restricted _) (hagree_S a c1 hc1S)
  have hφ_ac2 : φ (mask2fn (a ||| c2)) = φ (mask2fn a) :=
    hφS _ _ (mask2fn_restricted _) (mask2fn_restricted _) (hagree_S a c2 hc2S)
  cases h0 : φ (mask2fn 0) <;> cases ha : φ (mask2fn a) <;> cases hS : φ (mask2fn mS)
  · apply hdiff0
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => (hagree_out mS c0 hmS_self i hi hni).symm) (by rw [hφ_c0, hφ_Sc0, h0, hS])
  · apply hdiff1
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => hagree_out a c1 haS i hi hni) (by rw [hφ_ac1, hφ_c1, ha, h0])
  · apply hdiff0
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => (hagree_out mS c0 hmS_self i hi hni).symm) (by rw [hφ_c0, hφ_Sc0, h0, hS])
  · apply hdiff2
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => by rw [hagree_out a c2 haS i hi hni, hagree_out mS c2 hmS_self i hi hni])
      (by rw [hφ_ac2, hφ_Sc2, ha, hS])
  · apply hdiff2
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => by rw [hagree_out a c2 haS i hi hni, hagree_out mS c2 hmS_self i hi hni])
      (by rw [hφ_ac2, hφ_Sc2, ha, hS])
  · apply hdiff0
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => (hagree_out mS c0 hmS_self i hi hni).symm) (by rw [hφ_c0, hφ_Sc0, h0, hS])
  · apply hdiff1
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => hagree_out a c1 haS i hi hni) (by rw [hφ_ac1, hφ_c1, ha, h0])
  · apply hdiff0
    rw [f8Bit_eq_pm3, f8Bit_eq_pm3]
    exact hfact _ _ (mask2fn_restricted _) (mask2fn_restricted _)
      (fun i hi hni => (hagree_out mS c0 hmS_self i hi hni).symm) (by rw [hφ_c0, hφ_Sc0, h0, hS])

inductive MForm4 where
  | const (b : Bool)
  | var (i : Fin 4)
  | and (l r : MForm4)
  | or (l r : MForm4)

def MForm4.eval : MForm4 → (Fin 4 → Bool) → Bool
  | .const b, _ => b
  | .var i, x => x i
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

def MForm4.vars : MForm4 → Finset (Fin 4)
  | .const _ => ∅
  | .var i => {i}
  | .and l r => l.vars ∪ r.vars
  | .or l r => l.vars ∪ r.vars

def MForm4.readOnce : MForm4 → Prop
  | .const _ => True
  | .var _ => True
  | .and l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.vars r.vars
  | .or l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.vars r.vars

lemma MForm4.eval_congr (φ : MForm4) (x y : Fin 4 → Bool)
    (h : ∀ i ∈ φ.vars, x i = y i) : φ.eval x = φ.eval y := by
  induction φ with
  | const b => rfl
  | var i => exact h i (by simp [MForm4.vars])
  | and l r ihl ihr =>
    simp only [MForm4.eval]
    rw [ihl (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihr (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or l r ihl ihr =>
    simp only [MForm4.eval]
    rw [ihl (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihr (fun i hi => h i (Finset.mem_union_right _ hi))]

lemma MForm4.eval_mono (φ : MForm4) (x y : Fin 4 → Bool)
    (h : ∀ i : Fin 4, x i = true → y i = true) (hx : φ.eval x = true) : φ.eval y = true := by
  induction φ with
  | const b => exact hx
  | var i => exact h i hx
  | and l r ihl ihr =>
    simp only [MForm4.eval, Bool.and_eq_true] at hx ⊢
    exact ⟨ihl hx.1, ihr hx.2⟩
  | or l r ihl ihr =>
    simp only [MForm4.eval, Bool.or_eq_true] at hx ⊢
    rcases hx with hl | hr
    · exact Or.inl (ihl hl)
    · exact Or.inr (ihr hr)

def p4fn (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

lemma not_readOnce_P4 (φ : MForm4) (hro : φ.readOnce)
    (heq : ∀ x : Fin 4 → Bool, φ.eval x = p4fn x) : False := by
  induction φ with
  | const b =>
    have h0 : b = false := by simpa [MForm4.eval, p4fn] using heq (fun _ => false)
    have h1 : b = true := by simpa [MForm4.eval, p4fn] using heq (fun _ => true)
    rw [h0] at h1
    exact Bool.false_ne_true h1
  | var i =>
    fin_cases i
    · have h := heq (fun j => decide (j = 0)); revert h; decide
    · have h := heq (fun j => decide (j = 1)); revert h; decide
    · have h := heq (fun j => decide (j = 2)); revert h; decide
    · have h := heq (fun j => decide (j = 3)); revert h; decide
  | and l r ihl ihr =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    by_cases hl0 : l.eval (fun _ => false) = true
    · apply ihr hror
      intro x
      have hlx : l.eval x = true := l.eval_mono _ x (fun _ h => by simp at h) hl0
      have h := heq x
      simp [MForm4.eval, hlx] at h
      exact h
    · by_cases hr0 : r.eval (fun _ => false) = true
      · apply ihl hrol
        intro x
        have hrx : r.eval x = true := r.eval_mono _ x (fun _ h => by simp at h) hr0
        have h := heq x
        simp [MForm4.eval, hrx] at h
        exact h
      · have hlf : l.eval (fun _ => false) = false := by cases h : l.eval (fun _ => false) <;> simp_all
        have hrf : r.eval (fun _ => false) = false := by cases h : r.eval (fun _ => false) <;> simp_all
        let x01 : Fin 4 → Bool := fun j => decide (j = 0 ∨ j = 1)
        let x12 : Fin 4 → Bool := fun j => decide (j = 1 ∨ j = 2)
        let x23 : Fin 4 → Bool := fun j => decide (j = 2 ∨ j = 3)
        let x03 : Fin 4 → Bool := fun j => decide (j = 0 ∨ j = 3)
        have h01 : l.eval x01 = true ∧ r.eval x01 = true := by
          have h := heq x01; simp [MForm4.eval, p4fn, x01] at h; exact h
        have h12 : l.eval x12 = true ∧ r.eval x12 = true := by
          have h := heq x12; simp [MForm4.eval, p4fn, x12] at h; exact h
        have h23 : l.eval x23 = true ∧ r.eval x23 = true := by
          have h := heq x23; simp [MForm4.eval, p4fn, x23] at h; exact h
        have h03 : l.eval x03 = false ∨ r.eval x03 = false := by
          have h : (l.eval x03 && r.eval x03) = false := by
            simpa [MForm4.eval, p4fn, x03] using heq x03
          exact Bool.and_eq_false_iff.mp h
        have hit_pair : ∀ (ψ : MForm4) (a b : Fin 4),
            ψ.eval (fun _ => false) = false → ψ.eval (fun j => decide (j = a ∨ j = b)) = true →
            a ∈ ψ.vars ∨ b ∈ ψ.vars := by
          intro ψ a b h0 ht
          by_contra hno
          push Not at hno
          have heq' := ψ.eval_congr (fun _ => false) (fun j => decide (j = a ∨ j = b)) (fun j hj => by
            have hja : j ≠ a := fun h => hno.1 (h ▸ hj)
            have hjb : j ≠ b := fun h => hno.2 (h ▸ hj)
            simp [hja, hjb])
          rw [h0, ht] at heq'
          exact Bool.false_ne_true heq'
        have hl01 := hit_pair l 0 1 hlf h01.1
        have hl12 := hit_pair l 1 2 hlf h12.1
        have hl23 := hit_pair l 2 3 hlf h23.1
        have hr01 := hit_pair r 0 1 hrf h01.2
        have hr12 := hit_pair r 1 2 hrf h12.2
        have hr23 := hit_pair r 2 3 hrf h23.2
        have hdisj' : ∀ i : Fin 4, ¬ (i ∈ l.vars ∧ i ∈ r.vars) := fun i hi =>
          Finset.disjoint_left.mp hdisj hi.1 hi.2
        have hcase : (0 ∈ l.vars ∧ 2 ∈ l.vars ∧ 1 ∈ r.vars ∧ 3 ∈ r.vars) ∨
            (1 ∈ l.vars ∧ 3 ∈ l.vars ∧ 0 ∈ r.vars ∧ 2 ∈ r.vars) := by
          by_cases h1l : (1 : Fin 4) ∈ l.vars
          · have h1r : (1 : Fin 4) ∉ r.vars := fun h => hdisj' 1 ⟨h1l, h⟩
            have h0r : (0 : Fin 4) ∈ r.vars := hr01.resolve_right h1r
            have h2r : (2 : Fin 4) ∈ r.vars := hr12.resolve_left h1r
            have h2l : (2 : Fin 4) ∉ l.vars := fun h => hdisj' 2 ⟨h, h2r⟩
            have h3l : (3 : Fin 4) ∈ l.vars := hl23.resolve_left h2l
            exact Or.inr ⟨h1l, h3l, h0r, h2r⟩
          · have h0l : (0 : Fin 4) ∈ l.vars := hl01.resolve_right h1l
            have h2l : (2 : Fin 4) ∈ l.vars := hl12.resolve_left h1l
            have h0r : (0 : Fin 4) ∉ r.vars := fun h => hdisj' 0 ⟨h0l, h⟩
            have h2r : (2 : Fin 4) ∉ r.vars := fun h => hdisj' 2 ⟨h2l, h⟩
            have h1r : (1 : Fin 4) ∈ r.vars := hr01.resolve_left h0r
            have h3r : (3 : Fin 4) ∈ r.vars := hr23.resolve_left h2r
            exact Or.inl ⟨h0l, h2l, h1r, h3r⟩
        rcases hcase with ⟨h0l, h2l, h1r, h3r⟩ | ⟨h1l, h3l, h0r, h2r⟩
        · have hl03 : l.eval x03 = true := by
            rw [l.eval_congr x03 x01 (fun j hj => by
              fin_cases j
              · rfl
              · exact absurd ⟨hj, h1r⟩ (hdisj' 1)
              · rfl
              · exact absurd ⟨hj, h3r⟩ (hdisj' 3))]
            exact h01.1
          have hr03 : r.eval x03 = true := by
            rw [r.eval_congr x03 x23 (fun j hj => by
              fin_cases j
              · exact absurd ⟨h0l, hj⟩ (hdisj' 0)
              · rfl
              · exact absurd ⟨h2l, hj⟩ (hdisj' 2)
              · rfl)]
            exact h23.2
          rcases h03 with h | h
          · rw [hl03] at h; exact Bool.false_ne_true h.symm
          · rw [hr03] at h; exact Bool.false_ne_true h.symm
        · have hl03 : l.eval x03 = true := by
            rw [l.eval_congr x03 x23 (fun j hj => by
              fin_cases j
              · exact absurd ⟨hj, h0r⟩ (hdisj' 0)
              · rfl
              · exact absurd ⟨hj, h2r⟩ (hdisj' 2)
              · rfl)]
            exact h23.1
          have hr03 : r.eval x03 = true := by
            rw [r.eval_congr x03 x01 (fun j hj => by
              fin_cases j
              · rfl
              · exact absurd ⟨h1l, hj⟩ (hdisj' 1)
              · rfl
              · exact absurd ⟨h3l, hj⟩ (hdisj' 3))]
            exact h01.2
          rcases h03 with h | h
          · rw [hl03] at h; exact Bool.false_ne_true h.symm
          · rw [hr03] at h; exact Bool.false_ne_true h.symm
  | or l r ihl ihr =>
    rcases hro with ⟨hrol, hror, hdisj⟩
    let x01 : Fin 4 → Bool := fun j => decide (j = 0 ∨ j = 1)
    let x12 : Fin 4 → Bool := fun j => decide (j = 1 ∨ j = 2)
    let x23 : Fin 4 → Bool := fun j => decide (j = 2 ∨ j = 3)
    let x02 : Fin 4 → Bool := fun j => decide (j = 0 ∨ j = 2)
    let x13 : Fin 4 → Bool := fun j => decide (j = 1 ∨ j = 3)
    have h02f : l.eval x02 = false ∧ r.eval x02 = false := by
      have h := heq x02; simp [MForm4.eval, p4fn, x02] at h; exact h
    have h13f : l.eval x13 = false ∧ r.eval x13 = false := by
      have h := heq x13; simp [MForm4.eval, p4fn, x13] at h; exact h
    have h01t : l.eval x01 = true ∨ r.eval x01 = true := by
      have h := heq x01; simp [MForm4.eval, p4fn, x01] at h; exact h
    have h12t : l.eval x12 = true ∨ r.eval x12 = true := by
      have h := heq x12; simp [MForm4.eval, p4fn, x12] at h; exact h
    have h23t : l.eval x23 = true ∨ r.eval x23 = true := by
      have h := heq x23; simp [MForm4.eval, p4fn, x23] at h; exact h
    have need_single : ∀ (ψ : MForm4) (u a b : Fin 4) (y : Fin 4 → Bool),
        ψ.eval y = false →
        (∀ j : Fin 4, decide ((j = a ∨ j = b) ∧ j ≠ u) = true → y j = true) →
        ψ.eval (fun j => decide (j = a ∨ j = b)) = true → u ∈ ψ.vars := by
      intro ψ u a b y hyf hle ht
      by_contra hnu
      let xrem : Fin 4 → Bool := fun j => decide ((j = a ∨ j = b) ∧ j ≠ u)
      have heq' := ψ.eval_congr (fun j => decide (j = a ∨ j = b)) xrem (fun j hj => by
        have hju : j ≠ u := fun h => hnu (h ▸ hj)
        simp [xrem, hju])
      have hrt : ψ.eval xrem = true := heq'.symm.trans ht
      have hyt := ψ.eval_mono xrem y hle hrt
      rw [hyf] at hyt
      exact Bool.false_ne_true hyt
    have need01 : ∀ ψ : MForm4, ψ.eval x02 = false → ψ.eval x13 = false → ψ.eval x01 = true →
        (0 : Fin 4) ∈ ψ.vars ∧ (1 : Fin 4) ∈ ψ.vars := fun ψ h02' h13' ht =>
      ⟨need_single ψ 0 0 1 x13 h13' (by decide) ht,
       need_single ψ 1 0 1 x02 h02' (by decide) ht⟩
    have need12 : ∀ ψ : MForm4, ψ.eval x02 = false → ψ.eval x13 = false → ψ.eval x12 = true →
        (1 : Fin 4) ∈ ψ.vars ∧ (2 : Fin 4) ∈ ψ.vars := fun ψ h02' h13' ht =>
      ⟨need_single ψ 1 1 2 x02 h02' (by decide) ht,
       need_single ψ 2 1 2 x13 h13' (by decide) ht⟩
    have need23 : ∀ ψ : MForm4, ψ.eval x02 = false → ψ.eval x13 = false → ψ.eval x23 = true →
        (2 : Fin 4) ∈ ψ.vars ∧ (3 : Fin 4) ∈ ψ.vars := fun ψ h02' h13' ht =>
      ⟨need_single ψ 2 2 3 x13 h13' (by decide) ht,
       need_single ψ 3 2 3 x02 h02' (by decide) ht⟩
    have hdisj' : ∀ i : Fin 4, ¬ (i ∈ l.vars ∧ i ∈ r.vars) := fun i hi =>
      Finset.disjoint_left.mp hdisj hi.1 hi.2
    have hall : (∀ i : Fin 4, i ∈ l.vars) ∨ (∀ i : Fin 4, i ∈ r.vars) := by
      rcases h01t with h01l | h01r
      · have ⟨h0l, h1l⟩ := need01 l h02f.1 h13f.1 h01l
        have h12l : l.eval x12 = true := by
          rcases h12t with h | h
          · exact h
          · exact absurd ⟨h1l, (need12 r h02f.2 h13f.2 h).1⟩ (hdisj' 1)
        have ⟨_, h2l⟩ := need12 l h02f.1 h13f.1 h12l
        have h23l : l.eval x23 = true := by
          rcases h23t with h | h
          · exact h
          · exact absurd ⟨h2l, (need23 r h02f.2 h13f.2 h).1⟩ (hdisj' 2)
        have ⟨_, h3l⟩ := need23 l h02f.1 h13f.1 h23l
        exact Or.inl (fun i => by fin_cases i <;> assumption)
      · have ⟨h0r, h1r⟩ := need01 r h02f.2 h13f.2 h01r
        have h12r : r.eval x12 = true := by
          rcases h12t with h | h
          · exact absurd ⟨(need12 l h02f.1 h13f.1 h).1, h1r⟩ (hdisj' 1)
          · exact h
        have ⟨_, h2r⟩ := need12 r h02f.2 h13f.2 h12r
        have h23r : r.eval x23 = true := by
          rcases h23t with h | h
          · exact absurd ⟨(need23 l h02f.1 h13f.1 h).1, h2r⟩ (hdisj' 2)
          · exact h
        have ⟨_, h3r⟩ := need23 r h02f.2 h13f.2 h23r
        exact Or.inr (fun i => by fin_cases i <;> assumption)
    rcases hall with hallL | hallR
    · apply ihl hrol
      intro x
      have hrx : r.eval x = false := by
        rw [r.eval_congr x x02 (fun i hi => absurd ⟨hallL i, hi⟩ (hdisj' i))]
        exact h02f.2
      have h := heq x
      simp [MForm4.eval, hrx] at h
      exact h
    · apply ihr hror
      intro x
      have hlx : l.eval x = false := by
        rw [l.eval_congr x x02 (fun i hi => absurd ⟨hi, hallR i⟩ (hdisj' i))]
        exact h02f.1
      have h := heq x
      simp [MForm4.eval, hlx] at h
      exact h

inductive MForm9 where
  | const (b : Bool)
  | var (i : Fin 9)
  | and (l r : MForm9)
  | or (l r : MForm9)

def MForm9.eval : MForm9 → (Fin 9 → Bool) → Bool
  | .const b, _ => b
  | .var i, x => x i
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

def MForm9.vars : MForm9 → Finset (Fin 9)
  | .const _ => ∅
  | .var i => {i}
  | .and l r => l.vars ∪ r.vars
  | .or l r => l.vars ∪ r.vars

def MForm9.readOnce : MForm9 → Prop
  | .const _ => True
  | .var _ => True
  | .and l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.vars r.vars
  | .or l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.vars r.vars

def MForm9.restrict4 (base : Fin 9 → Bool) (a b c d : Fin 9) : MForm9 → MForm4
  | .const k => .const k
  | .var i =>
    if i = a then .var 0
    else if i = b then .var 1
    else if i = c then .var 2
    else if i = d then .var 3
    else .const (base i)
  | .and l r => .and (l.restrict4 base a b c d) (r.restrict4 base a b c d)
  | .or l r => .or (l.restrict4 base a b c d) (r.restrict4 base a b c d)

def lift4 (base : Fin 9 → Bool) (a b c d : Fin 9) (y : Fin 4 → Bool) : Fin 9 → Bool :=
  fun i =>
    if i = a then y 0
    else if i = b then y 1
    else if i = c then y 2
    else if i = d then y 3
    else base i

def pick4 (a b c d : Fin 9) : Fin 4 → Fin 9
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d

lemma MForm9.restrict4_eval (base : Fin 9 → Bool) (a b c d : Fin 9) (φ : MForm9) (y : Fin 4 → Bool) :
    (φ.restrict4 base a b c d).eval y = φ.eval (lift4 base a b c d y) := by
  induction φ with
  | const k => rfl
  | var i =>
    simp only [MForm9.restrict4, MForm9.eval, lift4]
    split_ifs <;> rfl
  | and l r ihl ihr => simp [MForm9.restrict4, MForm4.eval, MForm9.eval, ihl, ihr]
  | or l r ihl ihr => simp [MForm9.restrict4, MForm4.eval, MForm9.eval, ihl, ihr]

lemma MForm9.restrict4_vars (base : Fin 9 → Bool) (a b c d : Fin 9)
    (φ : MForm9) (j : Fin 4) (hj : j ∈ (φ.restrict4 base a b c d).vars) :
    pick4 a b c d j ∈ φ.vars := by
  induction φ with
  | const k => simp [MForm9.restrict4, MForm4.vars] at hj
  | var i =>
    simp only [MForm9.restrict4] at hj
    split_ifs at hj with h1 h2 h3 h4
    · simp only [MForm4.vars, Finset.mem_singleton] at hj
      subst hj; subst h1; simp [pick4, MForm9.vars]
    · simp only [MForm4.vars, Finset.mem_singleton] at hj
      subst hj; subst h2; simp [pick4, MForm9.vars]
    · simp only [MForm4.vars, Finset.mem_singleton] at hj
      subst hj; subst h3; simp [pick4, MForm9.vars]
    · simp only [MForm4.vars, Finset.mem_singleton] at hj
      subst hj; subst h4; simp [pick4, MForm9.vars]
    · simp [MForm4.vars] at hj
  | and l r ihl ihr =>
    simp only [MForm9.restrict4, MForm4.vars, Finset.mem_union] at hj
    simp only [MForm9.vars, Finset.mem_union]
    rcases hj with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
  | or l r ihl ihr =>
    simp only [MForm9.restrict4, MForm4.vars, Finset.mem_union] at hj
    simp only [MForm9.vars, Finset.mem_union]
    rcases hj with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

lemma MForm9.restrict4_readOnce (base : Fin 9 → Bool) (a b c d : Fin 9)
    (φ : MForm9) (hro : φ.readOnce) : (φ.restrict4 base a b c d).readOnce := by
  induction φ with
  | const k => trivial
  | var i =>
    simp only [MForm9.restrict4]
    split_ifs <;> trivial
  | and l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    refine ⟨ihl hl, ihr hr, ?_⟩
    rw [Finset.disjoint_left]
    intro j hjl hjr
    have h1 := MForm9.restrict4_vars base a b c d l j hjl
    have h2 := MForm9.restrict4_vars base a b c d r j hjr
    exact Finset.disjoint_left.mp hdisj h1 h2
  | or l r ihl ihr =>
    rcases hro with ⟨hl, hr, hdisj⟩
    refine ⟨ihl hl, ihr hr, ?_⟩
    rw [Finset.disjoint_left]
    intro j hjl hjr
    have h1 := MForm9.restrict4_vars base a b c d l j hjl
    have h2 := MForm9.restrict4_vars base a b c d r j hjr
    exact Finset.disjoint_left.mp hdisj h1 h2

lemma kill_p4 (vFin : Fin 9) (φ : MForm9) (hro : φ.readOnce)
    (heq : ∀ x : Fin 9 → Bool, Restricted x → x vFin = true → φ.eval x = pm3 x)
    (base : Fin 9 → Bool) (a b c d : Fin 9)
    (hspec : ∀ y : Fin 4 → Bool,
      lift4 base a b c d y 0 = false ∧
      lift4 base a b c d y vFin = true ∧
      pm3 (lift4 base a b c d y) = p4fn y) : False := by
  apply not_readOnce_P4 (φ.restrict4 base a b c d) (φ.restrict4_readOnce base a b c d hro)
  intro y
  rw [MForm9.restrict4_eval]
  have hs := hspec y
  rw [heq (lift4 base a b c d y) hs.1 hs.2.1, hs.2.2]

lemma no_readOnce_f8_fix (v : ℕ) (hv : v ∈ V8) (φ : MForm9) (hro : φ.readOnce)
    (heq : ∀ x : Fin 9 → Bool, Restricted x → x ⟨v, by simp [V8] at hv; omega⟩ = true →
      φ.eval x = pm3 x) : False := by
  simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kill_p4 1 φ hro heq (fun i => decide (i = 1 ∨ i = 3 ∨ i = 4)) 5 6 2 7 (by decide)
  · exact kill_p4 2 φ hro heq (fun i => decide (i = 2 ∨ i = 3 ∨ i = 5)) 4 6 1 8 (by decide)
  · exact kill_p4 3 φ hro heq (fun i => decide (i = 1 ∨ i = 3 ∨ i = 4)) 5 6 2 7 (by decide)
  · exact kill_p4 4 φ hro heq (fun i => decide (i = 1 ∨ i = 3 ∨ i = 4)) 5 6 2 7 (by decide)
  · exact kill_p4 5 φ hro heq (fun i => decide (i = 2 ∨ i = 3 ∨ i = 5)) 4 6 1 8 (by decide)
  · exact kill_p4 6 φ hro heq (fun i => decide (i = 1 ∨ i = 6 ∨ i = 7)) 4 2 3 8 (by decide)
  · exact kill_p4 7 φ hro heq (fun i => decide (i = 1 ∨ i = 4 ∨ i = 7)) 6 2 3 8 (by decide)
  · exact kill_p4 8 φ hro heq (fun i => decide (i = 2 ∨ i = 5 ∨ i = 8)) 6 1 3 7 (by decide)

section ClassicalPart

open Classical

noncomputable def src (C : Circuit) (w : ℕ) : ℕ :=
  if h : 9 ≤ w ∧ w - 9 < C.gates.length then
    let j : Fin C.gates.length := ⟨w - 9, h.2⟩
    let g := C.gates.get j
    if ¬ IsConst C w then
      match g.inputs with
      | [a, b] =>
        if _ha : a < w ∧ b < w ∧ IsConst C a ∧ ¬ IsConst C b then src C b
        else if _hb : a < w ∧ b < w ∧ IsConst C b ∧ ¬ IsConst C a then src C a
        else w
      | _ => w
    else w
  else w
termination_by w

lemma wireVal_not_const_and {C : Circuit} (a b : ℕ)
    (ha : IsConst C a) (hnc : ¬ ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
      (wireVal C x a && wireVal C x b) = (wireVal C y a && wireVal C y b)) :
    ∀ x : Fin 9 → Bool, Restricted x → wireVal C x a = true := by
  intro x hx
  by_contra hfalse
  have hxa : wireVal C x a = false := by cases h : wireVal C x a <;> simp_all
  apply hnc
  intro u v hu hv
  have hua : wireVal C u a = false := (ha u x hu hx).trans hxa
  have hva : wireVal C v a = false := (ha v x hv hx).trans hxa
  simp [hua, hva]

lemma wireVal_not_const_or {C : Circuit} (a b : ℕ)
    (ha : IsConst C a) (hnc : ¬ ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
      (wireVal C x a || wireVal C x b) = (wireVal C y a || wireVal C y b)) :
    ∀ x : Fin 9 → Bool, Restricted x → wireVal C x a = false := by
  intro x hx
  by_contra htrue
  have hxa : wireVal C x a = true := by cases h : wireVal C x a <;> simp_all
  apply hnc
  intro u v hu hv
  have hua : wireVal C u a = true := (ha u x hu hx).trans hxa
  have hva : wireVal C v a = true := (ha v x hv hx).trans hxa
  simp [hua, hva]

lemma src_props (C : Circuit) (hNF : NormalGate C)
    (h0c : IsConst C 0) (h9c : IsConst C 9) (h10c : IsConst C 10) :
    ∀ w : ℕ, w < 9 + C.gates.length → ¬ IsConst C w →
      src C w ≤ w ∧
      (∀ x : Fin 9 → Bool, Restricted x → wireVal C x w = wireVal C x (src C w)) ∧
      ((src C w < 9 ∧ src C w ≠ 0) ∨
        ∃ j : Fin C.gates.length, 2 ≤ j.val ∧ src C w = 9 + j.val ∧
          ¬ IsConst C (9 + j.val) ∧ ∀ i ∈ (C.gates.get j).inputs, ¬ IsConst C i) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hnc
    by_cases hge : 9 ≤ w
    · have hjlt : w - 9 < C.gates.length := by omega
      let j : Fin C.gates.length := ⟨w - 9, hjlt⟩
      have hwj : 9 + j.val = w := by simp [j]; omega
      have hj2 : 2 ≤ j.val := by
        by_contra hlt2
        have : j.val = 0 ∨ j.val = 1 := by omega
        rcases this with h0 | h1
        · have : w = 9 := by omega
          exact hnc (this ▸ h9c)
        · have : w = 10 := by omega
          exact hnc (this ▸ h10c)
      have hgate_eq : ∀ x : Fin 9 → Bool,
          wireVal C x w = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wireVal C x)) := by
        intro x
        rw [← hwj]
        exact wireVal_gate C x j (normal_inputs_lt hNF j)
      rcases hNF j with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
      · have hanc : ¬ IsConst C a := by
          intro hac
          apply hnc
          intro x y hx hy
          rw [hgate_eq x, hgate_eq y, hop, hin]
          simp [GateOp.eval, hac x y hx hy]
        have hsrc : src C w = w := by
          rw [src]
          simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
          have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a] := hin
          rw [hgin]
        rw [hsrc]
        refine ⟨le_refl w, fun _ _ => rfl, Or.inr ⟨j, hj2, hwj.symm, hwj.symm ▸ hnc, ?_⟩⟩
        intro i hi; rw [hin] at hi; simp at hi; exact hi ▸ hanc
      · have haw : a < w := by omega
        have hbw : b < w := by omega
        have hnotboth : ¬ (IsConst C a ∧ IsConst C b) := by
          rintro ⟨hac, hbc⟩
          apply hnc
          intro x y hx hy
          rw [hgate_eq x, hgate_eq y, hin]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, hac x y hx hy, hbc x y hx hy]
        by_cases hac : IsConst C a
        · have hbnc : ¬ IsConst C b := fun hbc => hnotboth ⟨hac, hbc⟩
          have hsrc : src C w = src C b := by
            rw [src]
            simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
            have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a, b] := hin
            rw [hgin]
            simp [haw, hbw, hac, hbnc]
          have hih := ih b hbw (by omega) hbnc
          rw [hsrc]
          refine ⟨le_trans hih.1 (le_of_lt hbw), ?_, hih.2.2⟩
          intro x hx
          rw [← hih.2.1 x hx, hgate_eq x, hin]
          rcases hop with hop | hop
          · rw [hop]
            have hat : wireVal C x a = true := wireVal_not_const_and a b hac (by
              intro hcon; apply hnc; intro u v hu hv
              rw [hgate_eq u, hgate_eq v, hop, hin]
              simpa [GateOp.eval] using hcon u v hu hv) x hx
            simp [GateOp.eval, hat]
          · rw [hop]
            have haf : wireVal C x a = false := wireVal_not_const_or a b hac (by
              intro hcon; apply hnc; intro u v hu hv
              rw [hgate_eq u, hgate_eq v, hop, hin]
              simpa [GateOp.eval] using hcon u v hu hv) x hx
            simp [GateOp.eval, haf]
        · by_cases hbc : IsConst C b
          · have hsrc : src C w = src C a := by
              rw [src]
              simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
              have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a, b] := hin
              rw [hgin]
              simp [haw, hbw, hac, hbc]
            have hih := ih a haw (by omega) hac
            rw [hsrc]
            refine ⟨le_trans hih.1 (le_of_lt haw), ?_, hih.2.2⟩
            intro x hx
            rw [← hih.2.1 x hx, hgate_eq x, hin]
            rcases hop with hop | hop
            · rw [hop]
              have hbt : wireVal C x b = true := wireVal_not_const_and b a hbc (by
                intro hcon; apply hnc; intro u v hu hv
                rw [hgate_eq u, hgate_eq v, hop, hin]
                simpa [GateOp.eval, Bool.and_comm] using hcon u v hu hv) x hx
              simp [GateOp.eval, hbt]
            · rw [hop]
              have hbf : wireVal C x b = false := wireVal_not_const_or b a hbc (by
                intro hcon; apply hnc; intro u v hu hv
                rw [hgate_eq u, hgate_eq v, hop, hin]
                simpa [GateOp.eval, Bool.or_comm] using hcon u v hu hv) x hx
              simp [GateOp.eval, hbf]
          · have hsrc : src C w = w := by
              rw [src]
              simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
              have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a, b] := hin
              rw [hgin]
              simp [hac, hbc]
            rw [hsrc]
            refine ⟨le_refl w, fun _ _ => rfl, Or.inr ⟨j, hj2, hwj.symm, hwj.symm ▸ hnc, ?_⟩⟩
            intro i hi; rw [hin] at hi; simp at hi
            rcases hi with rfl | rfl
            · exact hac
            · exact hbc
    · have hw9 : w < 9 := by omega
      have hsrc : src C w = w := by rw [src]; simp [hge]
      rw [hsrc]
      refine ⟨le_refl w, fun _ _ => rfl, Or.inl ⟨hw9, ?_⟩⟩
      intro h0; exact hnc (h0 ▸ h0c)

lemma sum_count_eq_length (W : Finset ℕ) (L : List ℕ) (hL : ∀ u ∈ L, u ∈ W) :
    ∑ w ∈ W, L.count w = L.length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : a ∈ W := hL a (List.mem_cons_self ..)
    have ht : ∀ u ∈ t, u ∈ W := fun u hu => hL u (List.mem_cons_of_mem a hu)
    simp only [List.count_cons, List.length_cons]
    have hsplit : ∑ w ∈ W, (t.count w + if a == w then 1 else 0) =
        (∑ w ∈ W, t.count w) + ∑ w ∈ W, (if a == w then 1 else 0) :=
      Finset.sum_add_distrib
    rw [hsplit, ih ht]
    have h1 : ∑ w ∈ W, (if a == w then 1 else 0) = 1 := by
      have heq : (fun w => if a == w then (1 : ℕ) else 0) = (fun w => if w = a then 1 else 0) := by
        ext w
        by_cases h : w = a
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [heq, Finset.sum_ite_eq' W a (fun _ => (1 : ℕ))]
      simp [ha]
    omega

noncomputable def reachW (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) (w : ℕ) : Finset ℕ :=
  if h : 9 ≤ w ∧ w - 9 < C.gates.length then
    let k : Fin C.gates.length := ⟨w - 9, h.2⟩
    if k ∈ R then
      insert w (((inSrc k).filter (· < w)).toFinset.attach.biUnion fun ⟨u, _⟩ => reachW C R inSrc u)
    else {w}
  else {w}
termination_by w
decreasing_by
  have hm := List.mem_toFinset.mp (Finset.mem_coe.mp ‹_›)
  exact of_decide_eq_true (List.mem_filter.mp hm).2

lemma reachW_eq (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) (w : ℕ) :
    reachW C R inSrc w =
      if h : 9 ≤ w ∧ w - 9 < C.gates.length then
        if (⟨w - 9, h.2⟩ : Fin C.gates.length) ∈ R then
          insert w (((inSrc ⟨w - 9, h.2⟩).filter (· < w)).toFinset.biUnion fun u => reachW C R inSrc u)
        else {w}
      else {w} := by
  conv_lhs => rw [reachW]
  dsimp only
  split_ifs with h1 h2
  · congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, exists_prop]
  · rfl
  · rfl

lemma mem_reachW_self (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) (w : ℕ) :
    w ∈ reachW C R inSrc w := by
  rw [reachW_eq]
  split_ifs <;> simp

lemma reachW_le (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) :
    ∀ w u : ℕ, u ∈ reachW C R inSrc w → u ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    rw [reachW_eq] at hu
    split_ifs at hu with h1 h2
    · simp only [Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq] at hu
      rcases hu with rfl | ⟨v, ⟨_, hlt⟩, huv⟩
      · exact le_refl _
      · exact le_trans (ih v hlt u huv) (le_of_lt hlt)
    · simp only [Finset.mem_singleton] at hu; omega
    · simp only [Finset.mem_singleton] at hu; omega

lemma reachW_gate (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) (k : Fin C.gates.length) (hk : k ∈ R)
    (hlt : ∀ u ∈ inSrc k, u < 9 + k.val) :
    reachW C R inSrc (9 + k.val) =
      insert (9 + k.val) ((inSrc k).toFinset.biUnion fun u => reachW C R inSrc u) := by
  rw [reachW_eq]
  have h1 : 9 ≤ 9 + k.val ∧ (9 + k.val) - 9 < C.gates.length := ⟨by omega, by simp [k.isLt]⟩
  have hk' : (⟨(9 + k.val) - 9, h1.2⟩ : Fin C.gates.length) = k := Fin.ext (by simp)
  rw [dif_pos h1]
  simp only [hk', hk, ite_true]
  congr 1
  have hfilt : (inSrc k).filter (· < 9 + k.val) = inSrc k :=
    List.filter_eq_self.mpr (fun u hu => decide_eq_true (hlt u hu))
  rw [hfilt]

lemma reachW_lt9 (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) (w : ℕ) (hw : w < 9) :
    reachW C R inSrc w = {w} := by
  rw [reachW_eq]
  have h : ¬ (9 ≤ w ∧ w - 9 < C.gates.length) := by omega
  rw [dif_neg h]

noncomputable def buildForm (C : Circuit) (R : Finset (Fin C.gates.length))
    (inSrc : Fin C.gates.length → List ℕ) (v : ℕ) (w : ℕ) : MForm9 :=
  if h : 9 ≤ w ∧ w - 9 < C.gates.length then
    let k : Fin C.gates.length := ⟨w - 9, h.2⟩
    if k ∈ R then
      match inSrc k with
      | [a, b] =>
        if _hab : a < w ∧ b < w then
          if (C.gates.get k).op = GateOp.and then
            .and (buildForm C R inSrc v a) (buildForm C R inSrc v b)
          else
            .or (buildForm C R inSrc v a) (buildForm C R inSrc v b)
        else .const false
      | _ => .const false
    else .const false
  else if h9 : w < 9 then
    if w = v then .const true else .var ⟨w, h9⟩
  else .const false
termination_by w

lemma main_proof :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
        C.output + 1 = 9 + C.size ∧
        NormalGate C ∧
        (∀ j : Fin C.gates.length,
          (∃ x y : Fin 9 → Bool,
            (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
          ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
            (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
        (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
          ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
        C.gates.head? = some ⟨GateOp.not, [0]⟩ ∧
        C.gates.tail.head? = some ⟨GateOp.or, [4, 9]⟩) := by
  rintro ⟨C, _, hSize, hEval, hOut, hNF, _, hUse, hHead, hTail⟩
  have hLenLe : C.gates.length ≤ 12 := hSize
  cases hgs : C.gates with
  | nil => simp [hgs] at hHead
  | cons g0 rest =>
    rw [hgs] at hHead hTail
    simp only [List.head?_cons, Option.some.injEq] at hHead
    cases rest with
    | nil => simp at hTail
    | cons g1 rest2 =>
      simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hTail
      have hLenGe2 : 2 ≤ C.gates.length := by rw [hgs]; simp
      have hg0 : C.gates.get ⟨0, by omega⟩ = ⟨GateOp.not, [0]⟩ := by simp [hgs, hHead]
      have hg1 : C.gates.get ⟨1, by omega⟩ = ⟨GateOp.or, [4, 9]⟩ := by simp [hgs, hTail]
      have hEvalWire : ∀ x : Fin 9 → Bool, wireVal C x C.output = pm3 x := fun x => hEval x
      have hOutEq : C.output = 9 + (C.gates.length - 1) := by
        change C.output + 1 = 9 + C.gates.length at hOut
        omega
      have hW9 : ∀ x : Fin 9 → Bool, wireVal C x 9 = !(x 0) := by
        intro x
        have h := wireVal_gate C x ⟨0, by omega⟩ (normal_inputs_lt hNF ⟨0, by omega⟩)
        rw [hg0] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil] at h
        rw [wireVal_nat C x 0 (by omega)] at h
        exact h
      have hW10 : ∀ x : Fin 9 → Bool, wireVal C x 10 = (x 4 || !(x 0)) := by
        intro x
        have h := wireVal_gate C x ⟨1, by omega⟩ (normal_inputs_lt hNF ⟨1, by omega⟩)
        rw [hg1] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          Bool.or_false, id_eq] at h
        rw [wireVal_nat C x 4 (by omega), hW9 x] at h
        exact h
      have hLenGt2 : 2 < C.gates.length := by
        by_contra hle2
        have heq2 : C.gates.length = 2 := by omega
        have hout10 : C.output = 10 := by omega
        let xw : Fin 9 → Bool := fun _ => false
        have h1 := hEvalWire xw
        rw [hout10, hW10 xw] at h1
        have h2 : (xw 4 || !(xw 0)) = true := by decide
        have h3 : pm3 xw = false := by decide
        rw [h2, h3] at h1
        exact Bool.false_ne_true h1.symm
      have h0c : IsConst C 0 := by
        intro x y hx hy
        rw [wireVal_nat C x 0 (by omega), wireVal_nat C y 0 (by omega)]
        exact hx.trans hy.symm
      have h9c : IsConst C 9 := by
        intro x y hx hy
        rw [hW9 x, hW9 y, hx, hy]
      have h10c : IsConst C 10 := by
        intro x y hx hy
        rw [hW10 x, hW10 y, hx, hy]
        simp
      have hOutNotConst : ¬ IsConst C C.output := by
        intro hcon
        let xa : Fin 9 → Bool := fun _ => false
        let xb : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 3 ∨ i = 8)
        have h1 := hcon xa xb (by rfl) (by rfl)
        rw [hEvalWire xa, hEvalWire xb] at h1
        have h2 : pm3 xa = false := by decide
        have h3 : pm3 xb = true := by decide
        rw [h2, h3] at h1
        exact Bool.false_ne_true h1
      have hUse10 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 10 ∈ (C.gates.get k).inputs := by
        obtain ⟨k, hkgt, hkmem⟩ := hUse ⟨1, by omega⟩ (show 1 + 1 < C.gates.length by omega)
        dsimp only at hkgt hkmem
        exact ⟨k, by omega, hkmem⟩
      have hUse0or9 : ∃ w : ℕ, (w = 0 ∨ w = 9) ∧ ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ w ∈ (C.gates.get k).inputs := by
        by_contra hno
        push Not at hno
        have hno0 : ∀ k : Fin C.gates.length, 2 ≤ k.val → 0 ∉ (C.gates.get k).inputs :=
          fun k hk => hno 0 (Or.inl rfl) k hk
        have hno9 : ∀ k : Fin C.gates.length, 2 ≤ k.val → 9 ∉ (C.gates.get k).inputs :=
          fun k hk => hno 9 (Or.inr rfl) k hk
        let x0 : Fin 9 → Bool := fun i => decide (i = 4 ∨ i = 8)
        let x1 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4 ∨ i = 8)
        have hall : ∀ w : ℕ, w < 9 + C.gates.length → w ≠ 0 → w ≠ 9 → wireVal C x0 w = wireVal C x1 w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hlt hne0 hne9
            by_cases h9 : w < 9
            · rw [wireVal_nat C x0 w h9, wireVal_nat C x1 w h9]
              have hne' : (⟨w, h9⟩ : Fin 9) ≠ 0 := fun h => hne0 (congrArg Fin.val h)
              simp [x0, x1, hne']
            · by_cases hw10 : w = 10
              · rw [hw10, hW10 x0, hW10 x1]; decide
              · let k : Fin C.gates.length := ⟨w - 9, by omega⟩
                have hwk : 9 + k.val = w := by simp [k]; omega
                have hk2 : 2 ≤ k.val := by simp [k]; omega
                rw [← hwk, wireVal_gate C x0 k (normal_inputs_lt hNF k),
                  wireVal_gate C x1 k (normal_inputs_lt hNF k)]
                congr 1
                apply List.map_congr_left
                intro a ha
                have halt : a < w := by rw [← hwk]; exact normal_inputs_lt hNF k a ha
                have hane0 : a ≠ 0 := fun h0 => hno0 k hk2 (h0 ▸ ha)
                have hane9 : a ≠ 9 := fun h9' => hno9 k hk2 (h9' ▸ ha)
                exact ih a halt (by omega) hane0 hane9
        have hEqOut := hall C.output (by omega) (by omega) (by omega)
        rw [hEvalWire x0, hEvalWire x1] at hEqOut
        have h2 : pm3 x0 = false := by decide
        have h3 : pm3 x1 = true := by decide
        rw [h2, h3] at hEqOut
        exact Bool.false_ne_true hEqOut
      obtain ⟨w0, hw0_or, hw0_use⟩ := hUse0or9
      let G2 : Finset (Fin C.gates.length) := Finset.univ.filter fun j => 2 ≤ j.val
      let Gconst : Finset (Fin C.gates.length) := G2.filter fun j => IsConst C (9 + j.val)
      let Gpass : Finset (Fin C.gates.length) := G2.filter fun j =>
        ¬ IsConst C (9 + j.val) ∧ ∃ a ∈ (C.gates.get j).inputs, IsConst C a
      let Grem : Finset (Fin C.gates.length) := G2.filter fun j =>
        ¬ IsConst C (9 + j.val) ∧ ∀ a ∈ (C.gates.get j).inputs, ¬ IsConst C a
      have hG2_card : G2.card = C.gates.length - 2 := by
        have hcompl : G2 = Finset.univ \ {⟨0, by omega⟩, ⟨1, by omega⟩} := by
          ext j
          simp only [G2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
            Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          omega
        have hpair : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)).card = 2 := by
          rw [Finset.card_pair]
          intro h
          have := congrArg Fin.val h
          simp at this
        rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hpair]
      have hPart : Gconst.card + Gpass.card + Grem.card = G2.card := by
        have h1 : Disjoint Gconst Gpass := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Gconst, Gpass, Finset.mem_filter] at hj1 hj2
          exact hj2.2.1 hj1.2
        have h2 : Disjoint (Gconst ∪ Gpass) Grem := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Finset.mem_union, Gconst, Gpass, Grem, Finset.mem_filter] at hj1 hj2
          rcases hj1 with hj1 | hj1
          · exact hj2.2.1 hj1.2
          · obtain ⟨a, ha, hac⟩ := hj1.2.2
            exact hj2.2.2 a ha hac
        have hunion : (Gconst ∪ Gpass) ∪ Grem = G2 := by
          ext j
          simp only [Finset.mem_union, Gconst, Gpass, Grem, Finset.mem_filter]
          constructor
          · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
          · intro hj
            by_cases hc : IsConst C (9 + j.val)
            · exact Or.inl (Or.inl ⟨hj, hc⟩)
            · by_cases hex : ∃ a ∈ (C.gates.get j).inputs, IsConst C a
              · exact Or.inl (Or.inr ⟨hj, hc, hex⟩)
              · push Not at hex
                exact Or.inr ⟨hj, hc, hex⟩
        rw [← hunion, Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1]
      let K0 : Finset ℕ := {w0, 10}
      let S : Finset ℕ := K0 ∪ Gconst.image fun j => 9 + j.val
      have hS_card : S.card = 2 + Gconst.card := by
        have hdisj : Disjoint K0 (Gconst.image fun j => 9 + j.val) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Finset.mem_image, Gconst, G2, Finset.mem_filter] at hw2
          obtain ⟨j, ⟨⟨_, hj2⟩, _⟩, rfl⟩ := hw2
          simp only [K0, Finset.mem_insert, Finset.mem_singleton] at hw1
          rcases hw0_or with rfl | rfl <;> omega
        have hK0 : K0.card = 2 := by
          rw [Finset.card_pair]
          rcases hw0_or with rfl | rfl <;> omega
        have hinj : Set.InjOn (fun j : Fin C.gates.length => 9 + j.val) ↑Gconst := by
          intro a _ b _ hab
          dsimp only at hab
          exact Fin.ext (by omega)
        rw [Finset.card_union_of_disjoint hdisj, hK0, Finset.card_image_of_injOn hinj]
      have hS_const : ∀ w ∈ S, IsConst C w := by
        intro w hw
        simp only [S, K0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Gconst, Finset.mem_filter] at hw
        rcases hw with (rfl | rfl) | ⟨j, ⟨_, hcj⟩, rfl⟩
        · rcases hw0_or with rfl | rfl
          · exact h0c
          · exact h9c
        · exact h10c
        · exact hcj
      have hS_used : ∀ w ∈ S, ∃ k ∈ G2, w ∈ (C.gates.get k).inputs := by
        intro w hw
        simp only [S, K0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Gconst, G2, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rcases hw with (rfl | rfl) | ⟨j, ⟨hj2, hcj⟩, rfl⟩
        · exact hw0_use
        · exact hUse10
        · have hjlt : j.val + 1 < C.gates.length := by
            by_contra hge
            have hlast : 9 + j.val = C.output := by omega
            exact hOutNotConst (hlast ▸ hcj)
          obtain ⟨k, hkgt, hkmem⟩ := hUse j hjlt
          exact ⟨k, by omega, hkmem⟩
      let E : Finset (ℕ × Fin C.gates.length) :=
        (S ×ˢ G2).filter fun p => p.1 ∈ (C.gates.get p.2).inputs
      have hE_ge : S.card ≤ E.card := by
        have hsub : S ⊆ E.image Prod.fst := by
          intro w hw
          obtain ⟨k, hk, hmem⟩ := hS_used w hw
          refine Finset.mem_image.mpr ⟨(w, k), ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw, hk⟩, hmem⟩
        exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have hE_le : E.card ≤ 2 * Gconst.card + Gpass.card := by
        have hsub : E ⊆ (Gconst ∪ Gpass).biUnion fun k =>
            (S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k) := by
          intro p hp
          simp only [E, Finset.mem_filter, Finset.mem_product] at hp
          rcases hp with ⟨⟨hwS, hkG2⟩, hmem⟩
          rw [Finset.mem_biUnion]
          refine ⟨p.2, ?_, ?_⟩
          · rw [Finset.mem_union]
            by_cases hc : IsConst C (9 + p.2.val)
            · exact Or.inl (Finset.mem_filter.mpr ⟨hkG2, hc⟩)
            · exact Or.inr (Finset.mem_filter.mpr ⟨hkG2, hc, p.1, hmem, hS_const p.1 hwS⟩)
          · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨hwS, hmem⟩, rfl⟩
        have h1 := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        have hdisj_cp : Disjoint Gconst Gpass := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Gconst, Gpass, Finset.mem_filter] at hj1 hj2
          exact hj2.2.1 hj1.2
        rw [Finset.sum_union hdisj_cp] at h1
        have hc_bound : ∑ k ∈ Gconst,
            ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card ≤
            2 * Gconst.card := by
          calc ∑ k ∈ Gconst,
                ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
              ≤ ∑ k ∈ Gconst, 2 := by
                apply Finset.sum_le_sum
                intro k _
                calc ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
                    ≤ (S.filter fun w => w ∈ (C.gates.get k).inputs).card := Finset.card_image_le
                  _ ≤ (C.gates.get k).inputs.toFinset.card := by
                      apply Finset.card_le_card
                      intro w hw
                      simp only [Finset.mem_filter] at hw
                      exact List.mem_toFinset.mpr hw.2
                  _ ≤ (C.gates.get k).inputs.length := List.toFinset_card_le _
                  _ ≤ 2 := normal_inputs_len hNF k
            _ = 2 * Gconst.card := by simp [Nat.mul_comm]
        have hp_bound : ∑ k ∈ Gpass,
            ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card ≤
            Gpass.card := by
          calc ∑ k ∈ Gpass,
                ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
              ≤ ∑ k ∈ Gpass, 1 := by
                apply Finset.sum_le_sum
                intro k hk
                calc ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
                    ≤ (S.filter fun w => w ∈ (C.gates.get k).inputs).card := Finset.card_image_le
                  _ ≤ 1 := by
                      rw [Finset.card_le_one]
                      intro w1 hw1 w2 hw2
                      simp only [Finset.mem_filter] at hw1 hw2
                      simp only [Gpass, Finset.mem_filter] at hk
                      have hwc1 : IsConst C w1 := hS_const w1 hw1.1
                      have hwc2 : IsConst C w2 := hS_const w2 hw2.1
                      rcases hNF k with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
                      · rw [hin] at hw1 hw2; simp at hw1 hw2; omega
                      · rw [hin] at hw1 hw2; simp at hw1 hw2
                        by_contra hne
                        have hboth : IsConst C a ∧ IsConst C b := by
                          rcases hw1.2 with rfl | rfl <;> rcases hw2.2 with rfl | rfl
                          · exact absurd rfl hne
                          · exact ⟨hwc1, hwc2⟩
                          · exact ⟨hwc2, hwc1⟩
                          · exact absurd rfl hne
                        apply hk.2.1
                        intro x y hx hy
                        rw [wireVal_gate C x k (normal_inputs_lt hNF k),
                          wireVal_gate C y k (normal_inputs_lt hNF k), hin]
                        rcases hop with hop | hop <;> rw [hop] <;>
                          simp [GateOp.eval, hboth.1 x y hx hy, hboth.2 x y hx hy]
            _ = Gpass.card := by simp
        omega
      have hGrem_le8 : Grem.card ≤ 8 := by omega
      have hSrcAll := src_props C hNF h0c h9c h10c
      have hOutSrc := hSrcAll C.output (by omega) hOutNotConst
      have hOutInGrem : ∃ jout ∈ Grem, src C C.output = 9 + jout.val := by
        rcases hOutSrc.2.2 with ⟨hlt9, hne0⟩ | ⟨j, hj2, hjeq, hjnc, hjins⟩
        · exfalso
          have hother : ∃ v ∈ V8, v ≠ src C C.output := by
            by_cases h1 : src C C.output = 1
            · exact ⟨2, by decide, by omega⟩
            · exact ⟨1, by decide, by omega⟩
          obtain ⟨v, hvV8, hvne⟩ := hother
          obtain ⟨x, y, hx, hy, hagree, hdiff⟩ := V8_essential v hvV8
          apply hdiff
          rw [← hEvalWire x, ← hEvalWire y, hOutSrc.2.1 x hx, hOutSrc.2.1 y hy]
          rw [wireVal_nat C x (src C C.output) hlt9, wireVal_nat C y (src C C.output) hlt9]
          exact hagree ⟨src C C.output, hlt9⟩ (by simpa using hvne.symm)
        · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj2⟩, hjnc, hjins⟩, hjeq⟩
      obtain ⟨jout, hjoutGrem, hjoutEq⟩ := hOutInGrem
      let inSrc (k : Fin C.gates.length) : List ℕ := (C.gates.get k).inputs.map (src C)
      let ClosedSets : Finset (Finset (Fin C.gates.length)) :=
        Grem.powerset.filter fun R => jout ∈ R ∧ ∀ k ∈ R, ∀ j ∈ Grem, 9 + j.val ∈ inSrc k → j ∈ R
      have hGremMem : Grem ∈ ClosedSets := by
        simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.Subset.refl _, hjoutGrem, fun _ _ j hj _ => hj⟩
      obtain ⟨R, hRmem, hRmin⟩ := Finset.exists_min_image ClosedSets Finset.card ⟨Grem, hGremMem⟩
      simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset] at hRmem
      rcases hRmem with ⟨hRsub, hjoutR, hRclosed⟩
      have hR_le8 : R.card ≤ 8 := le_trans (Finset.card_le_card hRsub) hGrem_le8
      have hR_pos : 1 ≤ R.card := Finset.card_pos.mpr ⟨jout, hjoutR⟩
      have hInSrc_props : ∀ k ∈ R, ∀ u ∈ inSrc k,
          u < 9 + k.val ∧ (u ∈ V8 ∨ ∃ j ∈ R, u = 9 + j.val) := by
        intro k hkR u hu
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
        have hkGrem := Finset.mem_filter.mp (hRsub hkR)
        have halt : a < 9 + k.val := normal_inputs_lt hNF k a ha
        have hsp := hSrcAll a (by omega) (hkGrem.2.2 a ha)
        refine ⟨by omega, ?_⟩
        rcases hsp.2.2 with ⟨hlt9, hne0⟩ | ⟨j, hj2, hjeq, hjnc, hjins⟩
        · left; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; omega
        · right
          have hjGrem : j ∈ Grem :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj2⟩, hjnc, hjins⟩
          exact ⟨j, hRclosed k hkR j hjGrem (hjeq ▸ List.mem_map.mpr ⟨a, ha, rfl⟩), hjeq⟩
      have hR_le_jout : ∀ k ∈ R, k.val ≤ jout.val := by
        let R' := R.filter fun k => k.val ≤ jout.val
        have hR'mem : R' ∈ ClosedSets := by
          simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.Subset.trans (Finset.filter_subset _ R) hRsub,
            Finset.mem_filter.mpr ⟨hjoutR, le_refl _⟩, ?_⟩
          intro k hk j hj hmem
          have hk' := Finset.mem_filter.mp hk
          have hjR := hRclosed k hk'.1 j hj hmem
          have hlt := (hInSrc_props k hk'.1 (9 + j.val) hmem).1
          exact Finset.mem_filter.mpr ⟨hjR, by omega⟩
        have hcard := hRmin R' hR'mem
        have hsub' : R' ⊆ R := Finset.filter_subset _ R
        have heqR : R' = R := Finset.eq_of_subset_of_card_le hsub' hcard
        intro k hk
        have : k ∈ R' := heqR ▸ hk
        exact (Finset.mem_filter.mp this).2
      have hR_used : ∀ j ∈ R.erase jout, ∃ k ∈ R, 9 + j.val ∈ inSrc k := by
        intro j hj
        by_contra hno
        push Not at hno
        have hne : j ≠ jout := (Finset.mem_erase.mp hj).1
        have hjR : j ∈ R := (Finset.mem_erase.mp hj).2
        have hErMem : R.erase j ∈ ClosedSets := by
          simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.Subset.trans (Finset.erase_subset j R) hRsub,
            Finset.mem_erase.mpr ⟨hne.symm, hjoutR⟩, ?_⟩
          intro k hk j' hj' hmem
          have hkR : k ∈ R := (Finset.mem_erase.mp hk).2
          have hj'R : j' ∈ R := hRclosed k hkR j' hj' hmem
          have hj'ne : j' ≠ j := fun heq => hno k hkR (heq ▸ hmem)
          exact Finset.mem_erase.mpr ⟨hj'ne, hj'R⟩
        have hcard := hRmin (R.erase j) hErMem
        have hlt : (R.erase j).card < R.card := Finset.card_erase_lt_of_mem hjR
        omega
      have hV8_used : ∀ v ∈ V8, ∃ k ∈ R, v ∈ inSrc k := by
        intro v hvV8
        by_contra hno
        push Not at hno
        obtain ⟨x, y, hx, hy, hagree, hdiff⟩ := V8_essential v hvV8
        have hallR : ∀ n : ℕ, ∀ k ∈ R, k.val = n → wireVal C x (9 + k.val) = wireVal C y (9 + k.val) := by
          intro n
          induction n using Nat.strong_induction_on with
          | ind n ih =>
            intro k hkR hkn
            have hkGrem' := Finset.mem_filter.mp (hRsub hkR)
            rw [wireVal_gate C x k (normal_inputs_lt hNF k),
              wireVal_gate C y k (normal_inputs_lt hNF k)]
            congr 1
            apply List.map_congr_left
            intro a ha
            have halt : a < 9 + k.val := normal_inputs_lt hNF k a ha
            have hsp := hSrcAll a (by omega) (hkGrem'.2.2 a ha)
            rw [hsp.2.1 x hx, hsp.2.1 y hy]
            have hmemIn : src C a ∈ inSrc k := List.mem_map.mpr ⟨a, ha, rfl⟩
            rcases hsp.2.2 with ⟨hlt9, _⟩ | ⟨j, hj2, hjeq, hjnc, hjins⟩
            · have hne : src C a ≠ v := fun heq => hno k hkR (heq ▸ hmemIn)
              rw [wireVal_nat C x (src C a) hlt9, wireVal_nat C y (src C a) hlt9]
              exact hagree ⟨src C a, hlt9⟩ hne
            · have hjGrem : j ∈ Grem :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj2⟩, hjnc, hjins⟩
              have hjR : j ∈ R := hRclosed k hkR j hjGrem (hjeq ▸ hmemIn)
              have hjlt : j.val < n := by have := hsp.1; omega
              rw [hjeq]
              exact ih j.val hjlt j hjR rfl
        apply hdiff
        rw [← hEvalWire x, ← hEvalWire y, hOutSrc.2.1 x hx, hOutSrc.2.1 y hy, hjoutEq]
        exact hallR jout.val jout hjoutR rfl
      let Wset : Finset ℕ := V8 ∪ (R.erase jout).image fun j => 9 + j.val
      have hW_card : Wset.card = 8 + (R.card - 1) := by
        have hdisj : Disjoint V8 ((R.erase jout).image fun j => 9 + j.val) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Finset.mem_image] at hw2
          obtain ⟨j, _, rfl⟩ := hw2
          simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hw1
          omega
        have hinj : Set.InjOn (fun j : Fin C.gates.length => 9 + j.val) ↑(R.erase jout) := by
          intro a _ b _ hab; dsimp only at hab; exact Fin.ext (by omega)
        rw [Finset.card_union_of_disjoint hdisj, V8_card,
          Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hjoutR]
      have hInSrc_sub : ∀ k ∈ R, ∀ u ∈ inSrc k, u ∈ Wset := by
        intro k hkR u hu
        obtain ⟨hult, hor⟩ := hInSrc_props k hkR u hu
        rcases hor with huV8 | ⟨j, hjR, rfl⟩
        · exact Finset.mem_union_left _ huV8
        · have hkj := hR_le_jout k hkR
          have hjne : j ≠ jout := fun heq => by subst heq; omega
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjne, hjR⟩, rfl⟩)
      let deg (w : ℕ) : ℕ := ∑ k ∈ R, (inSrc k).count w
      have hdeg_pos : ∀ w ∈ Wset, 1 ≤ deg w := by
        intro w hw
        have hex : ∃ k ∈ R, w ∈ inSrc k := by
          simp only [Wset, Finset.mem_union, Finset.mem_image] at hw
          rcases hw with hwV8 | ⟨j, hjEr, rfl⟩
          · exact hV8_used w hwV8
          · exact hR_used j hjEr
        obtain ⟨k, hkR, hmem⟩ := hex
        have hpos : 1 ≤ (inSrc k).count w := List.count_pos_iff.mpr hmem
        have hle : (inSrc k).count w ≤ deg w :=
          Finset.single_le_sum (f := fun k' => (inSrc k').count w) (fun _ _ => Nat.zero_le _) hkR
        omega
      let Rnot : Finset (Fin C.gates.length) := R.filter fun k => (C.gates.get k).op = GateOp.not
      have hsum_deg : ∑ w ∈ Wset, deg w = 2 * R.card - Rnot.card := by
        calc ∑ w ∈ Wset, deg w
            = ∑ w ∈ Wset, ∑ k ∈ R, (inSrc k).count w := rfl
          _ = ∑ k ∈ R, ∑ w ∈ Wset, (inSrc k).count w := Finset.sum_comm
          _ = ∑ k ∈ R, (inSrc k).length := by
              apply Finset.sum_congr rfl
              intro k hkR
              exact sum_count_eq_length Wset (inSrc k) (hInSrc_sub k hkR)
          _ = ∑ k ∈ R, (if (C.gates.get k).op = GateOp.not then 1 else 2) := by
              apply Finset.sum_congr rfl
              intro k _
              simp only [inSrc, List.length_map]
              rcases hNF k with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
              · rw [hop, hin]; simp
              · rw [hin]
                rcases hop with hop | hop <;> rw [hop] <;> simp
          _ = 2 * R.card - Rnot.card := by
              have hadd : (∑ k ∈ R, (if (C.gates.get k).op = GateOp.not then 1 else 2)) + Rnot.card =
                  ∑ k ∈ R, 2 := by
                have hRnot : Rnot.card = ∑ k ∈ R, (if (C.gates.get k).op = GateOp.not then 1 else 0) := by
                  unfold Rnot
                  rw [Finset.card_filter]
                rw [hRnot, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro k _
                split_ifs <;> omega
              have h2R : ∑ k ∈ R, (2 : ℕ) = 2 * R.card := by simp [Nat.mul_comm]
              omega
      have hExcess : Rnot.card + ∑ w ∈ Wset, (deg w - 1) ≤ 1 := by
        have hsum_sub : (∑ w ∈ Wset, (deg w - 1)) + Wset.card = ∑ w ∈ Wset, deg w := by
          have h1 : Wset.card = ∑ _w ∈ Wset, (1 : ℕ) := by simp
          rw [h1, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w hw
          have := hdeg_pos w hw
          omega
        have hRnot_le : Rnot.card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ R)
        omega
      have hReach_sub_W : ∀ w : ℕ, (w ∈ V8 ∨ ∃ j ∈ R, w = 9 + j.val) →
          ∀ u ∈ reachW C R inSrc w, u ∈ V8 ∨ ∃ j ∈ R, u = 9 + j.val := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw u hu
          rcases hw with hwV8 | ⟨k, hkR, rfl⟩
          · have hlt9 : w < 9 := by simp [V8] at hwV8; omega
            rw [reachW_lt9 C R inSrc w hlt9, Finset.mem_singleton] at hu
            subst hu; exact Or.inl hwV8
          · rw [reachW_gate C R inSrc k hkR (fun z hz => (hInSrc_props k hkR z hz).1)] at hu
            simp only [Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset] at hu
            rcases hu with rfl | ⟨v, hv, huv⟩
            · exact Or.inr ⟨k, hkR, rfl⟩
            · have hp := hInSrc_props k hkR v hv
              exact ih v hp.1 hp.2 u huv
      have hReach_parent : ∀ w u : ℕ, u ∈ reachW C R inSrc w → u ≠ w →
          ∃ k ∈ R, 9 + k.val ∈ reachW C R inSrc w ∧ u ∈ inSrc k := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro u hu hne
          rw [reachW_eq] at hu
          split_ifs at hu with h1 h2
          · let k0 : Fin C.gates.length := ⟨w - 9, h1.2⟩
            have hwk0 : 9 + k0.val = w := by simp [k0]; omega
            simp only [Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
              decide_eq_true_eq] at hu
            rcases hu with rfl | ⟨v, ⟨hvmem, hvlt⟩, huv⟩
            · exact absurd rfl hne
            · by_cases huv_eq : u = v
              · subst huv_eq
                refine ⟨k0, h2, ?_, hvmem⟩
                rw [hwk0]
                exact mem_reachW_self C R inSrc w
              · obtain ⟨k, hkR, hkreach, hmem⟩ := ih v hvlt u huv huv_eq
                refine ⟨k, hkR, ?_, hmem⟩
                rw [reachW_eq, dif_pos h1, if_pos h2]
                refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v, ?_, hkreach⟩)
                exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hvmem, decide_eq_true hvlt⟩)
          · simp only [Finset.mem_singleton] at hu; exact absurd hu hne
          · simp only [Finset.mem_singleton] at hu; exact absurd hu hne
      have hDisj_of_deg1 : ∀ (k : Fin C.gates.length) (a b excl : ℕ),
          k ∈ R → inSrc k = [a, b] →
          (excl < 9 ∨ 9 + k.val ≤ excl) →
          (∀ w ∈ Wset, w ≠ excl → deg w ≤ 1) →
          Disjoint ((reachW C R inSrc a).erase excl) ((reachW C R inSrc b).erase excl) := by
        intro k a b excl hkR hinK hexcl_out hdeg1
        rw [Finset.disjoint_left]
        intro m0 hm0a hm0b
        let I := ((reachW C R inSrc a).erase excl) ∩ ((reachW C R inSrc b).erase excl)
        have hIne : I.Nonempty := ⟨m0, Finset.mem_inter.mpr ⟨hm0a, hm0b⟩⟩
        obtain ⟨m, hmI, hmMax⟩ := Finset.exists_max_image I id hIne
        have hmA : m ∈ reachW C R inSrc a := (Finset.mem_erase.mp (Finset.mem_inter.mp hmI).1).2
        have hmB : m ∈ reachW C R inSrc b := (Finset.mem_erase.mp (Finset.mem_inter.mp hmI).2).2
        have hmNe : m ≠ excl := (Finset.mem_erase.mp (Finset.mem_inter.mp hmI).1).1
        have haLt : a < 9 + k.val := (hInSrc_props k hkR a (by rw [hinK]; simp)).1
        have hbLt : b < 9 + k.val := (hInSrc_props k hkR b (by rw [hinK]; simp)).1
        have haOr : a ∈ V8 ∨ ∃ j ∈ R, a = 9 + j.val := (hInSrc_props k hkR a (by rw [hinK]; simp)).2
        have hmOr : m ∈ V8 ∨ ∃ j ∈ R, m = 9 + j.val := hReach_sub_W a haOr m hmA
        have hmLtK : m < 9 + k.val := lt_of_le_of_lt (reachW_le C R inSrc a m hmA) haLt
        have hmW : m ∈ Wset := by
          rcases hmOr with h | ⟨j, hjR, rfl⟩
          · exact Finset.mem_union_left _ h
          · have hkj := hR_le_jout k hkR
            have hjne : j ≠ jout := fun heq => by subst heq; omega
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjne, hjR⟩, rfl⟩)
        have hdm : deg m ≤ 1 := hdeg1 m hmW hmNe
        have hdeg_ge2 : 2 ≤ deg m := by
          by_cases hma : m = a
          · by_cases hmb : m = b
            · subst hma
              have hcnt : (inSrc k).count m = 2 := by rw [hinK, hmb]; simp
              have hle : (inSrc k).count m ≤ deg m :=
                Finset.single_le_sum (f := fun k' => (inSrc k').count m) (fun _ _ => Nat.zero_le _) hkR
              omega
            · obtain ⟨k2, hk2R, hk2reach, hmIn2⟩ := hReach_parent b m hmB hmb
              have hk2lt : 9 + k2.val ≤ b := reachW_le C R inSrc b (9 + k2.val) hk2reach
              have hk2ne : k2 ≠ k := fun heq => by subst heq; omega
              have h1 : 1 ≤ (inSrc k).count m := List.count_pos_iff.mpr (by rw [hinK, hma]; simp)
              have h2 : 1 ≤ (inSrc k2).count m := List.count_pos_iff.mpr hmIn2
              have hsum2 : (inSrc k).count m + (inSrc k2).count m ≤ deg m := by
                have hpair : ({k, k2} : Finset (Fin C.gates.length)) ⊆ R := by
                  intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
                have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k' => (inSrc k').count m) hpair (fun _ _ _ => Nat.zero_le _)
                rw [Finset.sum_pair hk2ne.symm] at hle
                exact hle
              omega
          · by_cases hmb : m = b
            · obtain ⟨k1, hk1R, hk1reach, hmIn1⟩ := hReach_parent a m hmA hma
              have hk1lt : 9 + k1.val ≤ a := reachW_le C R inSrc a (9 + k1.val) hk1reach
              have hk1ne : k1 ≠ k := fun heq => by subst heq; omega
              have h1 : 1 ≤ (inSrc k).count m := List.count_pos_iff.mpr (by rw [hinK, hmb]; simp)
              have h2 : 1 ≤ (inSrc k1).count m := List.count_pos_iff.mpr hmIn1
              have hsum2 : (inSrc k).count m + (inSrc k1).count m ≤ deg m := by
                have hpair : ({k, k1} : Finset (Fin C.gates.length)) ⊆ R := by
                  intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
                have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k' => (inSrc k').count m) hpair (fun _ _ _ => Nat.zero_le _)
                rw [Finset.sum_pair hk1ne.symm] at hle
                exact hle
              omega
            · obtain ⟨k1, hk1R, hk1reach, hmIn1⟩ := hReach_parent a m hmA hma
              obtain ⟨k2, hk2R, hk2reach, hmIn2⟩ := hReach_parent b m hmB hmb
              have hk1ne : k1 ≠ k2 := by
                intro heq
                subst heq
                have hgt : m < 9 + k1.val := (hInSrc_props k1 hk1R m hmIn1).1
                have hlt2 : 9 + k1.val < 9 + k.val := lt_of_le_of_lt (reachW_le C R inSrc a _ hk1reach) haLt
                have hexcl : 9 + k1.val ≠ excl := by omega
                have hmemI : 9 + k1.val ∈ I :=
                  Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hexcl, hk1reach⟩,
                    Finset.mem_erase.mpr ⟨hexcl, hk2reach⟩⟩
                have hle := hmMax (9 + k1.val) hmemI
                dsimp only [id] at hle
                omega
              have h1 : 1 ≤ (inSrc k1).count m := List.count_pos_iff.mpr hmIn1
              have h2 : 1 ≤ (inSrc k2).count m := List.count_pos_iff.mpr hmIn2
              have hsum2 : (inSrc k1).count m + (inSrc k2).count m ≤ deg m := by
                have hpair : ({k1, k2} : Finset (Fin C.gates.length)) ⊆ R := by
                  intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
                have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k' => (inSrc k').count m) hpair (fun _ _ _ => Nat.zero_le _)
                rw [Finset.sum_pair hk1ne] at hle
                exact hle
              omega
        omega
      by_cases hCaseB : ∃ v ∈ V8, 2 ≤ deg v
      · obtain ⟨v, hvV8, hdegv⟩ := hCaseB
        have hvW : v ∈ Wset := Finset.mem_union_left _ hvV8
        have hv_sub : deg v - 1 ≤ ∑ w ∈ Wset, (deg w - 1) :=
          Finset.single_le_sum (f := fun w => deg w - 1) (fun _ _ => Nat.zero_le _) hvW
        have hRnot0 : Rnot.card = 0 := by omega
        have hdeg1 : ∀ w ∈ Wset, w ≠ v → deg w ≤ 1 := by
          intro w hw hne
          have hpair : ({v, w} : Finset ℕ) ⊆ Wset := by
            intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun w => deg w - 1) hpair (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hne.symm] at hle
          omega
        have hNoNot : ∀ k ∈ R, (C.gates.get k).op = GateOp.and ∨ (C.gates.get k).op = GateOp.or := by
          intro k hkR
          rcases hNF k with ⟨hop, _⟩ | ⟨hop, _⟩
          · exfalso
            have hkNot : k ∈ Rnot := Finset.mem_filter.mpr ⟨hkR, hop⟩
            have hpos : 0 < Rnot.card := Finset.card_pos.mpr ⟨k, hkNot⟩
            omega
          · exact hop
        have hBinIn : ∀ k ∈ R, ∃ a b, inSrc k = [a, b] ∧ a < 9 + k.val ∧ b < 9 + k.val := by
          intro k hkR
          rcases hNF k with ⟨hop, _⟩ | ⟨_, a0, b0, _, _, hin⟩
          · exfalso
            have hkNot : k ∈ Rnot := Finset.mem_filter.mpr ⟨hkR, hop⟩
            have hpos : 0 < Rnot.card := Finset.card_pos.mpr ⟨k, hkNot⟩
            omega
          · have hinS : inSrc k = [src C a0, src C b0] := by simp only [inSrc]; rw [hin]; rfl
            refine ⟨src C a0, src C b0, hinS, ?_, ?_⟩
            · exact (hInSrc_props k hkR (src C a0) (by rw [hinS]; simp)).1
            · exact (hInSrc_props k hkR (src C b0) (by rw [hinS]; simp)).1
        have hFormProps : ∀ w : ℕ, (w ∈ V8 ∨ ∃ j ∈ R, w = 9 + j.val) →
            (buildForm C R inSrc v w).readOnce ∧
            (∀ i : Fin 9, i ∈ (buildForm C R inSrc v w).vars → i.val ∈ (reachW C R inSrc w).erase v) ∧
            (∀ x : Fin 9 → Bool, Restricted x → x ⟨v, by simp [V8] at hvV8; omega⟩ = true →
              (buildForm C R inSrc v w).eval x = wireVal C x w) := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            rcases hw with hwV8 | ⟨k, hkR, rfl⟩
            · have hw9 : w < 9 := by simp [V8] at hwV8; omega
              have hnot9 : ¬ (9 ≤ w ∧ w - 9 < C.gates.length) := by omega
              rw [buildForm, dif_neg hnot9, dif_pos hw9]
              by_cases hwv : w = v
              · subst hwv
                simp only [ite_true, MForm9.readOnce, MForm9.vars, MForm9.eval]
                refine ⟨trivial, fun _ h => by simp at h, fun x _ hxv => ?_⟩
                rw [wireVal_nat C x w hw9, hxv]
              · simp only [hwv, ite_false, MForm9.readOnce, MForm9.vars, MForm9.eval]
                refine ⟨trivial, fun i hi => ?_, fun x _ _ => ?_⟩
                · simp only [Finset.mem_singleton] at hi
                  subst hi
                  rw [reachW_lt9 C R inSrc w hw9]
                  exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_singleton_self w⟩
                · rw [wireVal_nat C x w hw9]
            · obtain ⟨a, b, hinK, haLt, hbLt⟩ := hBinIn k hkR
              have h1 : 9 ≤ 9 + k.val ∧ (9 + k.val) - 9 < C.gates.length := ⟨by omega, by simp [k.isLt]⟩
              have hk' : (⟨(9 + k.val) - 9, h1.2⟩ : Fin C.gates.length) = k := Fin.ext (by simp)
              have hbf : buildForm C R inSrc v (9 + k.val) =
                  if (C.gates.get k).op = GateOp.and then
                    .and (buildForm C R inSrc v a) (buildForm C R inSrc v b)
                  else
                    .or (buildForm C R inSrc v a) (buildForm C R inSrc v b) := by
                rw [buildForm, dif_pos h1]
                simp only [hk', hkR, ite_true, hinK, haLt, hbLt, and_self, dite_true]
              have haOr := (hInSrc_props k hkR a (by rw [hinK]; simp)).2
              have hbOr := (hInSrc_props k hkR b (by rw [hinK]; simp)).2
              have hiha := ih a haLt haOr
              have hihb := ih b hbLt hbOr
              have hvlt9 : v < 9 := by simp [V8] at hvV8; omega
              have hdisjReach : Disjoint ((reachW C R inSrc a).erase v) ((reachW C R inSrc b).erase v) :=
                hDisj_of_deg1 k a b v hkR hinK (Or.inl hvlt9) hdeg1
              have hdisjVars : Disjoint (buildForm C R inSrc v a).vars (buildForm C R inSrc v b).vars := by
                rw [Finset.disjoint_left]
                intro i hia hib
                exact Finset.disjoint_left.mp hdisjReach (hiha.2.1 i hia) (hihb.2.1 i hib)
              have hvarsSub : ∀ i : Fin 9,
                  i ∈ (buildForm C R inSrc v a).vars ∪ (buildForm C R inSrc v b).vars →
                  i.val ∈ (reachW C R inSrc (9 + k.val)).erase v := by
                intro i hi
                rw [reachW_gate C R inSrc k hkR (fun z hz => (hInSrc_props k hkR z hz).1)]
                simp only [Finset.mem_union] at hi
                rcases hi with hia | hib
                · have hm := Finset.mem_erase.mp (hiha.2.1 i hia)
                  refine Finset.mem_erase.mpr ⟨hm.1, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ?_, hm.2⟩)⟩
                  exact List.mem_toFinset.mpr (by rw [hinK]; simp)
                · have hm := Finset.mem_erase.mp (hihb.2.1 i hib)
                  refine Finset.mem_erase.mpr ⟨hm.1, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, ?_, hm.2⟩)⟩
                  exact List.mem_toFinset.mpr (by rw [hinK]; simp)
              have hevalK : ∀ x : Fin 9 → Bool, Restricted x → x ⟨v, by simp [V8] at hvV8; omega⟩ = true →
                  wireVal C x (9 + k.val) =
                    if (C.gates.get k).op = GateOp.and then
                      wireVal C x a && wireVal C x b
                    else
                      wireVal C x a || wireVal C x b := by
                intro x hx hxv
                have hkGrem' := Finset.mem_filter.mp (hRsub hkR)
                rw [wireVal_gate C x k (normal_inputs_lt hNF k)]
                rcases hNF k with ⟨hop, _⟩ | ⟨hop, a0, b0, _, _, hin0⟩
                · exfalso
                  have := hNoNot k hkR
                  rw [hop] at this
                  simp at this
                · have ha0lt : a0 < 9 + k.val := normal_inputs_lt hNF k a0 (by rw [hin0]; simp)
                  have hb0lt : b0 < 9 + k.val := normal_inputs_lt hNF k b0 (by rw [hin0]; simp)
                  have hspa := hSrcAll a0 (by omega) (hkGrem'.2.2 a0 (by rw [hin0]; simp))
                  have hspb := hSrcAll b0 (by omega) (hkGrem'.2.2 b0 (by rw [hin0]; simp))
                  have hpair_eq : [src C a0, src C b0] = [a, b] := by
                    have : inSrc k = [src C a0, src C b0] := by simp only [inSrc]; rw [hin0]; rfl
                    rw [← this, hinK]
                  have haeq : src C a0 = a := by injection hpair_eq
                  have hbeq : src C b0 = b := by injection hpair_eq with _ htail; injection htail
                  rw [hin0]
                  simp only [List.map_cons, List.map_nil]
                  rw [hspa.2.1 x hx, hspb.2.1 x hx, haeq, hbeq]
                  rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
              rw [hbf]
              split_ifs with hand
              · refine ⟨⟨hiha.1, hihb.1, hdisjVars⟩, hvarsSub, fun x hx hxv => ?_⟩
                simp only [MForm9.eval]
                rw [hiha.2.2 x hx hxv, hihb.2.2 x hx hxv, hevalK x hx hxv, if_pos hand]
              · refine ⟨⟨hiha.1, hihb.1, hdisjVars⟩, hvarsSub, fun x hx hxv => ?_⟩
                simp only [MForm9.eval]
                rw [hiha.2.2 x hx hxv, hihb.2.2 x hx hxv, hevalK x hx hxv, if_neg hand]
        have hOutForm := hFormProps (9 + jout.val) (Or.inr ⟨jout, hjoutR, rfl⟩)
        apply no_readOnce_f8_fix v hvV8 (buildForm C R inSrc v (9 + jout.val)) hOutForm.1
        intro x hx hxv
        rw [hOutForm.2.2 x hx hxv, ← hjoutEq, ← hOutSrc.2.1 x hx, hEvalWire x]
      · push Not at hCaseB
        have hdegV8 : ∀ v ∈ V8, deg v = 1 := by
          intro v hv
          have h1 := hdeg_pos v (Finset.mem_union_left _ hv)
          have h2 := hCaseB v hv
          omega
        have hReach_var_nonempty : ∀ w : ℕ, (w ∈ V8 ∨ ∃ j ∈ R, w = 9 + j.val) →
            ((reachW C R inSrc w) ∩ V8).Nonempty := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            rcases hw with hwV8 | ⟨k, hkR, rfl⟩
            · exact ⟨w, Finset.mem_inter.mpr ⟨mem_reachW_self C R inSrc w, hwV8⟩⟩
            · have hne : (inSrc k).length ≥ 1 := by
                simp only [inSrc, List.length_map]
                rcases hNF k with ⟨_, _, _, hin⟩ | ⟨_, _, _, _, _, hin⟩ <;> rw [hin] <;> simp
              cases hinK : inSrc k with
              | nil => rw [hinK] at hne; simp at hne
              | cons a t =>
                have ha := hInSrc_props k hkR a (by rw [hinK]; simp)
                obtain ⟨u, hu⟩ := ih a ha.1 ha.2
                have hu' := Finset.mem_inter.mp hu
                refine ⟨u, Finset.mem_inter.mpr ⟨?_, hu'.2⟩⟩
                rw [reachW_gate C R inSrc k hkR (fun z hz => (hInSrc_props k hkR z hz).1)]
                exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr (by rw [hinK]; simp), hu'.1⟩)
        have hReach_step : ∀ (w0 : ℕ) (k' : Fin C.gates.length), k' ∈ R →
            9 + k'.val ∈ reachW C R inSrc w0 → ∀ u ∈ inSrc k', u ∈ reachW C R inSrc w0 := by
          intro w0
          induction w0 using Nat.strong_induction_on with
          | ind w0 ih0 =>
            intro k' hk'R hmem0 u hu
            rw [reachW_eq] at hmem0
            split_ifs at hmem0 with h1 h2
            · simp only [Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
                List.mem_filter, decide_eq_true_eq] at hmem0
              rcases hmem0 with heq0 | ⟨v, ⟨hvmem, hvlt⟩, hkv⟩
              · rw [reachW_eq, dif_pos h1, if_pos h2]
                have hlt0 : u < w0 := by have := (hInSrc_props k' hk'R u hu).1; omega
                have hk'eq : (⟨w0 - 9, h1.2⟩ : Fin C.gates.length) = k' := Fin.ext (by dsimp; omega)
                refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, ?_, mem_reachW_self _ _ _ u⟩)
                rw [hk'eq]
                exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hu, decide_eq_true hlt0⟩)
              · rw [reachW_eq, dif_pos h1, if_pos h2]
                refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v, ?_, ih0 v hvlt k' hk'R hkv u hu⟩)
                exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hvmem, decide_eq_true hvlt⟩)
            · simp only [Finset.mem_singleton] at hmem0
              rw [← hmem0, reachW_gate C R inSrc k' hk'R (fun q hq => (hInSrc_props k' hk'R q hq).1)]
              exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hu, mem_reachW_self _ _ _ u⟩)
            · simp only [Finset.mem_singleton] at hmem0
              rw [← hmem0, reachW_gate C R inSrc k' hk'R (fun q hq => (hInSrc_props k' hk'R q hq).1)]
              exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hu, mem_reachW_self _ _ _ u⟩)
        have hModuleKill : ∀ (c : ℕ), (∃ gc ∈ R, c = 9 + gc.val) →
            2 ≤ ((reachW C R inSrc c) ∩ V8).card →
            ((reachW C R inSrc c) ∩ V8).card ≤ 7 →
            (∀ w ∈ (reachW C R inSrc c).erase c, deg w ≤ 1) → False := by
          intro c ⟨gc, hgcR, hceq⟩ hge2 hle7 hdeg_in
          let Sc : Finset ℕ := (reachW C R inSrc c) ∩ V8
          have hSc_sub : Sc ⊆ V8 := Finset.inter_subset_right
          have hNoExit : ∀ w ∈ (reachW C R inSrc c).erase c, ∀ k ∈ R,
              w ∈ inSrc k → 9 + k.val ∈ reachW C R inSrc c := by
            intro w hw k hkR hwIn
            have hw' := Finset.mem_erase.mp hw
            obtain ⟨k1, hk1R, hk1reach, hwIn1⟩ := hReach_parent c w hw'.2 hw'.1
            have hdw : deg w ≤ 1 := hdeg_in w hw
            have hkeq : k = k1 := by
              by_contra hne
              have h1 : 1 ≤ (inSrc k).count w := List.count_pos_iff.mpr hwIn
              have h2 : 1 ≤ (inSrc k1).count w := List.count_pos_iff.mpr hwIn1
              have hpair : ({k, k1} : Finset (Fin C.gates.length)) ⊆ R := by
                intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
              have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k' => (inSrc k').count w) hpair (fun _ _ _ => Nat.zero_le _)
              rw [Finset.sum_pair hne] at hle
              change (inSrc k).count w + (inSrc k1).count w ≤ deg w at hle
              omega
            subst hkeq
            exact hk1reach
          have hφS : ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
              (∀ i : Fin 9, i.val ∈ Sc → x i = y i) → wireVal C x c = wireVal C y c := by
            intro x y hx hy hagree
            have hall : ∀ w : ℕ, w ∈ reachW C R inSrc c → wireVal C x w = wireVal C y w := by
              intro w
              induction w using Nat.strong_induction_on with
              | ind w ih =>
                intro hw
                have hwOr := hReach_sub_W c (Or.inr ⟨gc, hgcR, hceq⟩) w hw
                rcases hwOr with hwV8 | ⟨k, hkR, rfl⟩
                · have hw9 : w < 9 := by simp [V8] at hwV8; omega
                  rw [wireVal_nat C x w hw9, wireVal_nat C y w hw9]
                  exact hagree ⟨w, hw9⟩ (Finset.mem_inter.mpr ⟨hw, hwV8⟩)
                · have hkGrem' := Finset.mem_filter.mp (hRsub hkR)
                  rw [wireVal_gate C x k (normal_inputs_lt hNF k),
                    wireVal_gate C y k (normal_inputs_lt hNF k)]
                  congr 1
                  apply List.map_congr_left
                  intro a ha
                  have halt : a < 9 + k.val := normal_inputs_lt hNF k a ha
                  have hsp := hSrcAll a (by omega) (hkGrem'.2.2 a ha)
                  rw [hsp.2.1 x hx, hsp.2.1 y hy]
                  have hmemIn : src C a ∈ inSrc k := List.mem_map.mpr ⟨a, ha, rfl⟩
                  have hsrc_lt : src C a < 9 + k.val := (hInSrc_props k hkR (src C a) hmemIn).1
                  have hsrc_in_reach : src C a ∈ reachW C R inSrc c :=
                    hReach_step c k hkR hw (src C a) hmemIn
                  exact ih (src C a) hsrc_lt hsrc_in_reach
            exact hall c (mem_reachW_self C R inSrc c)
          have hfact : ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
              (∀ i : Fin 9, i.val ∈ V8 → i.val ∉ Sc → x i = y i) →
              wireVal C x c = wireVal C y c → pm3 x = pm3 y := by
            intro x y hx hy hagreeOut hceval
            have hallOut : ∀ n : ℕ, ∀ k ∈ R, k.val = n →
                9 + k.val ∉ (reachW C R inSrc c).erase c →
                wireVal C x (9 + k.val) = wireVal C y (9 + k.val) := by
              intro n
              induction n using Nat.strong_induction_on with
              | ind n ih =>
                intro k hkR hkn hnotIn
                by_cases hkc : 9 + k.val = c
                · rw [hkc]; exact hceval
                · have hkNotReach : 9 + k.val ∉ reachW C R inSrc c :=
                    fun h => hnotIn (Finset.mem_erase.mpr ⟨hkc, h⟩)
                  have hkGrem' := Finset.mem_filter.mp (hRsub hkR)
                  rw [wireVal_gate C x k (normal_inputs_lt hNF k),
                    wireVal_gate C y k (normal_inputs_lt hNF k)]
                  congr 1
                  apply List.map_congr_left
                  intro a ha
                  have halt : a < 9 + k.val := normal_inputs_lt hNF k a ha
                  have hsp := hSrcAll a (by omega) (hkGrem'.2.2 a ha)
                  rw [hsp.2.1 x hx, hsp.2.1 y hy]
                  have hmemIn : src C a ∈ inSrc k := List.mem_map.mpr ⟨a, ha, rfl⟩
                  have hnotEr : src C a ∉ (reachW C R inSrc c).erase c :=
                    fun h => hkNotReach (hNoExit (src C a) h k hkR hmemIn)
                  by_cases huc : src C a = c
                  · rw [huc]; exact hceval
                  · rcases (hInSrc_props k hkR (src C a) hmemIn).2 with huV8 | ⟨j, hjR, hjeq⟩
                    · have huNotSc : src C a ∉ Sc := by
                        intro hsc
                        exact hnotEr (Finset.mem_erase.mpr ⟨huc, (Finset.mem_inter.mp hsc).1⟩)
                      have hu9 : src C a < 9 := by simp [V8] at huV8; omega
                      rw [wireVal_nat C x (src C a) hu9, wireVal_nat C y (src C a) hu9]
                      exact hagreeOut ⟨src C a, hu9⟩ huV8 huNotSc
                    · have hjlt : j.val < n := by
                        have := (hInSrc_props k hkR (src C a) hmemIn).1
                        omega
                      rw [hjeq]
                      exact ih j.val hjlt j hjR rfl (hjeq ▸ hnotEr)
            have hjoutNotEr : 9 + jout.val ∉ (reachW C R inSrc c).erase c := by
              intro h
              have h' := Finset.mem_erase.mp h
              have hle := reachW_le C R inSrc c (9 + jout.val) h'.2
              have hgc_le := hR_le_jout gc hgcR
              omega
            rw [← hEvalWire x, ← hEvalWire y, hOutSrc.2.1 x hx, hOutSrc.2.1 y hy, hjoutEq]
            exact hallOut jout.val jout hjoutR rfl hjoutNotEr
          exact no_module_f8_refute Sc hSc_sub hge2 hle7 (fun x => wireVal C x c) hφS hfact
        by_cases hG2 : ∃ gstar ∈ R.erase jout, 2 ≤ deg (9 + gstar.val)
        · obtain ⟨gstar, hgstarEr, hdegG⟩ := hG2
          have hgstarR : gstar ∈ R := (Finset.mem_erase.mp hgstarEr).2
          have hgstarW : 9 + gstar.val ∈ Wset :=
            Finset.mem_union_right _ (Finset.mem_image.mpr ⟨gstar, hgstarEr, rfl⟩)
          have hg_sub : deg (9 + gstar.val) - 1 ≤ ∑ w ∈ Wset, (deg w - 1) :=
            Finset.single_le_sum (f := fun w => deg w - 1) (fun _ _ => Nat.zero_le _) hgstarW
          have hRnot0 : Rnot.card = 0 := by omega
          have hdeg1 : ∀ w ∈ Wset, w ≠ 9 + gstar.val → deg w ≤ 1 := by
            intro w hw hne
            have hpair : ({9 + gstar.val, w} : Finset ℕ) ⊆ Wset := by
              intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
            have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun w => deg w - 1) hpair (fun _ _ _ => Nat.zero_le _)
            rw [Finset.sum_pair hne.symm] at hle
            omega
          have hBinG : ∃ a b, inSrc gstar = [a, b] ∧ a < 9 + gstar.val ∧ b < 9 + gstar.val := by
            rcases hNF gstar with ⟨hop, _⟩ | ⟨_, a0, b0, _, _, hin⟩
            · exfalso
              have hpos : 0 < Rnot.card := Finset.card_pos.mpr ⟨gstar, Finset.mem_filter.mpr ⟨hgstarR, hop⟩⟩
              omega
            · have hinS : inSrc gstar = [src C a0, src C b0] := by simp only [inSrc]; rw [hin]; rfl
              exact ⟨src C a0, src C b0, hinS,
                (hInSrc_props gstar hgstarR (src C a0) (by rw [hinS]; simp)).1,
                (hInSrc_props gstar hgstarR (src C b0) (by rw [hinS]; simp)).1⟩
          obtain ⟨a, b, hinG, haLt, hbLt⟩ := hBinG
          have haOr := (hInSrc_props gstar hgstarR a (by rw [hinG]; simp)).2
          have hbOr := (hInSrc_props gstar hgstarR b (by rw [hinG]; simp)).2
          have hDisjAB : Disjoint (reachW C R inSrc a) (reachW C R inSrc b) := by
            have hd := hDisj_of_deg1 gstar a b (9 + gstar.val) hgstarR hinG (Or.inr (le_refl _)) hdeg1
            have hna : 9 + gstar.val ∉ reachW C R inSrc a := fun h => by
              have := reachW_le C R inSrc a _ h; omega
            have hnb : 9 + gstar.val ∉ reachW C R inSrc b := fun h => by
              have := reachW_le C R inSrc b _ h; omega
            rw [Finset.erase_eq_of_notMem hna, Finset.erase_eq_of_notMem hnb] at hd
            exact hd
          have hUnion : (reachW C R inSrc (9 + gstar.val)) ∩ V8 =
              ((reachW C R inSrc a) ∩ V8) ∪ ((reachW C R inSrc b) ∩ V8) := by
            rw [reachW_gate C R inSrc gstar hgstarR (fun z hz => (hInSrc_props gstar hgstarR z hz).1)]
            ext u
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
              Finset.mem_union, hinG, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro ⟨(rfl | ⟨v, (rfl | rfl), hv⟩), huV8⟩
              · simp [V8] at huV8; omega
              · exact Or.inl ⟨hv, huV8⟩
              · exact Or.inr ⟨hv, huV8⟩
            · rintro (⟨hu, huV8⟩ | ⟨hu, huV8⟩)
              · exact ⟨Or.inr ⟨a, Or.inl rfl, hu⟩, huV8⟩
              · exact ⟨Or.inr ⟨b, Or.inr rfl, hu⟩, huV8⟩
          have hDisjV : Disjoint ((reachW C R inSrc a) ∩ V8) ((reachW C R inSrc b) ∩ V8) :=
            Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hDisjAB
          have hCardSum : ((reachW C R inSrc (9 + gstar.val)) ∩ V8).card =
              ((reachW C R inSrc a) ∩ V8).card + ((reachW C R inSrc b) ∩ V8).card := by
            rw [hUnion, Finset.card_union_of_disjoint hDisjV]
          have hApos : 1 ≤ ((reachW C R inSrc a) ∩ V8).card :=
            Finset.card_pos.mpr (hReach_var_nonempty a haOr)
          have hBpos : 1 ≤ ((reachW C R inSrc b) ∩ V8).card :=
            Finset.card_pos.mpr (hReach_var_nonempty b hbOr)
          have hGle8 : ((reachW C R inSrc (9 + gstar.val)) ∩ V8).card ≤ 8 := by
            rw [← V8_card]; exact Finset.card_le_card Finset.inter_subset_right
          have hdeg_lt_gstar : ∀ w : ℕ, w < 9 + gstar.val → (w ∈ V8 ∨ ∃ j ∈ R, w = 9 + j.val) → deg w ≤ 1 := by
            intro w hwlt hwOr
            have hwW : w ∈ Wset := by
              rcases hwOr with h | ⟨j, hjR, rfl⟩
              · exact Finset.mem_union_left _ h
              · have hgle := hR_le_jout gstar hgstarR
                have hjne : j ≠ jout := fun heq => by subst heq; omega
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjne, hjR⟩, rfl⟩)
            exact hdeg1 w hwW (by omega)
          by_cases hle7 : ((reachW C R inSrc (9 + gstar.val)) ∩ V8).card ≤ 7
          · exact hModuleKill (9 + gstar.val) ⟨gstar, hgstarR, rfl⟩ (by omega) hle7 (fun w hw => by
              have hw' := Finset.mem_erase.mp hw
              have hle := reachW_le C R inSrc (9 + gstar.val) w hw'.2
              exact hdeg_lt_gstar w (by omega) (hReach_sub_W _ (Or.inr ⟨gstar, hgstarR, rfl⟩) w hw'.2))
          · have hEq8 : ((reachW C R inSrc (9 + gstar.val)) ∩ V8).card = 8 := by omega
            by_cases haGe2 : 2 ≤ ((reachW C R inSrc a) ∩ V8).card
            · have haGate : ∃ ga ∈ R, a = 9 + ga.val := by
                rcases haOr with haV8 | h
                · exfalso
                  have hlt9 : a < 9 := by simp [V8] at haV8; omega
                  rw [reachW_lt9 C R inSrc a hlt9] at haGe2
                  have : ({a} ∩ V8).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_left) (by simp)
                  omega
                · exact h
              exact hModuleKill a haGate haGe2 (by omega) (fun w hw => by
                have hw' := Finset.mem_erase.mp hw
                have hle := reachW_le C R inSrc a w hw'.2
                exact hdeg_lt_gstar w (by omega) (hReach_sub_W a haOr w hw'.2))
            · have hbGe2 : 2 ≤ ((reachW C R inSrc b) ∩ V8).card := by omega
              have hbGate : ∃ gb ∈ R, b = 9 + gb.val := by
                rcases hbOr with hbV8 | h
                · exfalso
                  have hlt9 : b < 9 := by simp [V8] at hbV8; omega
                  rw [reachW_lt9 C R inSrc b hlt9] at hbGe2
                  have : ({b} ∩ V8).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_left) (by simp)
                  omega
                · exact h
              exact hModuleKill b hbGate hbGe2 (by omega) (fun w hw => by
                have hw' := Finset.mem_erase.mp hw
                have hle := reachW_le C R inSrc b w hw'.2
                exact hdeg_lt_gstar w (by omega) (hReach_sub_W b hbOr w hw'.2))
        · push Not at hG2
          have hdegAll1 : ∀ w ∈ Wset, deg w ≤ 1 := by
            intro w hw
            simp only [Wset, Finset.mem_union, Finset.mem_image] at hw
            rcases hw with hwV8 | ⟨j, hjEr, rfl⟩
            · have := hdegV8 w hwV8; omega
            · have := hG2 j hjEr; omega
          have hAllReachJout : ∀ v ∈ V8, v ∈ reachW C R inSrc (9 + jout.val) := by
            let Sreach := R.filter fun k => 9 + k.val ∈ reachW C R inSrc (9 + jout.val)
            have hSreachMem : Sreach ∈ ClosedSets := by
              simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset]
              refine ⟨Finset.Subset.trans (Finset.filter_subset _ R) hRsub,
                Finset.mem_filter.mpr ⟨hjoutR, mem_reachW_self _ _ _ _⟩, ?_⟩
              intro k hk j hj hmem
              have hk' := Finset.mem_filter.mp hk
              have hjR := hRclosed k hk'.1 j hj hmem
              exact Finset.mem_filter.mpr ⟨hjR, hReach_step (9 + jout.val) k hk'.1 hk'.2 (9 + j.val) hmem⟩
            have heqS : Sreach = R :=
              Finset.eq_of_subset_of_card_le (Finset.filter_subset _ R) (hRmin Sreach hSreachMem)
            intro v hvV8
            obtain ⟨k, hkR, hvIn⟩ := hV8_used v hvV8
            have hkS : k ∈ Sreach := heqS ▸ hkR
            have hkReach : 9 + k.val ∈ reachW C R inSrc (9 + jout.val) := (Finset.mem_filter.mp hkS).2
            exact hReach_step (9 + jout.val) k hkR hkReach v hvIn
          have hTopBin : ∃ gtop ∈ R, ((reachW C R inSrc (9 + gtop.val)) ∩ V8).card = 8 ∧
              ∃ a b, inSrc gtop = [a, b] ∧ a < 9 + gtop.val ∧ b < 9 + gtop.val := by
            have hjoutCard : ((reachW C R inSrc (9 + jout.val)) ∩ V8).card = 8 := by
              have heq : (reachW C R inSrc (9 + jout.val)) ∩ V8 = V8 :=
                Finset.inter_eq_right.mpr hAllReachJout
              rw [heq, V8_card]
            rcases hNF jout with ⟨hop, a0, _, hin0⟩ | ⟨_, a0, b0, _, _, hin0⟩
            · have hinS0 : inSrc jout = [src C a0] := by simp only [inSrc]; rw [hin0]; rfl
              have haMem : src C a0 ∈ inSrc jout := by rw [hinS0]; simp
              have haProps := hInSrc_props jout hjoutR (src C a0) haMem
              have hReachEq : (reachW C R inSrc (9 + jout.val)) ∩ V8 = (reachW C R inSrc (src C a0)) ∩ V8 := by
                rw [reachW_gate C R inSrc jout hjoutR (fun z hz => (hInSrc_props jout hjoutR z hz).1)]
                ext u
                simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
                  hinS0, List.mem_singleton]
                constructor
                · rintro ⟨(rfl | ⟨v, rfl, hv⟩), huV8⟩
                  · simp [V8] at huV8; omega
                  · exact ⟨hv, huV8⟩
                · rintro ⟨hu, huV8⟩
                  exact ⟨Or.inr ⟨src C a0, rfl, hu⟩, huV8⟩
              rcases haProps.2 with haV8 | ⟨j1, hj1R, hjeq1⟩
              · exfalso
                have hlt9 : src C a0 < 9 := by simp [V8] at haV8; omega
                rw [hReachEq, reachW_lt9 C R inSrc _ hlt9] at hjoutCard
                have : ({src C a0} ∩ V8).card ≤ 1 :=
                  le_trans (Finset.card_le_card Finset.inter_subset_left) (by simp)
                omega
              · have hj1ne : j1 ≠ jout := fun heq => by subst heq; omega
                have hj1Bin : ∃ a b, inSrc j1 = [a, b] ∧ a < 9 + j1.val ∧ b < 9 + j1.val := by
                  rcases hNF j1 with ⟨hop1, _⟩ | ⟨_, a1, b1, _, _, hin1⟩
                  · exfalso
                    have hsub2 : ({jout, j1} : Finset (Fin C.gates.length)) ⊆ Rnot := by
                      intro x hx; simp at hx
                      rcases hx with rfl | rfl
                      · exact Finset.mem_filter.mpr ⟨hjoutR, hop⟩
                      · exact Finset.mem_filter.mpr ⟨hj1R, hop1⟩
                    have h2 : 2 ≤ Rnot.card := by
                      have hle := Finset.card_le_card hsub2
                      rw [Finset.card_pair hj1ne.symm] at hle
                      exact hle
                    omega
                  · have hinS1 : inSrc j1 = [src C a1, src C b1] := by simp only [inSrc]; rw [hin1]; rfl
                    exact ⟨src C a1, src C b1, hinS1,
                      (hInSrc_props j1 hj1R (src C a1) (by rw [hinS1]; simp)).1,
                      (hInSrc_props j1 hj1R (src C b1) (by rw [hinS1]; simp)).1⟩
                exact ⟨j1, hj1R, by rw [← hjeq1, ← hReachEq]; exact hjoutCard, hj1Bin⟩
            · have hinS0 : inSrc jout = [src C a0, src C b0] := by simp only [inSrc]; rw [hin0]; rfl
              exact ⟨jout, hjoutR, hjoutCard, src C a0, src C b0, hinS0,
                (hInSrc_props jout hjoutR (src C a0) (by rw [hinS0]; simp)).1,
                (hInSrc_props jout hjoutR (src C b0) (by rw [hinS0]; simp)).1⟩
          obtain ⟨gtop, hgtopR, hTopCard, a, b, hinTop, haLt, hbLt⟩ := hTopBin
          have haOr := (hInSrc_props gtop hgtopR a (by rw [hinTop]; simp)).2
          have hbOr := (hInSrc_props gtop hgtopR b (by rw [hinTop]; simp)).2
          have hDisjAB : Disjoint (reachW C R inSrc a) (reachW C R inSrc b) := by
            have hge_top : 9 + gtop.val ≤ 9 + C.gates.length := by omega
            have hd := hDisj_of_deg1 gtop a b (9 + C.gates.length) hgtopR hinTop (Or.inr hge_top) (fun w hw _ => hdegAll1 w hw)
            have hna : 9 + C.gates.length ∉ reachW C R inSrc a := fun h => by
              have := reachW_le C R inSrc a _ h; omega
            have hnb : 9 + C.gates.length ∉ reachW C R inSrc b := fun h => by
              have := reachW_le C R inSrc b _ h; omega
            rw [Finset.erase_eq_of_notMem hna, Finset.erase_eq_of_notMem hnb] at hd
            exact hd
          have hUnion : (reachW C R inSrc (9 + gtop.val)) ∩ V8 =
              ((reachW C R inSrc a) ∩ V8) ∪ ((reachW C R inSrc b) ∩ V8) := by
            rw [reachW_gate C R inSrc gtop hgtopR (fun z hz => (hInSrc_props gtop hgtopR z hz).1)]
            ext u
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
              Finset.mem_union, hinTop, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro ⟨(rfl | ⟨v, (rfl | rfl), hv⟩), huV8⟩
              · simp [V8] at huV8; omega
              · exact Or.inl ⟨hv, huV8⟩
              · exact Or.inr ⟨hv, huV8⟩
            · rintro (⟨hu, huV8⟩ | ⟨hu, huV8⟩)
              · exact ⟨Or.inr ⟨a, Or.inl rfl, hu⟩, huV8⟩
              · exact ⟨Or.inr ⟨b, Or.inr rfl, hu⟩, huV8⟩
          have hDisjV : Disjoint ((reachW C R inSrc a) ∩ V8) ((reachW C R inSrc b) ∩ V8) :=
            Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hDisjAB
          have hCardSum : 8 = ((reachW C R inSrc a) ∩ V8).card + ((reachW C R inSrc b) ∩ V8).card := by
            rw [← hTopCard, hUnion, Finset.card_union_of_disjoint hDisjV]
          have hApos : 1 ≤ ((reachW C R inSrc a) ∩ V8).card :=
            Finset.card_pos.mpr (hReach_var_nonempty a haOr)
          have hBpos : 1 ≤ ((reachW C R inSrc b) ∩ V8).card :=
            Finset.card_pos.mpr (hReach_var_nonempty b hbOr)
          have hdeg_lt_top : ∀ w : ℕ, w < 9 + gtop.val → (w ∈ V8 ∨ ∃ j ∈ R, w = 9 + j.val) → deg w ≤ 1 := by
            intro w hwlt hwOr
            have hwW : w ∈ Wset := by
              rcases hwOr with h | ⟨j, hjR, rfl⟩
              · exact Finset.mem_union_left _ h
              · have hgle := hR_le_jout gtop hgtopR
                have hjne : j ≠ jout := fun heq => by subst heq; omega
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjne, hjR⟩, rfl⟩)
            exact hdegAll1 w hwW
          by_cases haGe2 : 2 ≤ ((reachW C R inSrc a) ∩ V8).card
          · have haGate : ∃ ga ∈ R, a = 9 + ga.val := by
              rcases haOr with haV8 | h
              · exfalso
                have hlt9 : a < 9 := by simp [V8] at haV8; omega
                rw [reachW_lt9 C R inSrc a hlt9] at haGe2
                have : ({a} ∩ V8).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_left) (by simp)
                omega
              · exact h
            exact hModuleKill a haGate haGe2 (by omega) (fun w hw => by
              have hw' := Finset.mem_erase.mp hw
              have hle := reachW_le C R inSrc a w hw'.2
              exact hdeg_lt_top w (by omega) (hReach_sub_W a haOr w hw'.2))
          · have hbGe2 : 2 ≤ ((reachW C R inSrc b) ∩ V8).card := by omega
            have hbGate : ∃ gb ∈ R, b = 9 + gb.val := by
              rcases hbOr with hbV8 | h
              · exfalso
                have hlt9 : b < 9 := by simp [V8] at hbV8; omega
                rw [reachW_lt9 C R inSrc b hlt9] at hbGe2
                have : ({b} ∩ V8).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_left) (by simp)
                omega
              · exact h
            exact hModuleKill b hbGate hbGe2 (by omega) (fun w hw => by
              have hw' := Finset.mem_erase.mp hw
              have hle := reachW_le C R inSrc b w hw'.2
              exact hdeg_lt_top w (by omega) (hReach_sub_W b hbOr w hw'.2))

end ClassicalPart

end PEqualNP.Outside.L_meta_27511_aux

theorem PEqualNP.Outside.L_meta_27511 :
¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩) :=
  PEqualNP.Outside.L_meta_27511_aux.main_proof

