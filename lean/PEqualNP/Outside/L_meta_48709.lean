import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48709

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fullMask : Nat := 0xffffffffffffffff
abbrev Masked (mask w : Nat) : Prop := w &&& mask = w
def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c
theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl
theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp
theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]
theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp
theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all
theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all
def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)
theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]
theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]
theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]
theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩
theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]
theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w
theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]
theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne
theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]
def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))
theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _
theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩
theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]
theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h
theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1
def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank
def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b
def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs
def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length
theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)
theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩
theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)
theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2
def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S
theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _
theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega
inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S
theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega
theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1
theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩
theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))
def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w
theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl
def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k
theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]
def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws
theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢
theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha
theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq
def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)
theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]
theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega
theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit
def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws
theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]
def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w
theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]
def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l
def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws
def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l
theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]
theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩
def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l
theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩
theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2
theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]
def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits
theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)
theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)
theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩
def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])
def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)
theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)
def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i
theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2
def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi
theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2
theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2
theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]
theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length
def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k
def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0
theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide
theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]
theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]
def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]
theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)
theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)
theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])
theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel
theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i
theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl
def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1
theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]
def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)
theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)
theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl
def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws
theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl
def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l
theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl
def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop
theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl
def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits
theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl
def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)
theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl
def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl
def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i
theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm
def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))
def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm
def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))
def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws
theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all
theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)
theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])
def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws
def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))
theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl
def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps
def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps
def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps
theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]
theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl
theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih
theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]
def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi
theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl
theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
            have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
            have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
            obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
            obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
            have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
            have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
                ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                  ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                  ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                  binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                  LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                    (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
              by_cases hlt : ia0 < ib0
              · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                  by simp only [hlt, ite_true]; exact hea0,
                  by simp only [hlt, ite_true]; exact heb0,
                  by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
              · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
                have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                    dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                  ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
                exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                  by simp only [hlt, ite_false]; exact heb0,
                  by simp only [hlt, ite_false]; exact hea0,
                  by rw [hea0, heb0, hopEq],
                  by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
            · exact hznz hz'
            · rw [hznm] at hcm; exact Bool.noConfusion hcm
            · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
              have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
              have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
              have hzNotW : z ∉ ws := fun hm => by
                have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
              have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
                dropVal_comm x y ws
              set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
              have hnd_u : (z :: rest).Nodup :=
                List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                  dropVal_nodup (dropVal_nodup nd)⟩
              have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
                ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
              have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
              have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
                ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
              have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
              have hlen' : (insertSorted z rest).length =
                  ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
                list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
              have hcard' : (insertSorted z rest).length ≤ rem := by
                have hnd_s : (insertSorted z rest).Nodup :=
                  insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
                have := liveBin_card_le hlive_s
                rw [List.toFinset_card_of_nodup hnd_s] at this; omega
              have h2len : 2 ≤ ws.length := by
                have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                  intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                  · exact List.mem_toFinset.mpr hxM
                  · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
                have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
                have hc := Finset.card_le_card hsub2
                rw [List.toFinset_card_of_nodup nd] at hc; omega
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
    rw [subsetWordsF_eq] at hsr
    have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
    have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
    have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
      have := liveBin_card_le hlive'
      rw [List.toFinset_card_of_nodup hnd] at this; omega
    have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
      rw [lenN_eq]
      cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
      · rfl
      · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
        omega
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def m_0 : Nat := 0xf0f00000
def s_0 : List Nat := [0x50500000, 0x30300000, 0xf00000]
def g_0 : Nat := 0x10700000
def ep_0 : Nat := 0x600000000000000000000000000000102000000000000010400000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0xff000000000000
def s_1 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_1 : Nat := 0x17000000000000
def ep_1 : Nat := 0x600000000000000120000000000000014000000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0xf0f000000000000
def s_2 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_2 : Nat := 0x107000000000000
def ep_2 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0xf0f0000
def s_3 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_3 : Nat := 0x1070000
def ep_3 : Nat := 0x60000000000000000000000000000010200000000000001040000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0x5500550000000000
def s_5 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_5 : Nat := 0x100150000000000
def ep_5 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0x3300330000000000
def s_6 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_6 : Nat := 0x100130000000000
def ep_6 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0xf000f0000000000
def s_7 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_7 : Nat := 0x100070000000000
def ep_7 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0x4444444400000000
def s_8 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_8 : Nat := 0x4044400000000
def ep_8 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0xff0000000000
def s_9 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_9 : Nat := 0x170000000000
def ep_9 : Nat := 0x6000000000000001200000000000000140000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0xc0c0c0c
def s_10 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_10 : Nat := 0x4040c
def ep_10 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xa0a0a0a
def s_11 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_11 : Nat := 0x2020a
def ep_11 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0xf0000000f00000
def s_12 : List Nat := [0x50000000500000, 0x30000000300000, 0xf00000]
def g_12 : Nat := 0x10000000700000
def ep_12 : Nat := 0x60000000000000000000000000000000000000000000000000000000100000002000000010000000400000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0xaa000000aa
def s_13 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_13 : Nat := 0x20000002a
def ep_13 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0x3000300030003000
def s_14 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_14 : Nat := 0x100010003000
def ep_14 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0x3030000030300000
def s_15 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_15 : Nat := 0x10000010300000
def ep_15 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xcccc
def s_16 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_16 : Nat := 0x44c
def ep_16 : Nat := 0x48000000000000040800000000000000000000000000000440
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0x5050000050500000
def s_17 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_17 : Nat := 0x10000010500000
def ep_17 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x5555000000000000
def s_18 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_18 : Nat := 0x115000000000000
def ep_18 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xf000f00
def s_19 : List Nat := [0x5000500, 0x3000300, 0xf00]
def g_19 : Nat := 0x1000700
def ep_19 : Nat := 0x6000000000000000000000000000000000000000000010002000000000001000400
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x3333000000000000
def s_20 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_20 : Nat := 0x113000000000000
def ep_20 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0x2288228822882288
def s_21 : List Nat := [0x88008800880088, 0x208020802080208, 0x228800002288, 0x22882288]
def g_21 : Nat := 0x20000002208
def ep_21 : Nat := 0x200800000200000022080000000000000000000002000000000800000000000000000000000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1e383081e302080d3024a253984c5929548501e104800f 7 127 3 7 10 1023 14 16383
def nh_21 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0xa72531f1814a4a4241e49824a082400f 3 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 10 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 10 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 10 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 10 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0x2828282828282828
def s_22 : List Nat := [0x808080808080808, 0x28002800280028, 0x282800002828, 0x28282828]
def g_22 : Nat := 0x202028
def ep_22 : Nat := 0x20202800000000000020080000000000200008000000000000000000000000000000000000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0xd3039034e0a4073829048e6062e29510a06442200f 7 127 3 7 9 511 13 8191
def nh_22 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_22 : Nat → Nat × Nat := unpackForestF 0x239231229d3822121953852021100f 3 9
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 10 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 10 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 10 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 10 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x2222222288888888
def s_23 : List Nat := [0x88888888, 0x202020208080808, 0x22002200880088, 0x222200008888]
def g_23 : Nat := 0x2020200000008
def ep_23 : Nat := 0x200000000080002000000000008000202020000000800000000000000000000000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x193040f1a3030f113030c263e88c9d3e54c883e10c800f 7 127 3 7 10 1023 14 16383
def nh_23 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_23 : Nat → Nat × Nat := unpackForestF 0xc7c63229f68c0a64d3061810f886400f 3 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 10 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 10 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 10 ch_23 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 10 → ch_23 i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0x2222888822228888
def s_24 : List Nat := [0x888800008888, 0x202080802020808, 0x22008800220088, 0x22228888]
def g_24 : Nat := 0x2000000220008
def ep_24 : Nat := 0x20000800000000000000000002000000220008000200000000000800000000000000000000000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1e302080e3024b263988c592e548902e108800f 7 127 3 7 10 1023 14 16383
def nh_24 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_24 : Nat → Nat × Nat := unpackForestF 0xc72631f1814b8a4442e51824b084400f 3 10
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 10 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 10 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 10 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 10 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x5050050550500505
def s_25 : List Nat := [0x1010010110100101, 0x50500000505, 0x50000500500005, 0x50500505]
def g_25 : Nat := 0x10050510500505
def ep_25 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xff00ff0000000000
def s_26 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_26 : Nat := 0x100170000000000
def ep_26 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_26_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_26 : Nat → Nat := fun p => Bool.rec (hc_26_1 (Nat.sub p 32)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) (nh_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_9 (kn_cons lb_5 (kn_cons lb_6 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x6060606060606060
def s_27 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_27 : Nat := 0x4000602060
def ep_27 : Nat := 0x60202000000040000020000000004000600040000000000000000000000000000000000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14e59880f 4 15 2 3 9 511 11 2047
def nh_27 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_27 : Nat → Nat × Nat := unpackForestF 0x339cc40f 1 9
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 3 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 3 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 3 ch_27 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 3 → ch_27 i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_nil) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xffff000000000000
def s_28 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_28 : Nat := 0x117000000000000
def ep_28 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1), (m_18, s_18, 4, g_18), (m_20, s_20, 4, g_20)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_1 (kn_cons lb_18 (kn_cons lb_20 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xffff00000000
def s_29 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_29 : Nat := 0x175700000000
def ep_29 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xff00ff00000000
def s_30 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_30 : Nat := 0x17005700000000
def ep_30 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xcccccccc00000000
def s_31 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_31 : Nat := 0x4044400000000
def ep_31 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xaa00aa00aa00aa
def s_32 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_32 : Nat := 0x200020022002a
def ep_32 : Nat := 0x20002800000000000000080000000000000000000200020000000800020002002200200000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5555555500000000
def s_33 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_33 : Nat := 0x115155500000000
def ep_33 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_18, s_18, 4, g_18), (m_4, s_4, 4, g_4), (m_8, s_8, 4, g_8)]
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_33_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_33 : Nat → Nat := fun p => Bool.rec (hc_33_1 (Nat.sub p 32)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) (nh_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_18 (kn_cons lb_4 (kn_cons lb_8 (kn_nil))))) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x3030303030303030
def s_34 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_34 : Nat := 0x10101010303030
def ep_34 : Nat := 0x1020202000001000000020000010000000200000000000000000000000000000000000000010101010000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xcccc0000cccc
def s_35 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_35 : Nat := 0x4440000044c
def ep_35 : Nat := 0x800000000000000000000004000000048000004000000040800000000000000000000044400000440
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x3333000033330000
def s_36 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_36 : Nat := 0x113000011330000
def ep_36 : Nat := 0x1020000000000000000000000012000000220000010200000000000000000000000000000110000011000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xff000000ff00
def s_37 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_37 : Nat := 0x170000003700
def ep_37 : Nat := 0x200000000000000000000000000000000000000006000000040000001200000032000000140000000400
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xff000000ff
def s_38 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_38 : Nat := 0x570000007f
def ep_38 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x105000003070
def ep_39 : Nat := 0x202000000000000000000000004000000040000000000000000000001000000030200000105000000040
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cur_39 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_39 : Nat → Nat := fun _ => 0
def f_39 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 1 (dagTraceF m_39 s_39 3 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 1 bds_39 (dagTraceF m_39 s_39 3 f_39) (cur_39 0) (nh_39 0) s_39 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39 : treeBlockF 0 1 ch_39 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 1 → ch_39 i = true := fun _ h1 h2 => treeBlockF_at nb_39 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 4 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xaaaa0000aaaa
def s_40 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_40 : Nat := 0x2020000222a
def ep_40 : Nat := 0x202800000000000000000000000000000008000002020000000800000202000022200000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x100130011003300
def ep_41 : Nat := 0x1000200000001200000022000000000000000000010002000000000000000000000000000100100011000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf000f000f000f000
def s_42 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_42 : Nat := 0x100010003000
def ep_42 : Nat := 0x1000200000001000000020000000000000000000000000000000000000001000100030000000100010000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xcc00cc00cc00cc
def s_43 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_43 : Nat := 0x400440044004c
def ep_43 : Nat := 0x40000800000040000000080000000000000000000400000000000800000000000000000004004400440040
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_43_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_43_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_43_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_43 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_43_2 (Nat.sub p 64)) (hc_43_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 64 (dagTraceF m_43 s_43 5 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 64 bds_43 (dagTraceF m_43 s_43 5 f_43) (cur_43 0) (nh_43 0) s_43 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 64 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 6 :=
  lowerDagV5 (kn_nil) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff
def s_44 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_44 : Nat := 0x377f
def ep_44 : Nat := 0x48000000000000040800000000000032200000000000000440
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xf0f0f0f
def s_45 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_45 : Nat := 0x107070f
def ep_45 : Nat := 0x6080000000000060008000000000000000000000000010202000000000001040400
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_19, s_19, 4, g_19), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_45_1 (Nat.sub p 32)) (cc_45_0 p) (Nat.blt p 32)
def hc_45_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_45_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_45 : Nat → Nat := fun p => Bool.rec (hc_45_1 (Nat.sub p 32)) (hc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 43 bds_45 (dagTraceF m_45 s_45 6 f_45) (cur_45 0) (nh_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 ch_45 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 43 ch_45 = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_19 (kn_cons lb_10 (kn_cons lb_11 (kn_nil))))) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xcccccccc
def s_46 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_46 : Nat := 0x44044c
def ep_46 : Nat := 0x4080000000000440048000000000000040800000000000000000000000000440440
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xaaaaaaaa
def s_47 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_47 : Nat := 0x22222a
def ep_47 : Nat := 0x22080000000000220008000000000000000800000000002222200000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xff000000ff0000
def s_48 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_48 : Nat := 0x17000000770000
def ep_48 : Nat := 0x60000000000000000000000000000000000000000600000000000000120000002200000014000000440000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf000f000f000f0
def s_49 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_49 : Nat := 0x10005000700070
def ep_49 : Nat := 0x60002000000040000000000000000000000000000000000000000000100000002000200010005000400040
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf0f00000f0f00000
def s_50 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_50 : Nat := 0x10000010700000
def ep_50 : Nat := 0x1060000000000000000000000010000000600000000000000000000000100000102000000010000010400000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_0, s_0, 4, g_0), (m_17, s_17, 4, g_17), (m_15, s_15, 4, g_15)]
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_50_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_50 : Nat → Nat := fun p => Bool.rec (hc_50_1 (Nat.sub p 32)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 43 bds_50 (dagTraceF m_50 s_50 6 f_50) (cur_50 0) (nh_50 0) s_50 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 ch_50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 43 ch_50 = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 43 → ch_50 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 43 → ch_50 i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 7 :=
  lowerDagV5 (kn_cons lb_12 (kn_cons lb_0 (kn_cons lb_17 (kn_cons lb_15 (kn_nil))))) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x4444888844448888
def s_51 : List Nat := [0x888800008888, 0x404080804040808, 0x44008800440088, 0x44448888]
def g_51 : Nat := 0x4000000440008
def ep_51 : Nat := 0x40000800000000000000000004000000440008000400000000000800000000000000000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1e302080e3024b263988c592e548902e108800f 7 127 3 7 10 1023 14 16383
def nh_51 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0xc72631f1814b8a4442e51824b084400f 3 10
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 10 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 10 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 10 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 10 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x4444444444444444
def s_52 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_52 : Nat := 0x4044400440444
def ep_52 : Nat := 0x40000000000440000004000004004000440040000404000000040000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x55005500aa00aa
def s_53 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_53 : Nat := 0x1500550022002a
def ep_53 : Nat := 0x40000000080000000000000000000400000000000800100000002200200000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a192430a123434d263a88d9d3a54d883a10d800f 7 127 3 7 10 1023 14 16383
def nh_53 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6ce3469a10e886c00f 3 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 10 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 10 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 10 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 10 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xa0a0a0a0a0a0a0a
def s_54 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_54 : Nat := 0x202020002020a
def ep_54 : Nat := 0x800000200000002080002000000020008000000000000000000020202000202000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xc0c0c0c0c0c0c0c
def s_55 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_55 : Nat := 0x404040004040c
def ep_55 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xaaaaaaaaaaaaaaaa
def s_56 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_56 : Nat := 0x202020022222a
def ep_56 : Nat := 0x20202800000200000022080002000000220008000202020000000800020202002222200000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_24, s_24, 5, g_24), (m_23, s_23, 5, g_23), (m_22, s_22, 5, g_22), (m_21, s_21, 5, g_21)]
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42d0b42b299660946509060480200801b56c1b06c1b06c1b064945501405014050140488d507001 0xea50381410c5240948f95e3c568d956324a0b93c300f868322c0b828221e4c8392228130983e240b863501654083521e548705e1a168505608d401a501094839520c178285a0415a034b78d0dba4b6690d5a334c52d1143344cca84b2210c48230204c001f 10 1023 4 15 11 2047 18 262143
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548241209048241045d2c144a049160a05028028000000 0x32483fa3984a0fc4e7d071d838e4267493af485c0293410e2d0b649da9284018e80a6e2a16850ca2962d4b04bd7a5ab12b540e28099494e78a14e0645023024294a7484f080431819 9 511 3 7 11 2047 17 131071
def cc_56_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x22251093c871caf8c60a727931 6 63 3 7 10 1023 17 131071
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_56_2 (Nat.sub p 64)) (cc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_56_0 p) (Nat.blt p 32)
def hc_56_0 : Nat → Nat := unpackHintV5 0xeb00e904e704df10c23ac200c102c100c002a830a800a800a8008742810c7b0c7b007b00790477046f10513c4b0c450c450045004304410439101c3a00380000 0x3fcf1f50043c200015155055f4d555401354d7d55535540c24cff5ff3fd7c3c105503c0d544000ff5ff3fd1f3c1054103e55001050100400555410 16 65535 7 127
def hc_56_1 : Nat → Nat := unpackHintV5 0xd400d400b342b300b202b200b10299309900990099007744710c6b0c6b006b00690467045f10413c4100400240003f02292c2900290029000c3a060c000c0000 0x5d7d5741d0955755543cb052c00014b0f015cb002c0014ffc7fd3fcf7c5043dc0400014555403c80140094083c0058800216ff1f3d 16 65535 7 127
def hc_56_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x5f5d57005555 12 4095 6 63
def nh_56 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_56_2 (Nat.sub p 64)) (hc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0x22128828e6113c824e40b4b7a8e5e9397a0e00b43760e1c24e72131c0290292da24e684a1a0290290d645258d49625e5896969505a1416256028cd50384e539404c4e064094b46539193c46064094337148da5236578d95a38940e050365580933324a0b03e2e4f0b02e0212c904c240f8902e0210c535214548505e141685b501654050560208c125204548105e041681b500694010560204c001f 7 11
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 2 3 bds_56 69 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 2 3 69 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 69 ch_56 = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → ch_56 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 69 → ch_56 i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 69 → ch_56 i = true := nj_56_2
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_11 (kn_cons lb_24 (kn_cons lb_23 (kn_cons lb_22 (kn_cons lb_21 (kn_nil))))))) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xff00ff00ff00ff00
def s_57 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_57 : Nat := 0x100170011003700
def ep_57 : Nat := 0x1000200000001600000026000000000000000000010006000000040001001200110032000100140011000400
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_26 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xcccccccccccccccc
def s_58 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_58 : Nat := 0x404440044044c
def ep_58 : Nat := 0x40000800000440000004080004004000440048000404000000040800000000000000000004044400440440
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 6, g_43), (m_35, s_35, 5, g_35), (m_46, s_46, 5, g_46), (m_55, s_55, 5, g_55), (m_31, s_31, 5, g_31), (m_51, s_51, 5, g_51), (m_52, s_52, 5, g_52), (m_10, s_10, 4, g_10), (m_8, s_8, 4, g_8)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x850609c9a42629c9148d29115e7686a50c499801f 6 63 2 3 11 2047 15 32767
def nh_58 : Nat → Nat := unpackHintV5 0xdf00a378a30070666a8b621162003658006c0000 0x6f18f6318de00003558cf5ce79d1c015aed0518d600ac13cb39d74776c3d8e1828d507bd6a008e8263c71bc60000bd4680478f0e38004a7 16 65535 7 127
def f_58 : Nat → Nat × Nat := unpackForestF 0x41391686c5384a1945224a44578499801f 4 11
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 9 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 9 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 9 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 9 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_35 (kn_cons lb_46 (kn_cons lb_55 (kn_cons lb_31 (kn_cons lb_51 (kn_cons lb_52 (kn_cons lb_10 (kn_cons lb_8 (kn_nil)))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xff00ff00ff00ff
def s_59 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_59 : Nat := 0x1700570077007f
def ep_59 : Nat := 0x60002800000040000000080000000000000000000600020000000800120002002200200014005400440040
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 6, g_43), (m_49, s_49, 5, g_49), (m_30, s_30, 5, g_30), (m_48, s_48, 5, g_48), (m_38, s_38, 5, g_38), (m_32, s_32, 5, g_32), (m_53, s_53, 5, g_53), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d3095a5d209935a3958856791d447109c01f 6 63 2 3 10 1023 14 16383
def nh_59 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0xa000b56aec2e738cf318c13cf9a0005ebce719de3182e5d5b0a3db1ced1adeb004240e338c6c0aca8e005a801c671800233aba006471e 16 65535 7 127
def f_59 : Nat → Nat × Nat := unpackForestF 0x205d191da5d111cb5a2958856109c01f 4 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 9 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 9 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 9 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 9 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_49 (kn_cons lb_30 (kn_cons lb_48 (kn_cons lb_38 (kn_cons lb_32 (kn_cons lb_53 (kn_cons lb_12 (kn_cons lb_13 (kn_nil)))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xf0f0f0f0f0f0f0f
def s_60 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_60 : Nat := 0x10707070107070f
def ep_60 : Nat := 0x800000600000006080006000000060008000000000000000001020202010202000104040401040400
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 7, g_45)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xffffffff
def s_61 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_61 : Nat := 0x1177377f
def ep_61 : Nat := 0x26080000000000660048000000000000040800000000112232200000000011440440
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 7, g_45)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xffff0000ffff0000
def s_62 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_62 : Nat := 0x117000011770000
def ep_62 : Nat := 0x1060000000000000000000000016000000660000010600000000000001120000112200000114000011440000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffff0000ffff
def s_63 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_63 : Nat := 0x17570000377f
def ep_63 : Nat := 0x202800000000000000000000004000000048000006020000040800001202000032200000145400000440
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_38, s_38, 5, g_38), (m_40, s_40, 5, g_40), (m_37, s_37, 5, g_37), (m_29, s_29, 5, g_29), (m_39, s_39, 4, g_39), (m_13, s_13, 4, g_13), (m_9, s_9, 4, g_9)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d27090e408c63071dc0701936419060580601715c107401003c4d2340d0340c1288a006401 0xea5d8a55c24582357b46da46514a7234cb5d8b55c345aa3a6a36b952413aab56a256285a72447244945a8c5683567a5a6a56185a6042495c524b4247204c2a3b1a37e347d24bb2479a3b5a37393a3136104a0846001f 10 1023 4 15 11 2047 16 65535
def nh_63 : Nat → Nat := unpackHintV5 0x210807a341e5076f149b8876c045ac87607597f055ee1d574954e1d4c8e5163943054ee3d358c4c81d0d4a42a150a8041628d463285989e8527a00998a17dd42f60001780000 0x110175ae11a3017801001eaeb972c594f5468e8387465eefbab82a97577a8d18dea1c3d5d1ac2eb25c2c011a300003a30f5ee5ef7b97bdca1600b0ba34600001c2f7180500431c08c63184c000000055007824f7caa000f000040002f73c455033039af11a30039c39ce71a8c20000000aa0000066000468e0a046c0d11a30e4001c3883 18 262143 7 127
def f_63 : Nat → Nat × Nat := unpackForestF 0xea5d0b47da460a4bbb5dbb45b9520a47a356a2560a3b645a64566356625a7244625660420a37424b495c4247093a09361a3b204c1a37084a0846001f 5 11
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 30 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 30 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 30 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 30 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_38 (kn_cons lb_40 (kn_cons lb_37 (kn_cons lb_29 (kn_cons lb_39 (kn_cons lb_13 (kn_cons lb_9 (kn_nil))))))))) rc_63 nc_63 (by decide +kernel)

def g_64 : Nat := 0x11717571177377f
def ep_64 : Nat := 0x1060202800001640000026080016004000660048010606020000040801121202112232200114145411440440
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_59, s_59, 8, g_59), (m_50, s_50, 7, g_50), (m_26, s_26, 7, g_26), (m_62, s_62, 8, g_62), (m_63, s_63, 8, g_63), (m_33, s_33, 7, g_33), (m_60, s_60, 8, g_60), (m_58, s_58, 8, g_58), (m_36, s_36, 5, g_36), (m_56, s_56, 8, g_56), (m_61, s_61, 8, g_61), (m_45, s_45, 7, g_45), (m_28, s_28, 7, g_28), (m_41, s_41, 5, g_41), (m_43, s_43, 6, g_43), (m_16, s_16, 4, g_16), (m_13, s_13, 4, g_13), (m_34, s_34, 5, g_34), (m_5, s_5, 4, g_5), (m_55, s_55, 5, g_55), (m_14, s_14, 4, g_14), (m_4, s_4, 4, g_4), (m_54, s_54, 5, g_54), (m_20, s_20, 4, g_20), (m_47, s_47, 5, g_47), (m_15, s_15, 4, g_15), (m_25, s_25, 5, g_25), (m_48, s_48, 5, g_48)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb60590ac81601a62d302903480a20d1027853c09c0ce02683340980c61a3011808c0430e1810c08604302180f857c03d040f8001 0x3cd681c0ac0e03608a2d84114c1f2bc0e94606c2b032590172a80a96403cab026550112d807a6f062b782d58c146de0935f041ab81c5580c0ac0584c028220115bc07ac60336f015af808d5c020ad4045f9fe2dcfd15e7d8a73db5f9e5adceed5e736a73934f9bda5cd8d1e6968731a5f9612dca095e434a71c24f8b925c3091e07486fea3f7cd1dbda8ddde466e515f700adb4655d902a6c214f5d4a5aba51d562869613f4449da084dce32666612f3149594a49c992464985f2342d90215c7b0a63c04f1d8258d811c690862e03f1681d8720dc380661602f0a01584809c1a0460681f0240d80605c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x942508ca308854e501404c530485204811144101400f1258902048018860180600cc300481000400 0x1f35a7a159db5ab15beb563a716a935a9a9be5a5f9295e396f8a57e09577e49de06a74168e8226e991aa546499182545c9b1b56f6958d9a56625bd795f5a55d58445516d48564f5bd316f4a55cf154461110844 10 1023 4 15 11 2047 18 262143
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x84405acd064b2174b8552a150933a1c0d2683411480391c0c460291408440200c8281001 0x2f36ccf5bf2d63c8d5b0a6fbe97eea57b615acc68ab162a468af162ad6ea958a7a6f9c9bdf06a76168f0228655e8d65a11a27c5a9cd6a1157991625460911a23458871e22460849fe0350 9 511 3 7 11 2047 18 262143
def cc_64_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8d1d0bbb8b1a2998a88888180807978787146404032302928211918180a0801 0x3f044ff16fec53f815bd464f25bcf82276553bc5b7451ba568e35a37360eb1bf9a6fe491f816fde51f6927d61335044d0d933354c49bf1b64c4d5b0354 8 255 3 7 11 2047 18 262143
def cc_64_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x8440601007933590c86432190a550249208940990c0602c960a2502492082401c8381001 0x4f1549c8d53719a8eb7d0d6b9facf3b58e68ab4c24f9748f2c53e54a3ca1273e2a92411240221e836918b71f14cf0a3470568b8f9135c21e3e42d70836e1191b62927c42478629f0851e0893c0044 9 511 3 7 11 2047 19 524287
def cc_64_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2b09d2709c27094a14805f1785d1741c16c57458560581604cd304c1124405c140411002208002 0x17d596f5b45635aa94b57496ee52bddd7db86e156d6aa12d5aa78b24c96adf2c5305926cb16e96c9bed135d9a67b04c75ed82b6b75646fab8cf531bea233e1d6fbfacf791bede33d7457aa6b54e96a98ad4a06f820ceda15cfc23d21649c2c94455280be4d954 10 1023 4 15 11 2047 19 524287
def cc_64_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x8821184201801e2781b36c1a168191641815c5705c1522e8b0284a02449024054140320c03004801 0x3793e6e254da4c99e95b45ab6c27cce4adac953513669570d16cf9edbf39b3f0d6fdfad7bb59f6eb1ecc6fd78cfab17f4e2be8356cd4ad9659324be6556fc8acf8e95b18ab62368ad6b18492f0523e0370 10 1023 4 15 11 2047 19 524287
def cc_64_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x84a1080600789e0745d06c9b0685a06459064181601715c1705c16158160581513d82d0801104001 0x7f97c741547e9547d964739567c9347b97c729567a934799547816c771347545e735707656b75d6374c6a7446673a6f72a678156f8056b7f5677e5637d36f7c36b7b3677a3637935f78b5b77b5776b53721567126470254 10 1023 4 15 11 2047 20 1048575
def cc_64_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x88a208461080600801f17c1e1781e0708fd3c0f03c0f03c0f03c0f03c0f03c0f00f0300842000800 0x8f97c899568e9348d9548c16c8b1348a26f89a679556f9456b93567925639136f9036b8f3678e3638d35f8cb5b8bb578ab53891568856f87d6b8756786d638626f85a6b8526784a638425f83a5b8325782a53819647496480954 10 1023 4 15 11 2047 20 1048575
def cc_64_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a508ca308c2308c2308c2308c2308c2308c2218816c1fc701846014450104400c4300481000400 0x9fb6c978349ea4497044982509d45f9cc5b9c4579bc539b15f9a95b9a157999539914f9894b9794797143aa56fa956ba8567a7563a6b56a526fa426ba2a67a1a63a0a5fa025b9f2579e2539d8389683495964949549397c92954919648a15690934 10 1023 4 15 11 2047 20 1048575
def cc_64_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xc42ed1d0381700d85b03605c8b81512a04c4981112203c4688d01a02865008110020028c500620c008800800 0xafc60ba46fb9c67b8b6fb7b67b7347b626fb526bb4267b2a63b224bb1247b023baf2376392a4a86f4206737847208371682f12827ae134ad134adb6bacb63ac13cab934aab649d034a9b549c834a8b7c9c034a7b549b834a5a6fa3267a6364a5b569b034a4a449a844a3b7ca33569a034a224499844a13549903498844 11 2047 5 31 11 2047 20 1048575
def cc_64_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8dc2e152a8506814098aa540a050245208140200c460289408240200884020088400200 0xbf934bed7cbe17cbd134bb86cc1d6fc1567c036fbf36bbdb67bcb63bc35bbb35753236b9568b8570b6d6821037b5a6cb4d70b3a6cb3254b186cb0a6c 9 511 4 15 11 2047 20 1048575
def cc_64_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x902317d1f0749d0741b26c1b06c1b06c17441d003c4f0384e0344d0340b22c0a1064100401000400 0xcf054cf96ccc154ce86cc9814cd934c9014cca4dcc245caa4fca24bc9a47c9243d0b5fd035bce357cd353cb956cb018c8814c7c64c6c7cc5a54c4a64c4254c3254c736fc6367c526bc3a63c2a3b4b06f43067228371782fc0964 10 1023 4 15 11 2047 20 1048575
def cc_64_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c221846017c5e1781d1705845c5705856054550541324c13044910440f23c0f0348491001300400 0xdf47cdda58dc244ddb5cdba40dc24cdbb54de24fdd24bdca47db243dad70d9c7cd8d7cd7d70d705cd657cd5a7cd4a7cd4256d3470d2c5adfc6ddeb4fda347d924fd824bd6a47d5243d3a3bd2237cc964d1154ca814ca014 10 1023 4 15 11 2047 20 1048575
def cc_64_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x8d6308c221882118420180200801e2781d1741d06c9b06c1922f8b0284a0280a0208801c47009402 0xf5d6ff4d6bf3d67f2d63efa56ee464ed568ec464ead68ea05ce9264e8264e7a56e6c68e645aeec55edb4fecb47eba4feb24be9a47e8a43e723be5a373c84f38047238371882f13027e4954e316ce286ce1934e435fe3b5be2357e1353e0956d8a49d6241 10 1023 4 15 11 2047 20 1048575
def cc_64_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4a45902318c2218821184201789595414150131448b62c0a1280822006218051140501404110004 0x40117dff8af02d6f80eb3c04d5a01070ff0347f1323f4951f84f8fb25473cb7b5059dfbadefcd6b7deb3beb58df44ace716f69cb3b0a57d602aef94687c2383985bda52cef8d6f7beb3bdd169cb2ded2167578abbd8991e14c8f52547a13e3c0951e64a8f145e792b5bc758de18d4f0466 10 1023 4 15 11 2047 21 2097151
def cc_64_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e08e07e87e07e07a243c4203e23e03a23a03623603412e32e02e02e02e02e02c124408e080042040002000000000000 0x43cd7e1d6aeea05f7142db5c15d9d0a6bb83b58c1bc36d2e1a68f16c6f8b233c54dbe286d713367885b1c40d2e1f68ee996f710b5b5a59d9c2c6bb14b588a3a7c4fd17276831373bc999a04b4970de440678702e4321407208e2e83f1241b82007c0402f0ba648349242a9120c24909a7c82c924140521148904924840224140d20d6bf0635b82dabc12d4e168df0a46b84a33c1f18dd12dee116b6a8b3b3458d3c29e8a94b414a39da50e0e25104124819b24000d2046f8ff834 12 4095 5 31 11 2047 21 2097151
def cc_64_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41c0780700e01a8e394608c11062042184100600400366604b096028250090901184300600c014210c10801 0x11f47c8f1b2476d523a06920b6f8fdb5c7ad9e396c6eb96f720b5b6459da12c6a093f4689da104dcf22664c06f228338be0fc4b06e0901f0140b9524d4a826b190448deb7c6d59e358df1a46b8ce33c6318e308b717c57758b7b8e5adb02ced01635e0adac855d4029e8c94b41ca39e250ca726b0f05c8742e4575a2296d86912d89eb81a24b6234a112b6c891aa4440d21b0c10d050 11 2047 5 31 11 2047 21 2097151
def cc_64_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0371dc370d4b50a36719c2619826090a316a5a0609805c57054950541324c1303d02d0801104001 0x979364b89125b08930c5f97e2dcbb15e5a8a72ca56628afafc56d6a2aead953520a7a4052d0b28e7c1435f4a4cacdf25429f2994794ab84af1b65569728b475eca5ad051d4527e8f13b4289b9ec4ce464c927a54935224969b2454a924a449202248cd364568ac494d598a2c9d17e4c8b72545791e29c88959872bebc95b594abab254d4329e8e14b424a39e850e428c920354 10 1023 4 15 11 2047 21 2097151
def cc_64_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x70931b5882b295902a154c294948124011087a73829c00e0054e2a0150075a3a01b10a1c4c2260111088040204e0200084040001 0x27069736b478d925c5891e0347efba3b7bd1bbce8cd82296b99475409fa4c4ed0e26e7f133374979904acbf24e4f9237d51dbca8cd4e27e9213b4349b9f84ccdb25e4e9231941f8ac0dc3405e0b01f01c0b97c49e7c8ab20a4f8d525c5491e16486c714f5c4a39b24bcbc24f3d3568fd2fc6896e284af0a2532ec93cf11b63d49f19a4b89923c2490d8c29eb794735c9796e49e3c49b122458e8a7c6452e2228f081439d9ab47297e314b710a5783d29cea0e27406930a6b93931bb65bdbd2ce6a92f9c6b7ce159e664df2fa6b95533c9898e304b710257244358fe18c770b6290450a81584408e6e8df36c6799137cba9ae514cf252638bd25c3e91dd92deda1675b8a39a64bcae24f2d95b920a9cb49ae474c64786b1f431cd60e26a068100231441bcced904e08b32d689a22acccd2e6468ec014b5b0a3a944fd22276861373e8998e611c6107e268370500f80c05e624a930244 13 8191 5 31 11 2047 21 2097151
def cc_64_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c808 0x9c74b9bb478de4b8b6478163f7ee3b7c6377ae3360d4b5d1475513f4a93b44137409333852f3292b30d2728d231d44719c3f160370d82f09c270601f020177e63b7a6335493f4a13b43d374013337d2f28523 11 2047 5 31 10 1023 20 1048575
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_64_20 (Nat.sub p 640)) (cc_64_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_64_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (cc_64_17 (Nat.sub p 544)) (cc_64_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_64_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (cc_64_14 (Nat.sub p 448)) (cc_64_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_64_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_64_11 (Nat.sub p 352)) (cc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_64_9 (Nat.sub p 288)) (cc_64_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_64_6 (Nat.sub p 192)) (cc_64_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_64_4 (Nat.sub p 128)) (cc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_64_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_64_1 (Nat.sub p 32)) (cc_64_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def hc_64_0 : Nat → Nat := unpackHintV5 0xb18112ac454fa4d5dc9d61dd98095692e5498af9fb85d5497da20d79311c73357f6ec51c68cd7e6431275dd5975af0b955755f5175004bc56c49948c4618df415531350b1328632a1fc22817561b0ea62c08319d03d9160000f6000000000000 0x58b162c58b162c78f878f26aa8f51e91111088aaaaaaaaaa0d50baa8bd0f9556a555162c58b162c58b1e3c78f1e4c5a2d1e8f1ed44444104422d16a753a3d1ea8f54f03542eaaa1f2d2d4b4a2c58b162c58b162c58b1750b162c58f1e3c78f1ebc7af1e3c78f1e3c98f262d168f51ea3d2e3c7b51114514511108b45a5d4ba934ba3d1ea8f52f022c58b162c58b162c58b162c5d42c58b168c7974b8f76932e5c9910505145110b162c5970e5d2e1cba4cb97269cba32f05551382a82275559eaa82aa162c58b162c58b468c88888858b162d3a74e9d3a3469e0aaaaaaaa802cf550ba85d44eaa9a87cd5350790058b555458b16aa2c5aaaaaaaaa8b85c5ca2e5138bcaaaaaaaaaaaaaa2e170b0f41c3d0b85caab54aaa2c593162c5e7162c593162c5aaaaaaaa8b85c5ca2e5138bcaaaaaaaaaaaaaa8b545aa5d36aa9755526a97555556445545c2e162e858ba170b9556a96ceaaa1c58b168b16aaa2c5aaaaaaaaaaa8b85c4e272f29794aaaaaaaaaaaaaa2e170b85c2c3d070f4aab54aaa2c98b162c58bce2c593162c5aaaaaaaa8b85c4e271328994aaaaaaaaa9343aaaaaa2d516a93549aa4d26aa93555555591155170b85c2e162e858ba555aa5b3aaa87a555162c58b7e5d7937e5d793555555550000000000550500555500aa00a0aa555001552058b162c0261705501105523380000000aa0220aaaa008b545a800282009355555541800015aa0220aa555005b3aaac4c58b26acd8b162c5ab374aaaaaaaaaaa00100000000aaaa0a00aa0155540140aaa002a4c58b261b005810aaaa02200046700000155540441540136a8b549aa4d400141005555000056aaa80881554016ceaab172e2c58b165cd97162c9d2aaaaaaaaaa80000000002a8002aaaa805541e0000aa55500155005806cb8b164c2551001550000008ce00aa2002aaaa2009b545a8200000a9354baaaaa8300002b5411f000aaa555005b3aaad02c58b1600ad985cb80132e28a2ac6700001455528aaa52e6c58b162d99b2e2c5935555555556172b28b944e2f2aaaaaaaaaaaaaa8b85c7c3d070f44cfc5cfcaab54aa2c5aaaac2ea55555555554daa2d526aaaaaab222aa2e171f8fcaab54b675550e2c58b162c58b162c58b1750b45a8c7a971ea4d2ed5454555348743a1c3a870ea1c3a1c3aab33554b53554d354d22c58b16aaab5554aaaaaaaaab5554ab54aa2c58b162c58b163c78f1f5555541d0e8743a1d0eccd50baa96aa969458b162c5a2d46a36aaa9a43a1d0e8755666a85d54d354b67a585d42ea27552d50f96a22a0f2a2c593162c5e7162c593162c58b45a5c7a9b1ea4d2e8b85c5ca365138bcc8d0e1c38b0e1c38b0e1c3870e6c3a70e1c3870e5c39b0e1c3970e1c39350e3c3875a0e07283a1d0e1d438750e8755643b50b858b170b170ba166c59fa170b985b54aad2d9c593162c58b179c58b262c58b168b49a4d263d498f5170b89c4e265132991a1c387161c387161c387261c387261c3870e1c9874e1c3870e1c98726a1c7870eb41c0e50743a1d0e870e9350e1c38755590ed42e162c5c2e170b170ba164c59fa616d52ab4b672058b162c026530168b4041e08d46919c00000000e1c38b0e1c38b0000e9c0387000e1c3a70e1c39350e3c387500000e874040e01d0eaa8055542e00a08f85534802ab4b67262c5930d802c08468b49a4d0107800119c000000e1c38b0e1c39b0e1c3930e1c3930000e9c03870050e3c387500000e8743a1d010382a8055547eaa0220690055696ce00b00d97162c9848d1683c0049a5d0000008ce001c387161c3873601c380000074e1c3872e1c38726a1c7870ea00001d0e81c0043a1d55200aaa8fc11f000aaa690055696ce2c5a345a8d46c2ea646870e1c5870e1cd870e1d3870e1c9a871e1c3ad0703941d0e8743aab21da85c9c59f8fc7e63ed52ab4b67162c58b162c58b162c58b5555555556aa2a2aa9555555555555556aaaaaaaa9556a95458b162d5556aaa95555555556aaa9556a9556ce8b545aa4d5555556445559 24 16777215 10 1023
def hc_64_1 : Nat → Nat := unpackHintV5 0xc8a8ffc1f1aebc8d59b78d40b2195dabb19aa7ccf9a13da497567a9091b186be757f65d679ed5e716e206b9975634e135dd55e54fe364fc14f4b392244e5953e1db238b959300e2b28b5d6214dda1c7d3418051e1149af0c513e05d99e000176 0x2c58b162d162c7c3c7aaa3d47b555554aaaaaaaaaaaab0baa8bd0f9556aa955458b162c58b162c58b162ea162c58b1e3c78f1e3c78f1e3c78f168b47a8f51e971e3daaaaaaaaaa9a45a2d2ea5d49a5d1e8f547a9799162c58b162c58b162c78f1e3c5a2d1e8f1ed5555554d22d16a753a3c3a3c3aa3d53ccc2eaaa1f2d2d552d28b162c58b162c58b163c78fce8f1e3c9aaa3d47b555554aaaaaaaaaaaab542e89d0f959573d552aa8b162c58b162c58f1e3c78f262d168f478f6aaaaaaa69168b49a9d1e8f547aa799aa1747e87cb52d9eaa969458b1e3c58b162c79b1e3c78f1e3c98f45a3d1e3daa1750f28794c3d45aa3c3a8f0eaa3d53ca2e167e3f1f3f2ab4b678fd4b1f5162c58b5555aaaa5555555555aaaa555b3d52aa2d516a93551aaac88aaaaac8b175550b162ea858ba162c58b463d1a8c7a349a3464c882828888858b162d5874eab0e9d269d593468d1a382aa8a0aaaaa3f41550b164c58b179c58b164c58b162c58b166c79b4d8f3693468c9910505111142ea175178dd546eaa89d45ea6a1f350b162c59b0e6d361cda4d3ab268d1a3470553079aaaaa8dc7ea2755547e0b38501542c58b858baaa162eaa858b162c993264d18f46a31e8d22220a0a22162c58b264c993661d3acc3a751a3468e0aaa27551415547e802aa164c58b162c5e7162c98b162c58b162c993264c98f26931e4d22220aa09851142ea17513a89d44e275513aaa6a1f350b162c593264c9930e4d261c9a8d1a3470553079aa89d55555551f82ce1405517362c58b16ccd97162c9d48c58b468c7974b8f46932e5c99105051451133162cb970e5d2e1cba4cb97268cba32f05551f0a0aa2767aaaa8fd05554b52ccbb326ccbb3262c58b168c7aa31ea2d16a351a14144444434a1c3ac8743a1d55818a0aaaaa6a3ec134aa2c58b161c387261d5870e2d16870ea1c7aa351a44141444430ba85d41e0f5507aaa27533a5a87ad48b73870ea1c3870e875560699683875aaaaaa8fd5351f42ce14034972e2c58b165cd93162c9d2d4a345a5c7a971ea4d2691050511108743b4a1c3ac930e1d5581aa8a0a89d5351f609a498b164c39b0e1c38b0e1d5468b49a4d0e1d438f522220a0a218dd42ea27513a83c1eaa0f552d43d6a0e87526e70e1d43870eab034b075aa89d55555351f42ce14034ab162c9ab362c58b16acdd2cd2345a4d46a31ea8c7a91110505108743a1d90e1d6955606aaa82a29a8fb04d21c387161c38736ac58b26aa345a1c7a870ea4d469105051110c6ea17507aaa0f07aa89d45e96a1eb50743a1c3870e1d526e755801a65a0e1d6aa0f1faaaa89d5351f42ce140348b168c58b468d1a3464444451ba85d44eaa9a87cd42c5a74e9d1a3468e0aa60f3551faaaa3f059c280aa162c58b5545162c58b162c58b001e3c140000000000001555555555402aaa95569540015458b162d5526e75545aa2d51eaa0000000000aaaaaaaaaa015554ab2acca167005505802c026017011010780880080000808102c58b162c58b162c58b1600b162c5a31e5d2e3d7a4cb9726000000000002c58b165c3974b872e932e5c9a72e8cb805555555555500550b162c58b162c5a346bc00000058b162d3a74e9d3a3469c02aaaaa82ce01540b005804c001007800200702058b262c58bce2c58b262c58b162c58b363cda6c79b49a3464c0808008800880808080400000000000162c58b361cda6c39b49a7564d1a3468c800402aaaaaaaaa82000b3d52a2c58b161c387261d9870e2d16870ea1c7aa351a040400440044040404020000000000022dce1c3a870e1c3a1d55200100aaaaaaaa6908002ced21c387161c38736ac58b26aa345a1c7a870ea4d46810100110011010101008000000000001d0e870e1c387549b9d548004002aaaaaaa9a42000b3b48b16bd18b168d1a3468c0808080808040000000162d3af4e9d1a3468c800402aaaaa82000b3d50b162c5aaaa8b162c58b162c5d50f1f4aaaa444422140aaaaaaaaaaa835554aaa0a902aa2c58b16aa9373aaa2d516a8f552222110605555555555541aa89d52aacaad2c7d6802ceab0ba85d44ea2f4aaab0f5555a5956a55550058b162d55549a2c58b162c58b163c7d552aaa9111088502aaaaaaaaaaa0d544ea95554055480155162c58b555549b9d16a8b547aa9111088302aaaaaaaaaaa0d544ea955556963eb401675585d42ea27513a5555555a5956a55550058b162c58b162ea162c58b264c993263c9931e4c88882088858b162c993264c993264d1a3468e0aaaa89d13aaaaaa 24 16777215 10 1023
def hc_64_2 : Nat → Nat := unpackHintV5 0xd49934ce3998ca1509c45570bf5d3eb795f2aa235da301c89533748dd9d687d18280e9ba7bb54d76455c70f9536d4ceb6a78b561923a5c295a52be5b4c559a430e523dcd503212ef2cd150215edd1b89751aa43918e0710d66df08753c00021d 0x1d8b164dd9b162c58b766d695555551a000a0000000000aaaaaaaaaaa20155550f80000554015401601b762c59309544005551a9b545a8200000a9354baaa00000119c000001544005555555554402a823e001554b675558015458b555546a6d516a93555585d4aa8c8aaaaaaaaaaaaaa2e171f8fcb675551f54aa2c58b162c58b162c58b1750b45a3c7a8f1ea3c7a3c7b55151554d22d16970ea5c3a934baab33554b53554d5354d22c58b162d168f47b5554d22d16a753aab33542eaa472d9e96aa96961750ba89d550faa2296a0eaa8b162c58b45a3d963c7a2c58b162c58b163c78b162c58b16b42e5170b89cee61ecb2a5942d169359aaacc3ab30eb2cd170b85c2c59f985ab42da8fd42d85a2c593162c5e7162c593162c58b162c58b162c58f1e3c78f363c78f1e3c7971e6c78f1e5c78f1e3c98f262d168f1ea3c7a8f698f1ed42e171b28d944e770f28794c3d168b4d875361d49acd1e1d4787551ea9e59a2e162c5c2c5c2e859b167e85c2c59f955a5b3c7ea16b0b5162c58b168b47a3d162c58b162c58b162c58b1e3c58b5a1728b85c4e2730f5794bca168b49a4d55661d5987595e8b85c2e1730b5685b554c2d164c58b162c5e7162c98b162c58b162c58b162c78f1e4c78f1e3c98f263c78f1e3c98f1e3c78f1e4c793168b47a4c78f478f49a8f1e3c7ad42e171389c4ca2650f28794c3d168b49a4d261d498751e1d4787551ea9e57a2e162c5c2e162c9c2c5c2e8593167e955a5b3c7ea16b0b5162c98b45a3c7a3c7a2cb8b162c58bce2c78f162c58b162c5b0b45c2e2f17987a5e2f0b45a5d2eaa974bb25d170b858b858b2e2f3cc2d6175530b458b262d168f1e8f1e8b162c58b164c9b36168b85c4e2730f4bcae168b49a4d552e97657a2e170b170b1730b585d54c2d2e2c5931e8b478f478f599b162c58b2e6c78f1eb43e585c4e2f30f4b94aca668b49a5d552e1d4b8759668b85c4cfc5cfcc3d5a3ed5531f698b164c78b163c78f1e3c7935547a8f61713a9c3e1f2aaaaaaaaaaaa8b859f89c7cfcaab2ae78fd4aaa2ea0162c78f1e5c7971e3c7af1ebc58b162c7971e4c7a3d2e3e8000003a1d0e874797aa2f1fa1717566ce0a2c58b162d168f47b542c5d2f26fcbbf2ebc9850000000000000b45abd555f8757e1d402aaa985400001a6058b099704783c78b162c580172e2b6600f1ed319c00004381d0e94533404cb80f1e0f26283d1ec67002145858511f23eacb9c148162c58b009802c58b162c58b160003c078f001e3c78f1e3c98b45a020f01e8f1ed4467000000000088005a2d010382f51e1d4787551ea9c02a85c01411f0aa3f2ab4b670005a5262c5931e8b47a3d566c58b162d59baa1e3e8280000000000019a2d26935555875561d402aaa985400001a498b164c3600b02078f162c58b1e6c78f1e4c78f1e4c000780f1e003d168f498f1e80280f1e1500119c000000000668b49a4d010380f0ea3c3aa8f54e01547eaa27005047c155a5b38002d2bb162c98f45a3d963c7b2cd8b162c5cb363c7d55050000000000003345a4d66a8f54ecc3ab30ea01547eaa3f2c2aa0000000b4a00b00dbb162c9843c78b162c58f3603c7800000f1e3c7971e3c7931e8b41e0023da63c7b5000000467000000668b40e0024d668f0ea3c3aa8f54e401547e08f8005551f955a5b38002d28b162c5aaaaaa8b16acc9b32eccbb326aaaa2e173399caacca6652aaaaaaaaaaa8b45c2e172aad2ad52aaa2c58b161c387261d9870e2c58b162c58b161c3870e1c38f0e1c78f0e1c3871e3c7b31e3c7935555543a3d5547ac8b85c1ca0e53399c3ca1e52aab9d0ea875550e87555555555170b162e0e1e0f41c38b3f42e162cfcaab2b9e3f50b555262c59355552e6c58b162cb97551e3d555557c2e2713954b945ca555555555555170b89a4e555a55aa55262c5930e6c3870e2c3875478f162c58b1e6c78f1e4c78f1e4c3870e1c3871e1c38f1e1c3870eaaaa3d55543a3d595f0b89c4e0e507287943ca5555573a1d50eaaaaaaaaa8b938b3f13899327070f07a0e1cf9fa55595cf1fa93aaab3162c9aaaa8f599b162c58b666c78f5555555970b89cce5566533295555555555545c2e27273e7d555a558fd49d547b3c3877e59cfc3f0e03c1e1c3cb1ee722cf1f3f670e1c38b0e1c39b662c5935478f162c58b1e6c3871e3c3870e1c3870e1c3871e3c78f2e3c78f26aa8747aaaaaa8f5985c1ca0e51399c3ca1e52aaaa1d43aab9d5555555543a2e4e2cfc1c39f3f41c3c1e89c9cf9f9556573c7ea4eaaacc58b5eaaaa000000ccd8b162c5b336bc9b32eccbaf260a000000aaaaaa00aaab5554a200a000aacc58b5e3c78b162c58f363c78f663c78f26aaaa3d6401601b019804c001e0f00078020f011000800000000155543aaaaaaaa080039ea8fd547e55595ce11f000a000555 24 16777215 10 1023
def hc_64_3 : Nat → Nat := unpackHintV5 0xdc5d18d61991cf19c0c9d152c2b1c8b6def5ae721ba785bba1fd6293c78e8d39a383b26279e2747289d6665b0c5a57015485744c02214405ff41d48c3de0fd38256f32ed4e2ade0425c9451d721617f55f13951810b0b90ab180065118000194 0xb162c5aaaa93458b5551e3eaa95556aaa9562a29555555555556a85b54aab52aad52a8b162c5aaaaa4dce8b545aa3d56aaa9551915555555555556aa1767aa5555a58fad52ac2e89d44e955555569655a88a5555a858b162c58b162c58b162c58ba858b162d18f2e971eed265cb93aa8a8aaaaaa162c58b2e1cba5c39749972e4d397465eaaaaaaaaaaaaaaaa858b162c58b162d1a3aaaaaa162c58b4e9d3a74e8d1a7aaaa85d9eaaaaaaaa1744eaa9a87cd4454d41e6a162d458b16870f41c387858b162d18f5463d45a2d26935794bca170b89c4e646870ea1c3a8743a1d0eaac874387a162e85c2e0f0b985b54c1d5458b162c3870e4c3930e1c58b162c58b162c3870e1c387264c387261c3870f50b45a1c3a871ea4d26931ea4c7a8b85c1ca0e51389c4ca265323516e70e1d43870e1d0e870ea1c3aaac8745c2e0e1e838ba85d9c593a164c5b0b63f50b60e93162c993362c58b164c9d48c58b464c993264c793498f26af85c4e2713289948e470b169c993264c98726930e4d468d1a393af85c2e89d9c993a264cf9f8fd1fa8fc7e162c58b162d5526e75545aa2d51eab5554aa8c8aaaaaaaaaaaab5513b3d52aacaad2c7d6a9561750ba89caaab0f5555a587aad4452aaad42c58b162c58b164d193aaaaaa162c58b269d3934e8d1a7aaaa89d9eaaaaaaaa85d42ea3f4d43e6a22a6a0f350b164c58b162c58b162c58b2e6c58b162c58ba162c58baa162c5e7162c593162c5d42c58b165c7974b8f2e971e5d2e3cba4c993262e171728b945ca2e51389c8e470b162c5970e5d2e1cba5c3974b872e93264c9972e5cbc5cbc2e170b170ba165c59fa164c58b2750bb38b858b3f550b85c2e162ea858ba0a00162c58b268d193463d1a8c7a34000000000058b162c9a7564df874ebf0e9d468d1a300aa89c55000551f802a88162c58b162c58b0003e05cf800b162c5804c2e150b162c58083c0f8f3e9f1e7d268d193233800000004400002c58b16020703e1cfa7c39f49a7564d1a3468c02a808822744eaacf547e00aa005806cb97162c58b2e6c2800002898b162c5930aa462c5a307800971e5d2e3cba4c9932600000001100119c00b8b165c0e0025c3974b872e93264c9972e5cb90055047c002a2744eaacf547e00aa162c58b168b162c5a870f41e0e1c5a2d2697518f5463d45c2e27179994cca6468743a1d0e870ea1c3aaac8745c2e1707858ba0e1e9858b3ed530755162c58b162c58b0e1c3870e1cf870e5cf870e1c38b162c5870e1c9872e1c3d42d16870ea1c7a9f1ea5c7a934ba2e1707283947ca2e5138bcc8d45b9c38750e1c3870e1c3a870e9f50e8755643a2e17070f41c5d0b262c593a85d9d858b3ed530743870e2c3870e6cb97162c58b2e6d56a83870e1c3b24c58b26ad48d16871ea1c3a971ea5c7a9349aae1707283945ca2e51389cc8d0e8743870e1c3870ea1c3a5d4387549b9d564b870e8b85c1c39f3f41c3c1e8993264c9d44ecec8cf9f6a983a5c58b268d16934ba0010000ccd8b162c5b3361400a8c7a31ea00001d0e8753870eaa8052d2d544e29a8fa014000d25cd8b162c59f365c58b2752345a7c7a971ea4d2e802c03600170f8007c00b804c01e020000001000000743a1c3a870ea1d4e1c3aaa100039eaa2744eaaced47d200200693e6c58b162cf9b162c9d48c58b467c79f4f8f3e93468c9c2e3e51f289d2391c2c5a73e1cfa7c39f49a7268d1a3472785c2e264c99327513b39f919f3f551f8fc2c58b16aaab5554aaaaaaaaab5554ab54aa2c58b162c58b163c78f1f5555542c58b164c993263c78f1f5555544eaaaaaaa162c58b162c58b264c993aaaaaa162c58b264c9934e8d1a7aaaaaa89d9eaaaaaaa1750ba89d3543e9a88a9a83cd42c5aaaa2c58b55162d5555555551a2e173b29d944e772aaaaaaaaaaaaa8b85c2c5d0b1742e172aad52a8b164c58b179c58b164c58b16aaaaaaaa8d45aa2d52e9b554daaa9354baaa2e171b28d944e772aa322aaaaaaaaaaaaaaaaa8b85c2c5d0b1742e172d9d5545d52a8b162d162d55458b55555555555170b89c4e5e52f29555555555555545c2e170b858ba162e9556a954593162c58b179c58b262c58b555526aaaa4d1ea8b545aa4d526a9349aaa4d55545c2e271389944ca55464555555555555555555170b85c2e162e858ba5b3aaa8baa552e6c58b162d99b2e2c59355555555556172b28b944e2f2aaaaaaaaaaaaa8b85c7c7d0f1f44cfc5cfcaab54aab4aafcbaf26fcbaf262c58b160a00aaaa0000000000aaaaaaaaaa00014155542aa00ab02c58b1600ad985cb80132e28a2aac670000145528aaa52058b162c0263b05501105546a2d516a000a08024d55548ce000000000002a80882aaaaaaaa80550110552d9d5560055566c58b162d59b262c5935a55550500550000000000555555555500aa00a0aa1550055262c5930d802c08555526802823c136a8b549aa4d4001410054008ce0000000002aaa80882aaaaaa80555501102d9d5560055 24 16777215 10 1023
def hc_64_4 : Nat → Nat := unpackHintV5 0xe8cd18e21dacde44f6d97d32d4f921d1a0d6c84258be9e69b2e6eea69b139dea2c9609f89209008b61aa86e120807d997985be74115d6ad25064699a5abe6b53c1bf49f2744261e435fb1a2dc20e217f111bd16b12ae490a7a0d065509000195 0x13162c58b4b97555162d5555555555488882828455555415155401ced55555552ac12a93262c58b164f3932e4c58b16aaaaaaaa4444141422aaaaaaaaaaa00e74daa2d526a93549a4d5526aaaaaab20555555552ac12aab328b168b162c58b162db8b555555222228a1155455555550073b555554ab04aa2c58b162d555162c58b458b2f9d555554174559c88884516aab9d551555401ced555552ac12a9736dc59716dcd97265c9aaaaaaaaaa44141451422aaa0a8aaaaaa00e76aaaaaaa95609555554888845555555401ce9b545aa4d555555640aaaa5582555665a858b162c593162c58b164c1600b00586c00160b002058b162c58f168b162d264c99301078000000119c00000162c58b161c5a2c38b4993264c040e08d1a3460156785d42eaa0220aa00aaa801600b000582c00161b162c58b165c58b162c5930858b162c58f168b162d0780093468c9800000000046700162c58b161c5a2c38b40e0024d3b3268d1a34640156785d42e08f800555550055542c58b162c98b162c58b261c5870e1c5870e1c587361c3870e1c587161c3870ea8b45a2c7a8b16a4d26870ea1c7a8b85c2ca1651389c1ca0e532343a1d0e1d4387549b9c38750e1c3aac8761767162e858b162e17070f41c5d30b6a983b5070e1c5870e1c5870e1c387161c5870e1c387161cd8b162c58b2e2c58b162c9aa2d168b1ea2c5a871ea1c3a9351a2e170b285941ca0e51399cc8d0e87438750e1d43870e1c3aa4dceab29c38761767162e858b161c38b3f41c3c1e85c2e616d53076a162c58b166c58b162c593168b458f5162d51a8d005802c00160b000586c0660130078080000004000001d0e870ea1c3a8753870eaa84000e7ab3c2ea175534847c002801a6a162c58b166c58b162c593162c58b163c5a2c58b51a3468c5c2e1650b2a91c8e162c58b161c5a2c38b53a7468d1a393d0bb38b1742c58b170b85c2eaa170b858b162d55555458b5aa1e3e95556aaa9562a295555555555566aa9556956a95458b162d5526e75545aa2d51eab5554aa8c8aaaaaaaaaaaab0bb3d5552aacaad2c7d6a95561744ea2f4aaab0f5555a5956a2295556a162c58b555526aa8b16a3c7d552aaad5552ac5452aaaaaaaaaaac2daaa95556a555aa555162c58b555549b9d16a8b547aad5552aa322aaaaaaaaaaaac2ecf5554aaaab4b1f5aa55585d13a89d2aaaaaad2cab5114aaab50b162c58b162c58b162c58b1750b162c5a31e5d2e3dda4cb972755151555542c58b165c3974b872e932e5c9a72e8cbd555555555555555542c58b162c58b168d1d555550b162c5a74e9d3a7468d3d542ecf555555555527a1744eaa9a87cd4454d41e6a162e85c2c58b162c58b162c58b162c58b2e3d1a8c7974997465c9a3170b8b94aca271791c8e162c58b2e1cba5c39749972e4d197465e2ece170b858ba162e858b858b85c2c59faa85c2e0a00858b17542c5d0b162c5a31e8d463d1a4c9932600000000002c58b16ac3a755874e93264c9a3468d18051500055551f802aaa164c58b162c593162c58b058000b058002c016040b1e2d162c5a2c58b164c99326020f0000022002338000002c38b4587168b162c593264c98081c11a3468c021742eaacf540441547e00aa3f0b162e0a00162eaa858b162c9a3464d18f46a31e8d00002000000162c58b269d993661d3acc3a751a3468c8021715551b80002a8fc01547ea800160b0005800b0058b2e2c58b162c98b162c5842c78b458b168b162c583c0049a3464c000000000233800b0e2d161c5a2c58b1607001269d993468d1a320085d0baab3847c002aaaa8fc01547e0e1e83c1c38b162c58b162d162d45a2d2e3d4b8f5269345c2e2e517289c4e6468743a1c3a870ea1d0eaac8745c1e162e8387a170b9858b3ed53070e1da8593162c58b164c58b162c38b0e1c3870e1c587161c3870e1c5870e1c5870ea8b1ea2c5a8b45a4d26870ea1c7a8b285942e171389c1ca0e532343870e1d438745a8743a9373870ea1c3875590e8b162c58ba85d9c5c2e0e1e838ba6162cfb54c1c387458b162c387a0f070e2c5a8b458b168b49a8d463d518f5170b89cce665332991a1d0e870e8749870ea1c3aaaca70e1d162e0f0b170b858ba0e1e9858b3ed53070e1da83870e1c38b0e2c3870e1c38b0e1c387161c387162cb8b162c58b262c58b16a8b1ea2c5a8b45a1c7a870ea4d468b285942e1707283944e67323438750e1d43a1d0e1c3870ea9373aaca70e1d162c58b1750bb3871741c3d0b85cc2c59f6a983870e8b162c58b45a8d4680000005002f26ccbb32ebc9aa31e8c7a80000743a1d0eaa8052d2c2e2aa9a8fa014000d41da85b3162c58b164c58b162c58f5162d45a2d46a3400160b0005800b00580cc02600f010000220008000003870e1d438745a8743a1d4e1c3aaa100039e1742eaacf54d47d2002006a0ed42c58b162c593162c58b163c5a2c58b458b162d1a3468c5942ca170ba91c8e161c5a2c38b458b162d3a7468d1a393c2c58b162ea1767170b85c2c59faa85c2c59f858b162d555458b555aa1e3e95556aaa9562a29555555555556a85b54aab4ab54aa2c58b16aa9373aaa2d516a8f55aaaa554645555555555555aa85d9ea95655996a9561744ea2f4aaab0f5555a5956a2295556a 24 16777215 10 1023
def hc_64_5 : Nat → Nat := unpackHintV5 0xe983977e93cd067a31e51ac6e8571403dbb4cdeadffaab083aac200aa983aa3a36a8e802a3a00a760c6749488d5fe607f6c79644dbfb2f63ae217ce8e59cab9486f64a9bc108f0c39f424b25ac2444285a3b70eb3ec001d6 0x2d51e3cb9b55500b85c02e430586c2e1311002e02aa1c40739f8bc7c2362c59b155500000000055e4db976e5d79305000000555555005555170b91c8e5500467e919fa5554d8b166c78f1e4c78f1eae745aa2d55005806c001e0003c1e0004c041e022000000000000aaaaaaaa1d5504001ce2e170f1f43cfd2391caa1f002005516a8b162c5aaa82c1601721805c2e170b84c2622001722e00743aaa87101ce2e1750b09797262c1e1132ebc3a8e162c58b45a2aa80000002802f265cbaf260a000000aaaaaa00aaaa2e170b85caa002c5d0b174aaa8b162c58b164c58b162d16a2d55ceaa000b058002c005802c00098080800002c8000000010e87555555550eaa82000e7162e858ba170b85c2e5505801002a9b162cd9707846c58751c6c9a8f816d232e4cb935547a2800170000d8b166c14001400000155543aaa000aaaa8e47138bcaa3d00467e919fa551e3c78b1e2c79b2e4cb9355551ea3d55ce00b00d8003c1e000f002e013010100000002e00000aaaaaaaa1d5504001ce8e470f3f43c7d138bcaa3d0f801002a93264cda2d2e9740000000b97162c58b2f9c0162c004b974003a1d0e1d0e1d550090e8b85c5e2f333400bc5e60ea9b363c9971eb9c5a2d000362c59b1e3c78f2e5c7af5e3c78f05500555551f1f8fc7e5165cb8b162c993162c5a2d5ce0002d7af162c58b162c5972e2c58b160aa00aaaaa2e170b85c5c99726bd49a5d00000005e6cb8b5e2cb9b014b8f5e3d400003a1d0e1d0e1d5500a50f2b399c4e2f333400b9fa5e7e983aa3c9971eb9c5a2d0009855012aa1c6573d5297162c98b45ab9c00262e5f55010743aaa87195cf545c99726a4d2e800004c02a8069083a1d0eaf0e1d550a96673d55534805534ab26ac9aaaa800004c000017800002aa1d550400073a793c4e4f2a80002aaf5eabd401601b0002600f01000000000e8743a1c3aaa100039e97d321f0020060e9326aaa8b162c59355162d5555555548828288845554151555506aaaaaaa9560954993262c593ce2c593262c58b55555555220a0a2211555555555550073a6d516a974daaa5d5549aa5d55555902aaaaaaa956095559945a2c5aa8b16a4c9aaaaaaaaaaa9111050508aaaaa82a2aa8039daaaaaaaa558255162c9e7162c58b162c58b262d5555555488882828455555555555401ce8b545aa4d26a9355168b5545aaaaaaac8155555554ab04aaacca2c5aaa972eaaa2c5a2d555555542828888845514155555506aaaaaaa956095458b162c597162c58b162c9e7555555550585055111108a2d0eaaaaaaaaaaa00e745aaa8b45aaa2d516a9349aa5d55555640aaaaaaaa5582555665 22 4194303 9 511
def hc_64_6 : Nat → Nat := unpackHintV5 0xa0a149981e21931d408ac2178671147fa5b37b45187461b970011868e5c76461215d21d05c6c2d5a588556b8e852e4f54f10f549c5534620e941712c39e9e23529302d6def2984fa248d3e2090ff1a459310de5a1078190fe026093da900024f 0x2c5d55172f5542c5c2d58f5563d45a2d26974241488a0bc420a1c50e8743a1d55845aaaaaaaa698269162c58b166c58b162c58b279c58f5162d45a2d26974282888a0bc430baaa170baa85d42ea27517a5a87aaa1c3870ea1c3a2d43a1d0e875541ce0a05555555534c155553493162e365eaa858baaa368b49a4d663d598f522220509210e8743a1d0e282aac00d555555534c13493262c58b164f393364c58b166d169349a4c7a931ea44504e0aa098510c6ea17513a89d44e275513aa96a1eaa8743a1d0e870ea1c3aaa839c140aaaaaaaa6982aaaa695a55362c59b6e5db936e5db93555555552205052211554505555541aaaaaaaa55825554d8b166c78f1e4c7ab1e3d5ce8b545aaa44141450de118dd42ea1f0faa87d5513aa9555555555555555073828155555554ab055554aab4aafcbbf26fcbbf262c58b16aaaaaaaa0a0a4444220a8aaaaaaa80355555554ab04aaa8b562c58b162c98b162c5a2d45aab9d541614154445108c2eaa85c2eaa1750ba89d54aaaaaaaaaaaaaaa839c140aaaaaaaa5582aaaa55264c993666d98b662d99b5a555555555522220505115555450555401aaaaaaaa558255264c9931e6c78b1e2c78f55555ce8f547a44504e0aa078508c6ea17513a89d43e1f550faa9555555555555555073828155555554ab055554aaacdab16ac5ab365c99726b4aaaaaaaaaa440a0a505e11550545555541aaaaaaaa55982551e3c78b1e2c79b2e4cb9355551ea3d55ce441414505e118dd42ea1f5543e1f5513a8bd2aaaaaaa8743aaaaaaaa839c140aaaaaaaa55982aaaa55a16ae72752828002c2e2c5932168b573d511395442a8000b932e4c26ea004d2ed50513aa690e8740043a1d5502a8002a9a6a9a54d8b166c78f1e3d9b31e5cb8f1e3c7932e3e9738b45aaa44234aa22a15554a2cb97162c58b162c5b3662c58b165c58b2742d16ae7552211a551150aaaa2e6d98b2e2d99b2e4cb93a9598f52e3d49a5d22050928a210e87438a0a1c3a1c3aab00355555554d304d2aa445110c6ea17513aa96a1eaa8743a1d0eaa839c140aaaa6982aaaa69264c000162c9800b160aaaaaaaa0000000000aaaaaaaa5d5500170b8b97a2e7e89c5e550055264c98b164f38b164c98b162d55555554000000000155555554baaa0e7000d802c02e1b000b8001300b808080020b85c5cbd173f44e2f2a802a8107c058b0002e5c00058b05aaaaaaaa80000000002aaaaaaa9755400058ba162e85c2e170b954015458b162c597162c58b162c9e75555555500000590000002aaaaaaa975541ce000b000160b0005802c02601701010004162e858ba170b85c2e55005502058070e1c397265c9aaaaaaaa0000000000007026000002793c1e0f138bcaa00005cdaf165c5af365c9972602aaaaaaa800000000002aaaaaaaaaa8802793c9cfd173f44e2f2a802aaf5eaaaa000000aaaaaa839c003600b00980020200089e4f2793caa00aa041f00593164c99b45a4d2e8001700000009930162c015b8f6e3d400003a1d0eab0e1d5500a50f28b85c4e2f33340199fa667e983a4c993162c9e7162c993162c59b45a5c7a9b1ea4d2e802c036001b0002e1b00b801309803c040000000b800000743a1c3a870ea1d561c3aaa100039c5c2e2e6e8d9fa2717999a1f0020060ee747b9f38a3d0ee7162c58b058b279c5a2d26974000b800002c5800172e00a3c7a80000743a1d561c3aaa00039e943ca2e170b85cc2d00162e858ba60e8b162c58b362c58b162c593ce2c7a8b16a2d16934ba000b058002c005802c02e01300780800000017000000e1d438750e8743aac3875542000738b1742c5d0b85c2e1730b41600400c1d 24 16777215 10 1023
def hc_64_7 : Nat → Nat := unpackHintV5 0xab8e91a45dcc9b1e509609458f8d9f8b3d1484dd987fc94578f9b47439306e2d8368f54e625da65c059657153c4f9dde4af12b44b19040411c3b952b3b0c223539752e59b82a5cff289073252cd91ed9951a99101585450d5e0a085d40000217 0x162c58b165c58b162c58b279d168f55555555160b8582e162c58b265cb935545a1d55555555555ceaa8b555168b5545a6d5168b549a4d52eaaac88aa8b162e162c5c2c58b162c58b16aa2d162c58b555645a93262c58b164f3a5cbaaa8b16aaaaaaaaaaa6c58b364c99326bc8f2f23caaaaaaaaaaaaae755458b162c98b262d19f17233e2e554ea3168c5aa93262c58b164f3932e4c58b16aaaaaaaa6c58b364c993264c271309caaaaaaaaaaaaae7554daa2d526a93549a4d5526aaaac88aa8b162c593164c593262e267c5caa9d462d18b55564fad2aa9b162cdbf2ebc9bf2ebc9aa82802a80b00000000015414015550005c2e467e919fa472395401548362c59b00985c15404415416670000000154044155555ce009b545a800282009355550000545c2e020f82391caa9d0055564fa8b162c5aaaa891108aa02b726dcbb72edc9aaaad002aaaaaaa0aaaad5552ac155552a8b162c5aaaa82cce144422044ea2f4aaab52aaaaaab9d0555590ea8b545aa4d556aab30022b32ab2aaad5552acc155552aab32d2aac72ebc9c72ebc98b162c58002aaaa80000000000002aaaaaa000b1742c5d0b85c2e172a8b4015420b8004c58b162c11e000aaaaa00002cce00002002aaaaaaae7000400001516a8b549aaaa8300002a0b002170b85c2e5516802aab22d4d8b166d5554a05a44220aa91c9c72f1cbc726aaab400aaaaaaaae75055556aaa95660aaaa954d8b166d555428166722110227517a5555a95555555ce82aaaa9b545aa4d556aab002b32ab2aaad5552acc155552aab3293264c9ab36ac5ab16acdd2aaaaaa828000013000000015554140150011c8e2713919fa467e9553a00aa4c993261b005810aaaa0220001333800000aaaa0220aaae7004daa2d526a9350005040150000551c8e27138083e0aa9d0055564fa97265c9aaaa9104cce14231ba85d00aaab52aaaaaab9d415555536a8b549aa5d556600456655657aaab5554ab3055554aaacca5cb97165c597365c997274aaaaa000aaa0000000000aa000aaaa8008e47173f45cbd138bcaa00aa00b00d97265c984aa08f000555000000266700550438002aaaaab9c40136a8b50400001526a975541800015472380fa300093938bcaa9d0055564fa93264c9aaaa91141344639b8e2e38b8e6c15515556801555555550555665aaaa55982aaaa55264c9935555220a0999c463750ba015556a555555573a0aaab21d536a8b549aa4d556005665565555aaaa55982aaaa555665165cb8b162c597458b16a2c597166c9aaaaaaaaa2d5ab2e5d5912aaaa8b162c58b85c8b2e5cb8b165cb97162cb9752e5c58b162c58b5555555559b565cbab2255555462cb8b371f94e8b5555458b168b162c58b162c5aaaaaaa8b162c5ab2e5d58b162c5aaaaaaaaaaaaa8b162c58b162c58b162c5aa8b458b162d5458b162c5aaaa2c58b168b165f3a2d5573aaaa8b162c58b162c5972e5cbaaa2d5573aaaaaaaa8b162c58b162c58b162c5aa8b458b162d560d8b166c015bf0b970058b0264c2e5c514555166700001590a2aa91f0fc7e538b162e85882a80b33802aa8b85c8b20b97000158b162c5970262c5aa0aaa800b338020aaa8b085c2e4597362cb8b365c99726aaaaaaaaaaab56ac2f1715c4cb9726aaaaaaaaaaaaaaa8d3a34e8cf978b9f4f132e5c9aaa751a7469d555555555555555ceaa9b545aa4d555591155469d1a7469d1a7554ea34e8d3aaab27d4993aaa858b27542c5d1b45aac7aab1ea4d2e91028494178843a1d0e2828743aab0355555554d304d24c993162c9e7162c993162c59b45a5c7a9b1ea4d2e91050514178863750ba8bc6eaa375544ea2f4b50f5543a1d0e1d438750e875541ce0a05555555534c15555348b858baa162e8993aaa168b49a4d663d598f522220509210e8743a1d0e282aac00d555555534c1348b164f38b162c58b162c593162d169349a2c5a8b1ea44504e0aa058510c2ea17513a89d42e17550baa96a1eaa8743a1d0e870ea1c3aaa839c140aaaaaaaa6982aaaa69 24 16777215 10 1023
def hc_64_8 : Nat → Nat := unpackHintV5 0xc925acc4b51cbe5598b91d4eb285a6ac2d96a72d409fe9d19b3d2b94fd9091b4d28e6cd287e1a383a1107a6a4e71324e67fa4e5e327257a1a45189864af9a44479a03de9a437c18a30d9ba2a8d9326550e1fd99f1652620fb1a806465b000191 0x105c00262c58b1608f0005555500001667000010015555573aa800200000a8b545aa4d555400015058010b85c2e172a8b401555916a6c58b36aaaa4244220aa93c9c72f1cbcf26aaab400aaaaaaaa82aaab5554ab3055554aa6c58b36aaaa140b3391088113a8bd2aaad4aaaaae75541555643aa6d516a93555aaacc008accaacaaab5554ab3055554aaacca4c99326acdab16ac5ab374aaaaaaa00a00004c0000000555505004500472389c4e467e919fa551e802a93264c986c016042aaa80880004cce000002aaa80882b9d540136a8b549aa4d400141005400015472389c4e020f82a8f40155593ea5c99726aaaa4413338508c6ea17402aaad4aaaaae75550555554daa2d526a97555980115995595eaaad5552acc155552aab32972e5c597165cd97265c9d2aaaaa8002a80000000002a8002aaa8a802391c5cfd172f44e2f2a802a802c0365c9972612a823c001554000000999c01544005555ceaa2009b545a8200000a9354baaa0c0000aa391c07d180049c9c5e551e802aab27d4993264d555488a09a230cdc3170c5c3360aa8aaab400aaaaaaaa82aab32d5552acc155552a93264c9aaaa910504cce231ba85d00aaab52aaaab9d550555590ea9b545aa4d526aab002b32ab2aaad5552acc155552aab32c1b162cd802b7e172e004cb8a28aaa2cce000028aaa47c3f1f91e4172e0002b862c58b165c09aa0aaa800b338020aaa8b085c2e4597370c597170cd97265c9aaaaaaaaaaaad5ab0bc5c57132e5c9aaaaaaaaaaaaaaaa3468d1a33e5e2e7d1c4cb9726aa3d468d1a3555555555555573aaaaa6d516a9355556445551a3468d1a3468d547a8d1a346aaac9f5264c98b164f38b164c98b162d0ea87543a1d550e875543aa1d5555555555362c59b2e1b8d85e265cb934645555555555555555ceaa2c58b165cd8b8d9f1713165c5ab21d55518b462d5458b279c58b162c58b162c98b43aa1d50ea87543a1d550e8755555555555458b162c993264c582e160b919155555555555555573aa8b162c58b162c58b162e162c5cac87555162c58b55162c58b166c58b162c58b279d0e875543a1d550ea87543aa1d5555555555160b8582e162c58b265cb934645555555555555555ceaa2c58b858b170b162c58b162c5ab21d55458b162d54993162c58b279c99b262c58b43aa1d50ea87543a1d550e8755555555547a3d55362c59b264c99326138984e464555555555543a1d5555573aa8b162c593164c593262e267c5cac87555462d18b5520d8b166c0265b043aa1d4001410e0087543aaa80882aaa0b33800000000000aa0220aaaaaab9c005c2e020f82391cac875550055162c58b43aa1d50ea87555555416670a220605110227537a555a583aaaaaad4aaaaaaaab9d055556aaa95995560aaaa95422d8004c58b162c10e00000a87543aa1d50ea2002aaaaa80000b33800000000800aaaaaaaaae700058010b85c2e172b21d5540154d8b166d0ea87543aa1d5555550a0599c88181444089d56e9556960eaaaaab0f5a95555555573a0aaab21d6aaa95995560aaaa954993264c3600b0210ea87543aa1d4001410e00aaaa0220a8004cce0000000002aaa80882aaaae700472389c4e020f82b21d5540154b932e4d0ea87543aa1d555555220999c281814463750ba01556960eaaaaab52aaaaaaaae75055555aaaa56655582aaaa55005806cb932e4c243aa1d410e00000a87543aaa8800aaaa0000004cce000000aa2002aaaaaab9c4011c8e03e8c0024e4e2f2b21d5540154993264d0ea87543aa1d555555220a0999c1814463750ba01556960eaaaaab52aaaaaaaae741555643ad5552b32aac155552aa1d50ea87543aaaaaaa8c8aaaaaaaaaaab9d551a3468d1a3468d590eaaa8d1a346aa4c9aaaa2c58b164d5458b555555555362c59b2e178b85e265cb9355555555555555162c58b2e5c5c5cf8b898b2e2d5518b462d54993262c593ce2c593262c58b55555555362c59b2e178b85e265cb93555555555555573aaa6d36a8b45aa5d36aa9755526a9755591155162c58b2e5c5c5cf8b898b2e2d553a8c5a316aaac9f5164d162c5aa8b16a4c9aaaaaaaaaaa8b162c593264c9af23cbc8f2aaaaaaaaaaaaa8b162c58b162c58b162e162c5caa2d162c58b55162c9e7162c58b162c58b262d5555555458b162c993264c582e160b95555555555555ceaa8b545aa4d26a9355168b5545aaaab222aa2c58b162c58b162c58b858b172a8b458b162d555916a2c5aaa972eaaa2c5a2d55555554b85e2e17858b162c9972e4d5555555555555458b170b162e162c58b162c58b55162c58b55 24 16777215 10 1023
def hc_64_9 : Nat → Nat := unpackHintV5 0xb2bdc6ae3123a7e992a5b88c9ee1b69809b69131b68a11c8854533809d2a7bf52a76f540724d2a6d952e6ac8b365e5396109375e88a05a5d0b5419914ada5044719a3b325034dd952b566224dd9e1b566216653c0fc9a70b452105398300014e 0xb00d97265c984aa2002aa9b545a8200000a9354baaa0000004cce000000aa087000555573aaaa2008e4701f460012727179555694fa802a93264c9b336cc5b316ccd82aa2aaaaaaa9110850288aaaaaaaa1d555541aaaaaaaa558255264c99355554daa2d526a93554882826671106058dd42e805555555a5956a5555573aaaa82aaac875aaaa5555a5960aaaa95458b162d5556aaa95555555556aaa956a954993262c593ce2c593262c58b55555555362c59b2e6cd9f367cb9b265cb9355362c59b2e1b8d85e265cb93553e7cf9f555555555555555162c9e7162c58b162c58b262d5555555458b162c993264c58b167c59f162d5458b162c993264c582e160b954f9f3e7d55555555555555458b162c59b162c58b162c9e755555555167c58b162c59f162c58b265cb9355160b8582e162c58b265cb93553e7cf9f555555555555555264c58b162c9e7266c98b162d5555555268f5362c59b264c993264c99f267c99355362c59b264c99326138984e553e7cf9f55555555555555520d8b166c0263b055011055362c59b00f87c0f9f3e7d54166700000000003eaa0220aa2aaaa002c58b16aaaa2c58b167cf9f3eaa0b33851108910113a9bd2aaac7ea3f552aaaaaaaaa0aaaa843b00098b162c58800aaaa87c003e2c58b167cf9f3eaa00002cce0000002002aaaa2aaaa006c58b36aaaa6c58b367cf9f3eaa140b33910887e28089d4ee955561eb1fa8fd54aaaaaaaaa82aaaa4c993261b005810aaaa02207cf9f3e4c9932601f0f82a8004cce00000002aaa80880aaaa8017265c9aaaa9f3e7cf932e5c9aa9104cce1422451ba85d00aaab1fa8fd54aaaaaaaaaa0aaaaa5c99726aaaaddbb76e4e2e4d54000000015554555540001601b2e4cb930954400554f9f3e7c0f9f0003e4cb9726aa0000004cce0000aa2002aa2aaaa2004c99326aaaa7cf9f3e4c99326aa44141333889146ea17402aaac7ea3f552aaaaaaaaa0aaab21d55554f9f3e7cf9f3e7d5554f9f3e7d55555555555555536a8b549aaaaaaa322aaaaab9d55555469d1a7469d1a7555594faa34e8d3aa9326aaa8b164d5458b555555555362c59b2e178b85e265cb9355555555555555162c58b2e5c5c5cf8b898b2e2d5518b462d54993262c593ce2c593262c58b55555555362c59b2e178b85e265cb935555555555573aaaaa6d516a974daaa5d5549aa5d5564455458b162cb9717173e2e262cb8b551ea3168c5aaab27d45a2c5aa8b16a4c9aaaaaaaaaaa8b162c593264c9af21cbc872aaaaaaaaaaaaa8b162c58b162c58b162e162c5caa2d162c58b55162c9e7162c58b162c58b262d5555555458b162c993264c582e160b955555555555ceaaaa8b545aa4d526a8b45aaa2d555591155162c58b162c58b162c5c2c58b9545a2c58b16aaac8b5162d554b97555162d16aaaaaaaa5c2f170bc2c58b164cb9726aaaaaaaaaaaaaaa2c58b858b170b162c58b162c5aa8b162c5aa8b162c58b2e2c58b162c593ce8b47aaaaaaaa8b05c2c170b162c5932e5c9aaaaaaaaaaab9d555516aaa2d16aa8b545aa4d52eaab222aa2c58b858b170b162c58b162c5aa8b458b162d555916a4c58b4b97555162d55555555554d8b166c993264d790e5e43955555555555555458b162c98b262d19f17233e2e551ea3168c5aa93262c58b164f3932e4c58b16aaaaaaaa6c58b364c993264c271309caaaaaaaaa9343aab9d555536a8b549aa4d526935549aaaab222aa2c58b164c593164c98b899f172a8f518b462d55593eb4aaa6c58b36fcbaf26fcbaf26aa00a0aa0000000000aa0a00aa8a002e17233f48cfd2391caa00aa41b162cd804c2e0aa0220aa0b3380000000aa0220aaae755004daa2d4001410049aaaa8300002a2e170107c11c8e551e802aab27d458b162d555416944422a80adc9b72edcbb726aaab400aaaaaaaa82aaab5554ab055554aa2c58b16aaaa0b338511088113a8bd2aaad4aaaaae75541555545aa2d526aab5558015995595556aaa95660aaaa955599695571975e4ef975e4c58b162d40015554000000160000000aaaaa8a002c5d0b1742e170b85caa2d0055 24 16777215 10 1023
def hc_64_10 : Nat → Nat := unpackHintV5 0xb4dde2ae699daa310ea415879fb11999958797648c9470bd8f115888cd917f86527941916ffa5269a59560166459c19550326449c99a44d93c41b4c93b459c36f51430ad922bad402840db21d19c1d711817299212393c0bada3056d9000015b 0x1c387161c38736ac9ab26a802c0360007038001c00b804d5555555410000000000004ceaa8750eaae71001550004723839fa0e1e89c8e0f8012a802a870e1c5870e1cd9326aa871ea1c3a9350e078381e264d43a1d0e1c3870ea9373aa87438753a70e7c3c1c38789a726a753a74387458b162d555416944422a80a1c3d552aaad4008aaaaa4d55415555aaaa5582aaaa55162c58b55550599c288844089d44e95556a555549b9d5505555516a8b543aaaaacc008accaacaaab5554ab055554aaacca4c58b26aaaa502d221105540e1eaa95556a0045555549b9d55415555aaaa5582aaaa55262c59355550a0599c8844089d44e95556a555549b9d5505555536a8b543aaaaacc008accaacaaab5554ab055554aaacca4c99326aaab5554aaaaaaaaab5554ab54aa4c99326aaaa000000aaaa4d55004e9d3a7264c993550055264c99355555ebc993264d55555526e755554daa2d50eaaaab288aaa9d3a74e4c99326aa9d3a74eaaac9f5264d555162c9aa8b16aaaaaaaaa6c58b36dc6f371bc4cb9726aaaaaaaaaaaaaa2c58b168cf8b919f1713165c5aaa3168c5aa93264c58b279c58b264c58b16aaaaaaaa9b545aa5d36aa9b55526a97554d8b166cb86e361789972e4d551915555555555ceaaaaa8b162c597362e367c5c4c59716aaab0b53ea8c5a316aa2d162d5458b5264d5555555555458b162c993264d78ce5e3395555555555555458b162c58b162c58b170b162e55162c58b55162c9e7162c58b162c58b262d5555555516a8b549aa4d5168b5545aaaa8b162c593264c98b05c2c172aa322aaaaaaaaab9d55555162c58b162c58b162c5c2c58b9555616a2d458b162d5458b5552e5d55458b45aaaaaaaab71dcdc770b162c5932e5c9aaaaaaaaaaaaaaa8b162e162c5c2c58b162c58b16aa2c58b16aa2c58b162cd8b162c58b164f3aaaaaaaaa2d5545a2d5516a8b549aa5d55160b8582e162c58b265cb9355464543a1d555555555ceaaaaa8b162e162c5c2c58b162c58b16aaab0b516a2c58b16aa4c58b4d97555162d55555555554d8b166c993264d78ce5e33955555555555555458b162c98b262d19f17233e2e55462d18b55264c58b162c9e7266c98b162d5555555268f54daa2d526a93549a4d5526aaaa6c58b364c993264c271309caa8c8aaaaaaaaaae755555458b162c98b262c99317133e2e555585a9f5462d18b552e6d98b2e2d99b2e4cb93555555555555ab56178b8ae265cb93555555555555555469d1a7467cbc5cfa789972e4d551a7469d556955b975e4db975e4cd8b166c14015554000000000001415554540119fa467e85c2e472395401560d8b166c015b30b9700265c514555166700001455523e1f8fc41b162cd804c760aa0220aa9b545a800282009355550599c0000000000055011055573aaaa002e170107c11c8e5555a53ea00aa2c58b16a80adc9b72edcbb726aaaaaaaa2444140a22aaaaaaaaaa8355555554ab04aa2c58b16aaaa8b545aa4d556aa82cce1444220c0a044ea6f4aaaaaab4b2ad4aaaaae755550555590eb5554aaab4b2c155552aad2a8b162c5b72ebc9b72ebc9aa8002aa80000000002aa8002a8aa800b85c2c5d0b1742e172a802a905cb8000ad98b162c585cb804c9aa0aaa800b338020aaa8b085c2e08760013162c58b100155550400001516a8b549aaaa80000b33800000000800aaaaab9d55500058010b85c2e172aaad28b50055362c59b05546e4db976e5db935555555521220a05115555555555541aaaaaaaa558255362c59b55554daa2d526aab55428166722110605022753ba555587aaaad2cab52aaaab9d555415555aaaa5555a5960aaaa95559b562d58b566c993264d69555414015400000000015401415454011c8e467e919fa27139540154993264c3600b0215554044136a8b549aa4d40014100540026670000000001555404415ceaaa802391c4e270107c1555694fa802a97265c9aaaaa6d516a9354baaa44133385088302c6ea17402aaaaaad2cbd56a5555573aaaaa0aaaab5554aaab4b2c155552a97265c9b736dc5b716dcdad2aaaaa800280000000002aaaa8000aa8802391c4e2f236e7cfd233f37a550055 24 16777215 10 1023
def hc_64_11 : Nat → Nat := unpackHintV5 0xe68190e2a0f8ddf52bd745acd35cfacd1d90c651b3c1d120baadc9b5fd2ca7c78e991faa92d9918722ee8071ac7502dc69cace63c9805ad63d55994f4cf6294651a93d7637385d46329d70299a4121261d1a75ac10d6680c85140535d400014d 0x162c58b55550599c288844089d45e95556a5549b9d555500555590ea8b545aa1d55556005665565555aaaa5582aaaa555665170b16aaaa000000aaaa97738aa000aa2d50001540015170b85c2e55005555a5550e1c00058b162d555555540000000000001555262aaa0002c5d0b1742e170b85caa00aa1017000264c58b162c400555540000599c000040055526e755550000400001516a8b543aaaaa0000a82c0085c2e170b95401555916a6c58b26aaaa4244220aa9541c3d2aaad002aaaaaaaa0aaaad5552ac155552a9b162c9aaaa8502cce4422044ea2f4aaab52aa4dceaaaa802aaac8754daa2d50eaaaab002b32ab2aaad5552ac155552aab32932e4c99326aaaa4413338508c6ea17402aaad4aa9373aaaaa802bd555643aa6d516a8755555980115980111555aaaa5582aaaa5556653e7cf9f264c993a264d55555400000001555526e755550004daa2d5953ea875555400015005806c993264c255100155000000261300550438002a4dceaaaa200026d516a0c00000a875555418000154f2780f80049c9c4e550055564fa9326aaaa4c9aaaaa4dceaaaaaaa6d516a8755555911554e9d3a7269d393554e9d3a755564fa93264c3870e2c38b0e1c39b0e6c3870e1c38b50e1c38755162c9e7162c993162c5aa6d16971ea5c7a871ea1c3a9349a6c58b365c2f170bc1c0f0703c4c99326ab568743a1c3a5d43870e1d43870e1c3aa4dceaa1d2e1c3a2c58b165cb8b8b9f17073e1e0e1c3c4c593168b66ab16ac5a1c3a2c58b0e1c387550e1c3870e2d43870e2c38b0e1c38b0e6c58b262c58b162c593cea8b1ea2c5a8b45a1c7a870ea4c9a4cba2c170b05c2c58b161c0f0703c4c993265c9aad5a1c3870ea1c3a2d43a1d0e1c3870ea9373aa874b870e8b162e162c5c2c58b161c58783870f0b162c5a2c5a2c58b16870e9b4593550e1d478f55555555555362c59b26ddb936e379b8de55555555555555162c58b262d18b467c5c8cf8b95518b462d5550e1c38b0e1c39b0e1c3870e3c3870e1c3871e1c79b162c98f1e3c98f2e3c7aaae745aa2d43a3d555554d8b166c783e1e0f8381e0e0789b76e4d555555550ea1d55ceaaaa1d162c58b1e3c5c3cf8b839f0f070e1e262d18b55462d18b55162c5a1c3aaa8b16aaa8b55555555162c58b26edb936e479b91e555543aaaaaaaaaa87458b162c58b162c58b170b162e55162c58b55543870e1c38b0e2c3870e1c38b0e1c387161c387162cb8b162c58b262c58b16aa2d45aab9d555554582e160b858b162c381e0e0789bb6e4d555555550ea1d55ceaaaa1d162c5c2c58b858b162c38b0f070e1e162c58b55162c58b551e3c78b1e2c79b0e1c38b0e1c39b55555555264c9932e4d555551ea1d1eaaaa8f5573ab56ad58f07c3c1f0703c1c0f13264c9aaaaa1d0eaaaa8750eaae755550ea3468d18f3e3e1e3c7c1cf8783870f13264c9aa8f51a3468d54d8b164c3c1c3870f40a006d169355adc7ab71ea000000000001d0e874438700055000170b89cae6e7e9b9fa67e80307480e1c38b0e1c39b0000e01c3801b162c9804c2e0a9b45a020f00e3d4387526ab41667000000000e400001d0e8081c03870e1c3aa4dceaa0002e170107c039fa0e1e89cae640183a2c58b161c38070387a59a168b49aad563d558f505c5110505108743a1d90e1d6955606aaaaaaa9a609a43870e2c38b0e1c38b0e6c58b162d5168b438f50e1d49aad0599c2828288884083d550783d544ea2f4b50f5a83a1d0e1c3870ea9373aac00d32d070eb55555554d3055554d22c58b161c3d0783870500168b49aad6e3d5b8f50001667000000000e8743875126e70e1c001540005c2e170b858ba162e985a00c1d080387000000e1c387161c387161700098b162c5aa0f001168b438f50e1d49aad0000166700000000038008743a1c3870e1d526e755000058010b85c1c5d070f42e1730b40183a6c58b261c0e1c3870a59a368b49aad563d558f522220a0a210e8743b21c3ad2aac0d555555534c13482c5970e1c3870e1cd87374b529b45a5d2e871e870e911101e8aa210e874387592ee70e1c3aac00d55555534c134870e1c587161c387361cd9b162c9aa6d16871ea1c3a9355a140b3381c282a88884083d550783d544e27517a96a1eb50743a1c3870e1d526e755801a65a0e1d6aaaaaaa9a60aaaa9a43870e2c3870e6c993264d56ebb438f50e1d49a4d22038505504cce14431ba85d4855002a80b50f5a83a1d0e1c3870ea9373aad00070ed32d070eb55555554d3055554d27cf9f3e1c387161c3873741cf870e1e264c993a264d546a34fa7d0e3d43875269340000000000003a1d0e8743870e1c3aa4dceaa00000b00d870e1c5870e1cd8500000293264c9972612add6e83c00438f50e1d49a4d000000000e4001333800743a01c38002870e1c387549b9d540e0003399c07c0024e1cfd070f44e2733340183aac9ab26acdab16ac5ab374aaaaaaa0a8a44440a0a22aaaaaaaaaa8355555554ab04aa1c387161c38736ac9ab26aaaa1d1eaaaaaa44141444267058dd42ea0f5541e0f5513a8bd00aaaa1d43aab9d5500555590eb55555554ab055554aaac9ab26aaaadcdb716dc5b7360a00aaaa00000000000aa8745555000000472389c8e55467e919fa0055 24 16777215 10 1023
def hc_64_12 : Nat → Nat := unpackHintV5 0xbb48afb6992caf09e4aaa519a45d92a0c4e69c591b9581b693508c8ecd218a611b85853780f5247da4d4789943725591670ad360c5915532e54fe15447f1fc43093a3db954359e0731291d2a65b122f5dc18d2890ee67b0a5d2203d9a10000f6 0x1c58b365c58b265e2e4d555554000000015155555400d8b166cb8b164e8b93555555000000005545b9d555554010ea7d3ea9f5526a97555550000540160b00d86cb8b164c2551001550000002667005545b9c10e000aaaaa200874100000549a4d52eaaaaa8300002a2e1701f00085938bcaa00aaab4a7d498b164d555488282667444387aaa05545555a0055516aaaaa0aaaccb5554ab055554aa4c58b26aaaa4414133388c6ea17402aaad4aa8b73aaaaa0aaab21d50ea4d526aaaaac00accaacaaab5554ab055554aaab4b287162c986c00562aaa802000000000a8aa080aa002e17278bc00aa00aa0006cce1c58b2e0002aa8802a80000005cce00a800039d55544005c2e0002f179540154387162c58b361cb9b162c99b55555555554d8b166d585e2e2b89972e4d55555555555555458b162d39f17173e2e262cb8b554e2d38b55162c58b5555aaaa5555555555aaaa55aa55262c5930d802c0855550110000999c000005455011055000f0b364c9932601f0f82a802a97162c9aaaa9104cce14231ba85d00aaab52aaaaaa82aaaa87a89972e4d560aa3f1fa55005806cb8b164c25510015500000026670054100155551000f0b3607cf8001f4e4cb9726aa00aa4c58b26aaaa4414133388c6ea17402aaad4aaaaaa82aaac8750f513264c9aac1547e3f4aa6c58b36aaaa6c58b36aaaaaaaaaa1c58b367cf9f3eaa7cf9f3eaa6c58b36aaaa6c58b36aaaa8b73aaaaaaa1d49aaaaaaac88aa8b162c5a7169c5aaa7169c5aaaaca7d43875551e3d55498b49aaaaaaaa970bc5c2f1b162cd93264c9aaaaaaaaaaaaaa973e2e2e5c5c2c58b164c59316aa8c5a316aaa93162c98f1e3c98f263c787361c387161c3871e1c7870e1c3871e1c3870e1d5573a2d516aaaaaa9b162cd8f07c3c1f13264c98703c1c0f2aaaaaaaab9d0ea875555458b162c78f170f3e2e262c98b0e1c3c1cf8795518b462d54387555458b16aa2c5aaaaaaaaa8b162c5970bc5c2f13264c9aaaaaaaaaaaaaa8b162c58b162e162c5c2c58b16aa2c58b16aaa8b262c58b162c98b162c587161c3870e1c38b0e2c3870e1c38b0e1c38b0e1d545a8b5573aaaaaa8b05c2c170b162c593264c98703c1c0f2aa1d0eaaaaaaae743aa1d5555162c5c2c58b858b162c58b162c3870f07161e55162c58b550e1c3801c38b162c5d2d48b45a5c7a971ea4d2691050511108743b4a1c3ac930e1d5581aaaaaaaa698269162c58b0e2c3870e2c387545a2d2693438750e3d416670a220a0a210227513a83c1eaa0f552d43d6a0e87526e70e1d43870eab034b075aaaaaaaa6982aaaa69058b261cb870e1c3872e1cda2d2e974387438f48888a28843a1d943a870e1d5606aaaaaa9a609a403870e1c384c58b274b526d16971ea5c7a9349a44141444421d0ed2870eb24c38755606aaaaaaa9a609a498b164c39b0e1c38b0e1d5368b49a4d0e1d438f50a0599c88282884089c4ea27541e0f5507aa96a1eb50743a9373870ea1c3875581a583ad555555534c1555534972e5c597165cd93264c9d2aaaaa282aa9102829108aaaaaaaa8755506aaaaaaa9560954993264c39b0e1c38b0e1d55555555522220a0a13382c6ea17513a89d41e0f5507aa8055555ce87543aaa82aaab55555554ab055554aa4c993261cd870e1c5870eaa9349a1c3a871eabd793264c98703c1c0f2bd0e87526e70e1d43870eaa1d0ea74e4c993261c387839f0f29d4ebd3a1c3a4c993162c9e7162c993162c5aaaaaaaa9b162cd970bc5c2f13265c99326aaaaaaa9743aa4dceaaaaaaad4da6d5168b543a1d5516875543aaaaac88aa8b162c5972e2e2e7c5c4c59316aa9c5a716aaac9f5162c58b164c58b162c58b264d55555554582e160b858b162c993264d55168755555549b9d5555555a8b43aaa1d0eaa8b4daa2d16a875555591155162c5c2c58b858b162c58b162d5458b162d555916b4aaa6c58b26001c382aaaaaaa80000000002a828022aa8000b85c9cfd273f44e4f2a802a906c58b260130b82a80882a82cce00000002a808824dceaaaa0009b545a80028200875555400015170b8083e04e4f2a802aab27d458b162d55544888455016a8387a5555a005555555415555aaaa5582aaaa55 24 16777215 10 1023
def hc_64_13 : Nat → Nat := unpackHintV5 0xa16d9195dae595c80495c80095b80494b84094b80094b80094840d8e459082d6dc7ce57c73e6406f8d16670a216051ae5975b7505a474c290c46ad5f3e022b398d1d35c8f12ed9bc29d9402555211df9d71689dc11ed270b35ae04d598000135 0x162d555162c5aa870eaaaaaaaaa2c58b16bc672f19c4c99326aaaaaaaaaaaaaa2c58b162c58b858b170b162c5aa8b162c5aaaa1c9870e1c387262c58b161c38f0e1c3870e1c3870e1c78f162c58b162c58b550e8f555555573a3d51e8703c1c0f0b162c593264c98f07c3c1f2aa1d43aab9d555555555438b0f070e1e162c58b162c58b162c5c2c58b95458b162d562058f2e1e1e81d462e10e2c58b458b5550e1d555551eaaaaaa2c58b164cb972644aa87555555555555162c58b162c58b162c5c2c58b9545a2c58b16aaa870e3c7870e1c3870e1c3870e3c58b162c58b162c3970e1c3870e4c58b162d555555547a8f55738703c1c0f0b162c58f07c3c1f132e5c9aaa1d43aab9d555555555438b0f070e1e162c58b162c5c2c58b858b162d545a2c58b16aa0a002c58b161c3878387a168b558f5563d49a4d000000000000e8870e0001d0eaa800b85c2c5d0b1742e1730b40183aa87261c3870e1c98b162c581c000381c001600b02038f50e1d45a2d26934041e00000072000999c000000e1c3870ea8b738743a0207055000e2e8387a170b85c2e0205830b40183a2d162c5a2d2e97488282e67886a85c150709a6a0ec8743aab401da60ed55534c15534aa1c3970e1c3870e1c993162c58b0e3d43875168b49a5d0a0a220999c28860f2faa83c1eaa1750ba016a1eb5070e1c387545b9c3a1d55a00ed2c1d6aaaaaaa9a60aaaa9a458b162c1400387a0f070e2d16934badc7ab71ea000004cce0000001c3a88b738743a1c38002a81c005c2e170b858ba162e985a00c1d5439f0e1c3870e7c58b162c3970e1c3870e4c58b162e858b0e3d43875168b4fa7d269740000000000003870e1c3aa2dce1d0e8743aaa00a8001c0e0007001600b0e5c3870e1c393162c58b0838f50e1d45a2d07800934ba00000000004cce001c3870e1d516e7038008743aaa07000e2e8387a170b80580042c5c2e6168030745a2c58b45a5d569105ccf0510d50ba5734d41d90e87556069a83876aaa9a60aa9a6966858b162c3870e070e02d16b31eacc7a9349a44141444421c3b22c3870eb4ca1d0eaac0d555555534c134aa1c3930e1c3870e1c993162c58b0e3d43875168b49a4d0385055110504cce4307aaa0f07aa85d42e805a87ad41c3870e1d516e70e875560699683875aaaaaaaa6982aaaa69a555162c58b7e5df937e5df9355054555220505221143aaaaaaaaaaa0d55555552ac12aa872e5c3870e1c3870e5e18b162c5970e1c9d2a88a9108d0743ab9d56aaa950eac3870e1c393162c58b43a3d55555554282888884ce0b07aaa0f07aa85d42ea275500aa1d43aab9d5555055556aaaaaaa9560aaaa95458b162d555414017936e5db975e4d5554000000000014555554000005c2e170b95458ba162e8015543972e1c387264d5543975e1c3870e1c3872e5c58b162c154000003a1d5ceaa2e0f0b85ca878e1c3870e1c98b162c58001c0e0007001600b00026aaaaaaaa080000000000026743a875573aa8800aa80071741c3d0b85c2e1702c00954015550e1c3870e1c98b162c5871ea1c3a8b45aa1c0f0703c2c58b16a1c3870e1d516e70e875543a1d0e2c3c1c387858b162c58b162d162d162c58b4387498b164c387000a555555555550002600000002a2a82802a800b85c4e27273f49cfd2a802a93162c986c016042aaa80880004cce000002aa2dceaa0220aa008752693549aa000a0802aaa80002a2e171389c041f055005555a53ea5c58b26aaaa4413338508c6ea17402aaad4aa8b73aaaaa82aaaaa1d49aa5d55555980115995595eaaad5552ac155552aaad2ca0001c397162c9d2aaaaaaaaaa80000000002a0002aaaa800b85c5cb9f3f45cbc5e89c5e550055 24 16777215 10 1023
def hc_64_14 : Nat → Nat := unpackHintV5 0xcdfcd6c52e34bee991b39ed3ad359aa17eee9b9d7892d2338aa20c848d857db1b77462546ee55f66c2096271145eacf157d1b752e13c4ecd054771d7408db93bf127357d9d2f35922a99272615211efdc61ac50e14958c0dcdb208d13f000234 0xaaaa44440a2674daa2d526aa80caaaaaaa0aaaad5552ac12b32aa8b16a2c59b43870e5cd8b164cdb31ea5c7a9b45a4d2eab0bc5c571b162cd932e5c9aae3a1c3a870ea1d0e870e870eaa8743accf8b8b9f170b162c593165c5a2d9aac5b316870e8b16aaa1c3aaa931693555555555e33978ce362c59b264c99355555555555555467c5c8cf8b858b162c98b262d5518b462d555262c5930e1c3930e4c3871e6c58b162c78f0e1c3870e1c78f0e1c7870e1c3aaaaaaaaae747aa3d362c59b0e078381e264c9931e0f8783e55573a1d50eaaaaaaaaaa8b162c5870e1e0e7c3c4c593163c78b879f172aa3168c5aa97459355162d438755555555555362c59b265cb939e4fa793e55555555555555162c58b262cb8b467c5c8cf8b9547a8c5a316aaa8f1e2c58b163cd870e1c3870e3c3871e3c3870e1cb8b164c3870e4c3970e1d555555547a8f55739b162cd8703c1c0f0f07c3c1f132e5c9aaab9d0ea8750e875555555555162c58b0e1c3c1cf87879f170f1e2e262cb8b551ea3168c5aa8280070f41c387898b164d58f5563d4da2d26934000000000000387010e8743aaa00acfd2b3f42e171389cccd0060eaa4c58b261c387261c9870e1b005801c0e00070008368b438750e3d49a4d0107800000004cce0000022dce1c3a870e1c3a1d010382a800b85c1c3d073f44e270107c199a00c1d54b8b164c3870e4c3970e1cda2d0e1d438f52697488282826670a218dd42ea0f07aa83cbea805a87ad48b73870ea1c3870e87556803b4b075aaaaaaaa6982aaaa692e2c59300050e1e83c1c39b45a4d2eb71eadc7a80000000000a1d43a1d0e1c001540e002e17138bcccfd333f4ccd0060eaa6c58b361c3873e1cf870e5c58b261c387261cb870f45c99b45a1c3a871ea7d3e934ba0000000000008b73870ea1c3870e8743a1d55005401601b0003800070397162c9870e1c9872e1c3846d16870ea1c7a83c0049a5d000000000026670045b9c38750e1c38070e000a1d0eaa81c005c2e0e1e839fa03e0010b2717999a00c1da5a90e1c03870e13162c9b31eacc7a9b45a4d268505111110d32870e1d645870e8743aab0355555554d304d2a93162c9870e1c987261c39b45a1c3a871ea4d269105050504cce431ba85d41e0f5507aa805a87ad48b73870ea1c3870e875560699683875aaaaaaaa6982aaaa69a5559e5e7939e5e793362c59b450555550505222211555555555541aaaaaaaa55825552e2c59b0e1c3872f0c3972e1c3870e4cb87a551152211a5ce1d0eaad5552a6c58b361c387261d5870eaaaaaaaa44141444267058dd42ea0f07aa83d5513aa80555ce87543aaaaa82aaac875aaaaaaaa5582aaaa55362c59b555500055e4db976e5d79355550000000000155555500000170b91c8e55467e919fa005550e4cb87555362c5970e1c3872e5c3975e1c387055000005ce1d0eaa878fc5e3f2a6c58b361c387261e3870e00b00d8001c000381c0009aaaaaaaa8200000000000099d5ce87543aaa2002aa002e17070f41cfd2391c1f00255005554d8b166c3870e4c3870e6d16870ea1c7aa9b162cd8703c1c0f2a2dce1c3a870e1c3a1d550e87458b162c3870f073e1e162d168b16870e8b162c580070e14aaaaaaaaaaa0004c0000000455505005500170b85c2e162e858ba550055162c58b05802c0855550110000999c0000045b9d5554044154010ea4d526a000a0802aaa80002a2e170b85c040b05500555645a8b162c5aaaa9104cce14230ba85d00aaab522dceaaaaaaa0aaaaa87526a97555556600456655657aaab5554ab055554aaacca01c3800b162c5d2aaaaaaaaaa800000000022c5400155554005c2e162e858ba170b954015458b162c58b162e858b5555550000000045b9d55555554010ea7d53ea9354baaaaa80002a00b05802c362c58b1612a8800aa80000013338022dceaa2002aaaa200874100000549aa5d555541800015170b80580042c5c2e5500555645a8b162c5aaaa911413446a8387a05545555a00545aaaaaaa0aaaccb5554ab055554aa2c58b16aaaa4414133388c2ea17402aaad48b73aaaaaaa0aaab21d50ea4d526aaaaac00accaacaaab5554ab055554aaacca2c58b0e1c38b162c58b162c5aaaaaaaaaa2c58b16ac2f1715c4cb9726aaaaaaaaaaaaaaa2c58b162c58b858b170b162c5aa8b162c5aa8b162c5aaaa8b162c5aaa2dceaaaaaaaa87526aaaaaab222aa2c58b162c58b16aa2c58b16aaac8b5162d45a2c58b162c58b161c387168b4b8f5663d49a5d162c58b2e2b9585e265cb9355c743a1d0e1d438750e1d0e1d550e87458b162c58b170b162e162c58b458b458b162d0e1d 24 16777215 10 1023
def hc_64_15 : Nat → Nat := unpackHintV5 0xaa18a6a61501a1253c99220194313c8c2e01872d407ece1879cd4071960e6c594f68bce762cd7c59ee3853c18b4ae23844dd8140611f3c3d093545be3121092a45b72658fb1eb9e81a052d1355ac1008d30c80e20c1c19089ce0041123000104 0x5ebd5554f9f3e7cf9f3e7d540000000155555554017af55550d802c0260008000026700015555540440011c8e47239540203e000aa4c9d5542c593aa162e87a2d1e2828f47a440a1244426d16ab0eaac3a9355aab0355555554d304d24c993162c9e7162c993162c58f45a3c7a8f1ea3d1e91050511099c163750ba8bc6eaa375544ea2f402a6d169b0ea6c3a9355aab034b075aaaaaaaa6982aaaa69170b17542c5d13275542d168f47a2c5052222050921168b49a4d7e1d5f8755581aaaaaaaa698269162c9e7162c58b162c58b262c5a2d1e8f458b5163d4888828284ce0b0ba85d44ea2750b85d542eaa015168b49a4d161d458755581a583ad555555534c15555348b175546cbd550b170b051628b45a3d1e848291110c2ab0eaac3a8b45a4d56aac0d555555534c1348b162c58b362c58b162c593ce2c58f1ea2c5a2d45a2d1e8f4282888884ce0b0baaa170baa85d42ea27517a015161d45875168b49aad5581a583ad555555534c155553493162e365eaa858baaa1e8b47a3d1e282911102848409b45a4d26b70eadc3aaac0d555555534c13493262c58b164f393364c58b163d168f47a3c7a8f1ea4444154130a13382c6ea17513a89d44e275513aa8054da2d269349875261d55606960eb55555554d3055554d25cdc3165c5c3365c9972750f47a3c5051e3d1e3d22050928a2152e1d4b875269755606aaaaaaa9a609a47a3d1e8f488884ce0b1ba85d44eaa015555581a583ad55534c155553482c98b264c7a2d1e8f40009930162c01687ca00000000006d169355aaadc3ab70ea002e171391cc3d467e919fa0064693264c58b279c58b264c58b1600b00d8006c000b86c02e0131e8b478f51e3d47a3d08000000000001339b45a6c3a9b0ea4d5681c00554005c2e366e8d9fa272383e004c3d006468b162c164c5a2d1e8f4058b000365c01685ca000000099c00005a2d26ab555b8756e1d4005c2e170b985a2c5d0b17400c2d162c58b166c58b162c58b279c00160b0005800b005805c0262c7a8b16a2d168f47a1000000000000267161d45875168b49aad03800aa800b1742c5d0b85c2e1702c00985a00c2d2e4cb931e8f478f478f579b2e2d78b2e6c05a1f2800000000002934baaa5c3a970ea008e47138bcc3d2e7e919fa00646af5e00b00d800131e8f47a3d080000000133aaf503800aa802391c8e4707c00987a00c8d264d555162c58b26aa2c5aaaa82a2a9105051108aaaaaaaaaaa0d55555552ac12a93264c58b279c58b264c58b16aaaaaaaa441414440a2674da6d5168b54ba6d5536aaa4d52ea032aaaaaaaaaa82aaab55555554ab04accaaa2c9a2c58b55162d49935555555505422220a0a11555555555541aaaaaaaa558255162c9e7162c58b162c58b262d5555555488882828144ce8b545aa4d26a9355168b5545aaa032aaaaaaaaaa82aaab55555554ab04accaaa2c5aaa9b2eaaa2c5a2d514155542828888845555555555506aaaaaaa956095458b162c59b162c58b162c9e745a3d55555554161415444440a26745aaa8b45aaa2d36a8b45aa4d26a97540655555555555055556aaaaaaa95609599554993162c58b279d365d55458b5555555505422220a0a05133aaaaaaaaaaa8355555554ab04aa4c98b162c593ce4cd93162c5aaaaaaaa9111050502899d36a8b549aa4d526935549aaa032aaaaaaaaaa82aaab55555554ab04accaaa2cb97162c58b2e8b162d458b2e2cd935555155548a8895556aaa8b972e2c5972e5c58b2e5d4b97162c58b162d554555522a225555aaaa45aaad0b168b162c58b162c5aaa2aaa911114508aaaaaaaaa0d555552ac12a8b162c58b555458b162d162cbe745aaae7554505d15672222115555555541aaaaaa5582552e6c597166cb932e4d5555054555220a0a28a11555555555541aaaaaaaa558255 24 16777215 10 1023
def hc_64_16 : Nat → Nat := unpackHintV5 0x9f9e11975a119360fe8f6cfd89e9618660e282c8e67d7954752a147140fa6af99265e1465d2a2e58b11e543d1d4e118b4be08c45719c40f1203a859b3708df324d2f2eecd82aa5122619231e89e419ed271229f10d413a0b108c058962000162 0x264c99b162cd972e5e162e858b279c58b264c58b1744c99b162cd971e5d2e3cba7cf9f3e4c993260000000000005c58b2e5c3974b872e972e5cb93264c9972e5cb800b162c59fa162c5c2c58b162c593162c58b162c9e7a162c58f168b162d162c58b3e7cf9f264c993000000000000161c5a2c38b458b162cb972e5c993264cb972e5c00f9f3e7c993a3e4d1a3468cf9f3e7c9a3464c00000000f9f3e7c993468d1a300162c58b5549b9d5516a8b547aa80000000002aaaaaaaaa8055552acab32802a8b162c58b162c58b162c5aa2d168f1e3c78f549b9c00000000005a2d1e1d47875269355402aaaaaaa9aa401a458b162c58b162c993000000162c58b269d3934e9d3a700aaaaaa00aa005806c993081e0024c980000013338001c00499300280f80044ea80296aa498b164c78f01e3c7922c58b69458b51e8f48828288884da2d6e1d5b875269355606aaaaaaa9a609a55262c5931e3c7931e4c78f45b9c58b5162c58f47a44141414133390c6e3750b85d43e1f550faa805a87ad46d168f0ea3c3a9349aab034cb41d6aaaaaaa9a60aaaa9a458b162d55556a858ba055455552221110a05555555555541aaaa55aaaa8255162c58b45b9d555516a4d526aa910504cce220c0b0ba85d00aaab0f5555a5956a555555555541555656aaa95559960aaaa9556a6858b160b1602c58b163c7ad28b647a3d0a0a2222217e1d5f875168b49a4d5581aaaaaaaa69826954593162c58b164c58b162c58b1e2c5aa2dce3d1e82c282a8882826672185d550b85d542e3750b85d00b350f87ad42c3a8b0ea2d169349aab034cb41d6aaaaaaa9a60aaaa9a498b164d5516e755478faaa05545555220a0999d110a05555555555541aaaa55aaaa8255262c59355551f513264c9aa910504cce22451ba85d00aaab1fa8fd54aaaaaaaa82aaaca93162c9aaa2dceaa8f526a93554882826671106058dd42e805555555a5956a555555555541555656aaa9555696582aaaa55264c993555522221155545541aaaa5582555498b164c78f1e4c7931e3d16e7162d458b163d1e91050514138843870e1c3870e1c3870e1c438743870e8782aaaaaaaa6982aa162c58b45b9d555516a4d526aa91141344418143870e1c555550e87581aaaa55566582aa54593162c58b164c58b162c58b1e2c5aa2dce3d1e82c282a888a09c421c3870e1c3870e1c3870e21c3a1c3b0555555554d305544c58b26aaaa3ea264c993552228268891070e1c38aa87543870e1e0498b164d5516e75547a93549aaa44504d1106050e1c3871550eaaa1d0eb035554aaab4b2c15513264c993264c99114138883870e1c0e1c3870e1c3c1555555415513264c993264c9910504cce451ba85d01350f9a8993264e0aa9a0f3555555055555544c980002c59300162c15555555400000000015555555554005c2e467e919fa27239540154993262c593ce2c593262c58b555555550d802c02e1b000d8001300b80800000000267000155555555540440005c2e366e8d9fa2723954021607c0015458b000365c00058b05aaaaaaaa800000000002aaaaaaaaa800b1742c5d0b85c2e172a802a8b162c58b362c58b162c593ceaaaaaaaa0b000160b0005802c026017010000016400002670001555555555404400058ba162e85c2e170b954021602c00154b9b5e2cb8b5e6cb932e4c0555555555000000000005555555555004723919fa2e7e89c5e550055162c58b555500000055555500aaaa550055264c98b164f38b164c98b162d55555554d8b166cd9b367cd9f366c99f3e4d540000000000015555555555540058b162c59b162c58b162c9e755555555167c58b162c59f162c58b267cf935500000000000055555555555500 24 16777215 10 1023
def hc_64_17 : Nat → Nat := unpackHintV5 0xd27578c97640c5dce6c14127bcbd21b605aeb1c111a7c67f9e027195ee058fc58a87b20583451b7ce598766d9e6e16166a7ce65f8abd53eee74dfd7c44925b3ff52738e1c532719c29564724713920051b1d5caa189d3010f1eb09c1cc000270 0xa002c58b162c58b858ba1688f1e0003d1e80000000000b45aac3aab0ea4d26aa800b85c2c5d0b1742e1730b40185aa8b262c58b162c98b162c582c000582c001600b02058b1e2c5aa2dce3d1e8083c000001640013338000002c3a8b0ea2d169349a020705500162e858ba170b85c2e0205830b40185a3c58b261b00158a8aa080000000002aaa8022a800b85c8e2f002a802a8f1e0004c58b26b4aaa80a00aa00000004c000555555555500170b919fa467e89c4e550055262c5930d802c08545501101f0b364c9932601f0f82a8004cce00000002aaa80882aaa8013162c986c016042aa2dceaa02208f52693549aa000a0802a0013338000000000aaaa0220aaaaaa002e171389c041f05555a53ea00aa4c993261b0058104c99326020f0000999c00000264c993010380051389c041f0a00a264c98b164f38b164c98b162cd8b166cb8f2e971e5d264c993220aa0b8504cce14451b8dd42e17401550b0aa026a1f3517162cb970e5d2e1cba4c997264c9972e5cbd017aa60f35555555555055555542c58b162c98b162c58b164f38b1e2d162c5a2c58b164c993260b0a0aa220999c288a1615401550b8dd42e17404d43e6a161c5a2c38b458b162c993264cb972e5e80bd53079aaaaaaaaaa82aaaaaa54d8b164c78f1e4c7971e3d16e7162d458b163d1e91050504cce14431ba85d43e1f550f97d500b50f5a8da2d1e1d4787526b755681a583ad555555534c15555348b162c5a2dceaaaa8b526a975548826670a11060585d42e805555555a597aad4aaaaaaaaaaa0aaaab5554aaaccb055554aaa8b2e2c58b162c98b162c58b163c58b545b9c7a3d0a0a220999c2886172faa85c2eaa1750ba016a1eb50b0ea2c3a8b45a4d76aad034b075aaaaaaaa6982aaaa69362c59355551f5133e7c9aa9104cce1422451ba85d00aaab1fa8fd54aaaaaaaaa0aaaaa6c58b26aa8b73aaa3d49aa5d55220999c28441684163750ba015555556965eab52aaaaaaaaaa82aaaad5552aaad2cb055554aa4c99326aa9373aaa6d516a8f55220999c28441684163750ba0155561ea00b4a0ab52aaaaaaaaaa82aaaad5552acab32c155552a8f1e3c58f163cd93264c9aa3d1e8f1e3c78f549b9c881e1415413338510c6ea175215400aa02cd43e1eb5174ba3c3a8f0ea4d26aad0176960eb55555554d53055554d24c99326441333851146ea17404d43e6a264e82a983cd555554155555513264c0160b00d86c0016400442c593ce2c593262c58b08d8b166cb8f2e971e5d0780093264c980005c80000000999c00b8b165cb872e970e5d0380093264c9972e5cb85c005c2e2e5e8b9fa03e0010b27139dcee002f17858b160044000b200582c0161b162c98b162c58b164f3842c78b458b168b162c583c004993264cb9300000590000001309800b0e2d161c5a2c58b1607001264c9932e4cb972e5c2e002c5d0b1742e1700b000858b170b170b85c002e171b162c980028f1f43e1e3c516a3d1e8b1600000000000006d16935badc3ab70eaaa002e171391c8cfd233f4c3d00646aa00b00d8003c000783cd8b164c78f1e4c7971e3c245b9c58b5162c580f1e000a3d1e80000000001333801b45a3c3a8f0ea0700126b75546e002e170f1f43cfd01f460010b2723987a00c8d162c58b0162c016955162aaa000a0000000000aaaaaaaaaa002e170b85c2c5d0b174aa00aa00b05802c362c58b16122dceaa2002aa8b4100000549aa5d55000000266700000055100155555555100170b805a3000858b85caaac8b50055162c58b0500162e85c2c58b16a22dce3d1e8f1e000000013000000168b49add6e1d5b875550005c2e170b858ba162e985a00c2d5400160b0005800b0058b2e2c58b162c98b162c5842c58f162d516e7078008f47a00000000004cce002c3a8b0ea2d1681c0049add5500058ba162e85c2e0168c002162e1730b40185a6c58b260003c7ad2aaa2a800280000000002aaaaaaaaa8800b85c4e47236e7cfd233f37a5500551e2c597000361b000455154000738000017338000aaaa200aa2002e17178bc000aa00aa6c58b26a8aa6e166c9c7c9aa800000002aaaaaaa80002c0366c58b2612a0800aa8f859b03e7c000f933e7c9aa800000133380002a8800aaaaaa880002c1601b0d9b162c984aa8b73823c0015551e8200000a9349aa5d554000000999c00048001544005555555544005c2e03e8c002164e472aaad29f50055005806c993264c2550478002a4dceaa9b545a83000002a3d54000000999c00048001544005555555544011c8e03e8c00227139569aac9f500551e3c78b1e2c79b005806c00880044993264cb935421e8f478f1e03c780028f1ea937380000003c80000999c00ba5d1e1d47875038009349aaa17004723879fa1e3e80fa300089c4e51c3c7a00c5d 24 16777215 10 1023
def hc_64_18 : Nat → Nat := unpackHintV5 0xae854fa6161ca22cfa9dad2097798d90c5ad8ca90784e9f08029307991a679481278cc1f72659a6962416421505ed15456b60752bcfe4c7d9047554a3e524139d91e3535292f21852a393a2479701db5b119990713b9780aee3306751e00019d 0x162c0582c58b162c5ad4d0b45a3c7ad28f641714141444422d16ab0eaac3a9355aab0355555554d304d22c58b162c58b162c58f362c58b16a8b45a3c78f1e3d526e70599c2828288884087d550f87d544ea2f4b50f5a85a2d1e1d4787526ab55606960eb55555554d53055554d22c58b16aaaaa80a3c7d552aaa82111088502aaaaaaaaaaa0d5552ad555412a8b162c5aaaa93458b162c7d4aa0b33851108910113a89d2aaac7ea3f552aaaaaaaa0aaaa8b162c5aaaaa4dce8b545aa3d5416670a221105a1050227513a5555555a5956a5555555555415555aaaa5555a5960aaaa95458b1600b162c58b162c5d42c58b16ec7974b8f76932e5c9910505145110b162c5970e5d2e1cba4cb9726dcbb72f05555555555505542c58b162c58b160b338511110113aaa6a1f350b162c5c154c1e6aaaaaa0aaaaaa858ba170b162c58b162c5802c58b165c7af578f2e932e5c9800000000000b162c5970e5d2e1cba4cb9726bdd97b65c005c2e162e858ba170b85c2e00170b9695458b162c78f000550005498a80000000002aaaaaaaaa800b85c2c5d0b1742e172a8b4015420b8004c58b162c40055526e7550400001516a8b547aa80000b33800000000800aaaaaaaaaa8002c0085c2e170b9545aac8b5005573a1d11e670e8b162c58b1742e162c14005a2d1e3d1263c78000000b33800000000b45a4d568750eaaa002e170b85c2c5d0b1748b858b40185a100f1e000003c58b162c58b162c2e0013162c58b541e0022d168f1e3c78f549b9c0000599c000000000e0022d168f0ea3c3a9355aaa000b002170b858ba162e85c2e45c2c5a00c2d0800098b162c583c00458b162d7af000016670000038008b162c5af5e000b002170b85c2e170b8005c2e262c5930162c58b1e2d548f45b24c78f69478f522220a0a21368b49a4d761d5d8755581aaaaaaaa698269262c5931e6c58b162c78f547a2d49b9c78f51e3c78502cce44141442044e27513aa1f0faa87d54b50f5a8da2d2693478751e1d55606960eb55555554d3055554d26c58b26aaaaa0aa9543c7d2aaa9091088502aaaaaaaaaaa0d5552acd555412a9b162c9aaa4dceaa9b545aa3d54281667221106050227517a555587aaaad2cab52aaaaaaaaaa0aaaad5552acab32c155552a8f058b162c0d8b164d6a687a2d1e3d6947b244141444426d16ab0eaac3a9355aab0355555554d5304d23c78b163c58b163cd8f366c58b26a8f45a3c78f1e3d526e70a0599c1e141544442043eaa87c3eaa2713a8bd4b350f87ad46d168f0ea3c3a9355aab034b075aaaaaaaa6a982aaaa69262c593555549b9d05541e3eaa95554281667488442815555555555506aaa956aaaa095498b164d55549a6c58b363ea550a0599c88443f14044ea274aaab1fa8fd54aaaaaaaa82aaaa4c58b26aaaa9373a6d516a8f550a0599c88441814089d44e955555569655a95555555555055556aaa9555696582aaaa55058b263cd8b163c78f763c7a2d947a8f1e3c8888a2884da2d2e974787478755606aaaaaa9a609a478f163c58f363f382c5975aa647a2d1e3c78f1eb25dce440fa2a88884ba2d1e1d1e1d2e9755606aaaaaa9aa609a4058b162cd85cd8b164cdd46c58b36ec7974b8f76932e5c9910505145111b162cb970e5d2e1cba4cb9726ecbdb2f055555555555505546c58b366c58b36140b3391110113aaa6a1f351b162cdc154c1e6aaaaaa0aaaaaa8140078fa1e3c7c4c58b26002c5808b47a3d0000000000561d55875368b49a4d5500467e919fa170b89c4e61e8032355262c5931e3c7931e4c78f0d802c01e0f0007800422dce2c5a8b162c7a3d0107800000004cce000001b45a3c3a8f0ea4d268081c154005c2e1e3e879fa27138083e0c3d00646800b1602c58b16b4aa8a0a00aa0000000000aaaaaaaaaa002e170b1742c5d0b85caa00aa2c58b160b0058108b73aaaa808822d49aa4d4001410054002667000000000155540441555554005c2e170b808160aaac8b50055 24 16777215 10 1023
def hc_64_19 : Nat → Nat := unpackHintV5 0xd2f61aca023dc14e2db9dddcb315b2ae193fa52e3b9dbddc96e5b694b48c9164d48c59438479f87a5689706a7b6c45095e0f8e4f67aa482dce45fc8c4250eb3d454335bde231451e2ac99f24d97c1ba24e16ed2d11d54609e5fc060cf6000183 0xb162c58b362c58b162c593ce2c78b458b168b162c593262c170b05c2c58b164c98b0e2d161c5a2c58b164c98b162e162c5c2c58b162c58b162c58b162c58b162c58b164c98b162c593ce4cd93162c59b162cd93264c9931e4d263c9a6c58b364c993264c271309cbd79b162cd93264c9930e4d261c9abd78b162c593164c593262e267c5c2c58b5e2c58b162d458b368f1e3cb9b162c99b1e2d458b51e8b478f478f5585e2e2b8d8b166c9972e4d1e3d2e1d4b875368b49a5d5556a8cf8b8b9f170b162c593165c5a2c7a8c5a3168b46aa6c58b363c78f263c78f45b9c58b5162c58f47a6c58b363c1f0f07c8f1e9b45a3c3a8f0eaaaaa2c58b163c78b879f1723168c5a2c7a8c5a3168b468b162c58b162c58b162c58b16aaaaaaaaaa8b162c5ab0bc5c57132e5c9aaaaaaaaaaaaaa8b162c58b162e162c5c2c58b16aa2c58b16aa2c58b168b73aaaaa2d49aaaa8b162c5aaa322aaaaaaaaaaaa8b162c58b162c5aaab22d458b162d5458b5168b162c58b162c58b162c5a2d1e3d478f51e3d1e3d162c58b2e2b9585e265cb93478f45a2d2e1d4b87526975555a8b162c58b162e162c5c2c58b162c5a2c5a2c58b168b16aa2c58b162c593162c58b162c78b16a8b738f47a2c170b05c2c58b168f1e8b0ea2c3a8b45aaaaa2c58b858b170b162c58b162c5a2c5a2c58b168b168f1e2c58b166c797362c59336aaaaaaaaaa9b162cdab0bc5c57132e5c9aaaaaaaaaaaaaaa8b162c5a33e2e2e7c5c4c59716aa8c5a316aa2c58b16aaab5554aaaaaaaaab5554ab54aa6c58b36aaaa3c58b367cf9f3eaa6c58b36aa7cf9f3eaaaaaaaaaa6c58b36aa8b73aaa3d49aaaa9b162cdaaa322aaaaaaaaaaaa8b162c5a3168c5aaaaca7d518b462d54993264c79b1e2c78b1e3d51e8f526e71e3d478f1ebd793264c98f07c3c1f23c7aa4d268f0ea3c3aaaabd468d1a3264c9931e3c7c3cf8f91e3d468d1a351a34993262c593ce2c593262c58b555554ba3d526e7554da6d5168b547a3d55168b5547aa9b162cd970bc5c2f13264c9aaa322aaaaaaaaaaaaaaaa8b162c5972e2e2e7c5c4c58b262c5aad35593ea8c5a316aa2c58b162c98b162c58b164f3a2d1eaaaaaa9373aaa2d1eaa8b45aaa2d36a8b45aa3d54582e160b858b162c993264d551915555555555555555458b170b162e162c58b162c58b5516ab22d458b162d549935549b9d5536a8b547aa9326aa8c8aaaaaaaaaaaaa8d193464d55564faa346aa4c9931e3c58b1e2c58b1e6c79b1e3c78f1e2d458b162d5458b279c58b264c58b16a8f45a3c7a5d478f1e3d478f1e3c7aa4dce6c58b365c2f170bc3c1f0f07c4c993268f1e9745a5c3a970ea3c3a8f0ea4d26aa974ba2c58b165cb8b8b9f170f3e2e1e3c5c4c59316a3163c7a8c5a3168b2e8b162c58b1e3d5458b162c58b5162c58b162c58b162c79b162c98b162c58b164c9aa2c58f1ea2c5a2d45a2d1e3c78f1ea93738b05c2c170b162c58f07c3c1f13264c997268f1e8b0ea2c3a8b45a3c3a8f0ea4c9a4cbaaa5d2e8b162e162c5c2c58b162c58b858b170b162c5a2c58b168b162c5a2c5a3c78f163c58f364c9aa3d1e8f1e3c78f549b9c783e1e0f8993478f5478751e1d49aaaaa3468d18f3e3e1e3c7c4d1a326a31e3c7a8d1a346a3468b162c5aaaad5552aaaaaaaaad5552ad52a93264c9aaaa934f9f3e7c793264d557af264c993553e7cf9f5555555555264c993555549b9d36a8b547aaaf5e4c99326aa8c8aaaaaaaaaaaaa8d193264c9aaaaca7d51af46aa2c5d0b166e00b9b162c99b5e3cba5c7af4d8b166c9972e4c00000000000b872e970e5d362c597265cb93765ed97005e7e8b9fa170b89c5e774005ea72d2a800f1e06c58b260a00aa8a0000000000aaaaaaaaaa008cfd233f42e171391caa00aa41b162c9804c2e0aa02209373aaa6d516a000a08023d54166700000000000154044155555554005c2e020f81391caaab27d40154d8b164c7c2c58b1740a003d168f4478f00000000000000368b49aad7e1d5f8755500170b89c8e467e919fa61e80323481e3c58b162c79b0001e03c7801b162c9804c2e0a8f45a020f01e3c78f1ea937382cce000000003c80000da2d010380f0ea3c3a9355aaa002e170107c079fa1e3e89c8e51c3c7a00c8d20d8b166c02601b162cd8083c17af0599c0000000362c59b010382f5e002e170107c17d50050b162c58b162c0162d6aa45a2d91ed28f1ea44441414422d169349adc3ab70eaab0355555554d304d22c58b162c58b162c58b16a8b45a93738f1ea3c78f0599c2888282884089d44ea1f0faa87d54b50f5a85a2d2693478751e1d55606960eb55555554d3055554d22c58b16aaaaa80b543c7d2aaa8911088502aaaaaaaaaaa0d5552ad555412a8b162c5aaa4dceaa8b545aa3d5416670a221106050227517a5555555a5956a5555555555415555aaaa559566582aaaa55 24 16777215 10 1023
def hc_64_20 : Nat → Nat := unpackHintV5 0x1303d200260 0x4c993162c9e7162c993162c59b162cd9b1e6d363cda4c99b162cd9b0dc6c3713266c58b366c39b4d873693262c58b166cd8b8d9f1713162c58b162c58b162c9e7162c58b162c58b262c58b162c993264c58b168b1e2d162c58b264c993160b8582e5ebc58b162c993264c587168b0e2d5ebc58b162c58b162c58b170b162e162c58b162c58b162c58b 21 2097151 10 1023
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_64_20 (Nat.sub p 640)) (hc_64_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_64_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (hc_64_17 (Nat.sub p 544)) (hc_64_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_64_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (hc_64_14 (Nat.sub p 448)) (hc_64_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_64_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_64_11 (Nat.sub p 352)) (hc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_64_9 (Nat.sub p 288)) (hc_64_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (hc_64_6 (Nat.sub p 192)) (hc_64_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (hc_64_4 (Nat.sub p 128)) (hc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_64_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_64_1 (Nat.sub p 32)) (hc_64_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def f_64 : Nat → Nat × Nat := unpackForestF 0xc5f0062d80315c018a73e455005afcf4d58016b73c46d005abce8d5a740713a034005a9802d3e70adf38567005a5cdb1be6d8ce00b479a81c4d40d0016873245599db24c8d2e65ad1323470052fcc4952598bf302449662dcbc9b2598af2da4496c224b314e594ac00a5b94636cacdf2516972994f94ca3ca55c25168e00a5793d2a48917e4d4892245b92d3648915e484892404491229c8ad364568b2225600529c85192396df203548e5b5c7d1f2396cf1d3648e9aa4740d2396c600a4f8beb7c5f59e2f8df17c6b8be33c641122f8c717c5b8be2b80292e198df0cc678aeb4432dbe296d90cb6b89eb8432d9e226d91135488d284440d2196c70cb4b865a3c3ad7e1d6af0c85c869a5c34d1e190a000a4785d324111be154890446b84d3e41119e104890804482231c104a2096bf04b5b825abc140d2096a70412400521c0cd91feadf0237c7fab3bfcd59fe070ffc5f7fe2bbfc0d00147efe2647d2b7bf4951f4ad6fc27c7d2b3bec951f4ac6fa2560051dbe51a1eeadef84707bab3bdd1680146ef626477eb7bd4951dfad6f427c77eb3bcc951dfac6f056b782b1bc5179e08d4f046677d2b0028cdcb8aaee46472da7bb55a1cb68eec46472d27b9692dd4ad0ea05c72d23ba4991cb486e7a6473d2b3968edcc8d0e645a72d1b80257dc92a8e0b5f705adb8a5b1c50d8e0b5770c9a382d4dc12ac0095b69236b7d1f1a469edb24f6edae36c92db648edc24c6ddaa36c90db5ae0d23476ce3e34893db1af8d224b6bab835c171a448ed5d7c6ad3e34890da84f8d42566911db4b1c1a58b4d2237004abb44551916bec8b5b674b633c1519d0d8c8b5766c9a322d4d9849acc245644ab3220619249ec924b64923b2490d910280095363e3230adbd8d8f8c2b6762d2a30a9ad884c8c425461531b0c951854760094f5dab7aed59d812c8bb36f5fc9a2ecdad7caf8be17c5d9b3af44d1766c6bb35b5dc362ecd5c01296af46f57a33ae55a15e6deb8570579b3abcd1d6dad0af26f5ad362bc9ad69ae0af267599362cc9515e4c6af24b58c362bc91d614d8af23b57e302bc8dc0128eae13455db5ab44d1576c6ab93c55c9a00250d556c896d6f54daa25b5ad516f896d6753daa25b58d2d6aca5b6452dab25a9bd4948896a6b519be28cd592d4cea22444b531a84d512d4be96a5b4fdb625a95d3d48896a534b41c25d17d2e8b6974574ba29a5c57d2e2b6971574b8a9a5c53d2e296982504b8a3a5c50d2d0680093f4acb22255bd292a88956b49cbe22559d252a88956348cb2224dbd212688936b47cbe224d9d1d2688936346caa224d7d126b68c16c449aba2c4d1126a689a6f44d33a245580127682d6f416b5a0b59d05ac682a6f41535a0a99d054c682a5f4152da0a95d054a60093740cb21c95bd012a87256b3fcbe1c959cfd2a8725633ecb21c8dbcf92687236b3dcbe1c8d9cf5268723633ccaa1c8d7ce46b67816c391ab9dc4d0e46a672d6b396b19d5178e58d472c66395379cd5c0e54ce72156004999c4990cdade70254336b59bc9f0cdace6e254336b19b4990cd8de6c27c336339ac950cd8be6a26c3362b9a55c0d16ce66b56339b799cd9ccd4ac0092f32cb218d5bcc92f8635673192b18c558012566236829ab798292cc148e6037029ab397b594bd6d05346f2e2be97296cb94ae5c37029a339609bcb56f85826b2c1339649b0b16e8582632bdb014d15cabadc55c6f2ae3394cd68a88de544672992d14c5680124e5216426ab79445509aad65017c26ab393c5509aac64dc6a26e33134558012464a24f2512392853c9428e4a1270042f9241108e8b64804423a2991c158010b64146d22e3e10493c89ae04124721e3e10453c85ae04114720db810449c010ae400441f22d8fc1107c8a63e056004298f5190792de0084f1de2d80212c6d8de3a5681b5378da91c71ad03696f1b4a38dcd806d24e008471a8260d41100108634364176b78ccd505dac62eb56189b20c4d585d4de303541752f8bcdb05d4ae0083f16c2b0020ec598d01d56f15e2c07558c54adc2a5620ea2d074d684eaca2746813a2d09cd683a4de264580e92f8951803a4ae244680e8b788d1603a2be2146010e3c0849fc3a2ae203500e89387ad683d0ac1d06a0edad0741680106e008330dd3205b5bc354a816d630b52b0649902d2de182540b4af85c9b02d2ae0082f0ac2205316c290ac0082b096b784a5bc252ae0082708c2203716c210880dc5306caf03cd681b28c0e03606c2b00208c192c80756f05caa01d58c152c80736f04caa01cd7c112d80735703d3781c5580103e0505602826014110010360256f012b1808dbc046be023570040b804158010260003f 10 11
def ch_64 : Nat → Bool := dagCheckNodeV5 fullMask g_64 ep_64 5 31 bds_64 641 (dagTraceF fullMask rootStock 11 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 fullMask g_64 ep_64 5 31 641 bds_64 (dagTraceF fullMask rootStock 11 f_64) (cur_64 0) (nh_64 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 96 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_3 : treeBlockF 96 128 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_4 : treeBlockF 128 160 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_5 : treeBlockF 160 192 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_6 : treeBlockF 192 224 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_7 : treeBlockF 224 256 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_8 : treeBlockF 256 288 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_9 : treeBlockF 288 320 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_10 : treeBlockF 320 352 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_11 : treeBlockF 352 384 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_12 : treeBlockF 384 416 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_13 : treeBlockF 416 448 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_14 : treeBlockF 448 480 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_15 : treeBlockF 480 512 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_16 : treeBlockF 512 544 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_17 : treeBlockF 544 576 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_18 : treeBlockF 576 608 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_19 : treeBlockF 608 640 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_20 : treeBlockF 640 641 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 96 → ch_64 i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nj_64_3 : ∀ i, 0 ≤ i → i < 128 → ch_64 i = true := block_join nj_64_2 (fun _ h1 h2 => treeBlockF_at nb_64_3 h1 h2)
theorem nj_64_4 : ∀ i, 0 ≤ i → i < 160 → ch_64 i = true := block_join nj_64_3 (fun _ h1 h2 => treeBlockF_at nb_64_4 h1 h2)
theorem nj_64_5 : ∀ i, 0 ≤ i → i < 192 → ch_64 i = true := block_join nj_64_4 (fun _ h1 h2 => treeBlockF_at nb_64_5 h1 h2)
theorem nj_64_6 : ∀ i, 0 ≤ i → i < 224 → ch_64 i = true := block_join nj_64_5 (fun _ h1 h2 => treeBlockF_at nb_64_6 h1 h2)
theorem nj_64_7 : ∀ i, 0 ≤ i → i < 256 → ch_64 i = true := block_join nj_64_6 (fun _ h1 h2 => treeBlockF_at nb_64_7 h1 h2)
theorem nj_64_8 : ∀ i, 0 ≤ i → i < 288 → ch_64 i = true := block_join nj_64_7 (fun _ h1 h2 => treeBlockF_at nb_64_8 h1 h2)
theorem nj_64_9 : ∀ i, 0 ≤ i → i < 320 → ch_64 i = true := block_join nj_64_8 (fun _ h1 h2 => treeBlockF_at nb_64_9 h1 h2)
theorem nj_64_10 : ∀ i, 0 ≤ i → i < 352 → ch_64 i = true := block_join nj_64_9 (fun _ h1 h2 => treeBlockF_at nb_64_10 h1 h2)
theorem nj_64_11 : ∀ i, 0 ≤ i → i < 384 → ch_64 i = true := block_join nj_64_10 (fun _ h1 h2 => treeBlockF_at nb_64_11 h1 h2)
theorem nj_64_12 : ∀ i, 0 ≤ i → i < 416 → ch_64 i = true := block_join nj_64_11 (fun _ h1 h2 => treeBlockF_at nb_64_12 h1 h2)
theorem nj_64_13 : ∀ i, 0 ≤ i → i < 448 → ch_64 i = true := block_join nj_64_12 (fun _ h1 h2 => treeBlockF_at nb_64_13 h1 h2)
theorem nj_64_14 : ∀ i, 0 ≤ i → i < 480 → ch_64 i = true := block_join nj_64_13 (fun _ h1 h2 => treeBlockF_at nb_64_14 h1 h2)
theorem nj_64_15 : ∀ i, 0 ≤ i → i < 512 → ch_64 i = true := block_join nj_64_14 (fun _ h1 h2 => treeBlockF_at nb_64_15 h1 h2)
theorem nj_64_16 : ∀ i, 0 ≤ i → i < 544 → ch_64 i = true := block_join nj_64_15 (fun _ h1 h2 => treeBlockF_at nb_64_16 h1 h2)
theorem nj_64_17 : ∀ i, 0 ≤ i → i < 576 → ch_64 i = true := block_join nj_64_16 (fun _ h1 h2 => treeBlockF_at nb_64_17 h1 h2)
theorem nj_64_18 : ∀ i, 0 ≤ i → i < 608 → ch_64 i = true := block_join nj_64_17 (fun _ h1 h2 => treeBlockF_at nb_64_18 h1 h2)
theorem nj_64_19 : ∀ i, 0 ≤ i → i < 640 → ch_64 i = true := block_join nj_64_18 (fun _ h1 h2 => treeBlockF_at nb_64_19 h1 h2)
theorem nj_64_20 : ∀ i, 0 ≤ i → i < 641 → ch_64 i = true := block_join nj_64_19 (fun _ h1 h2 => treeBlockF_at nb_64_20 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 641 → ch_64 i = true := nj_64_20
theorem lb_64 : LowerBin fullMask rootStock g_64 12 :=
  lowerDagV5 (kn_cons lb_59 (kn_cons lb_50 (kn_cons lb_26 (kn_cons lb_62 (kn_cons lb_63 (kn_cons lb_33 (kn_cons lb_60 (kn_cons lb_58 (kn_cons lb_36 (kn_cons lb_56 (kn_cons lb_61 (kn_cons lb_45 (kn_cons lb_28 (kn_cons lb_41 (kn_cons lb_43 (kn_cons lb_16 (kn_cons lb_13 (kn_cons lb_34 (kn_cons lb_5 (kn_cons lb_55 (kn_cons lb_14 (kn_cons lb_4 (kn_cons lb_54 (kn_cons lb_20 (kn_cons lb_47 (kn_cons lb_15 (kn_cons lb_25 (kn_cons lb_48 (kn_nil))))))))))))))))))))))))))))) rc_64 nc_64 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.and, [7, 16]⟩, ⟨GateOp.or, [13, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4001941632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 4001941632)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 4001941632) = g_64 by decide]
  exact lb_64

end PEqualNP.Outside.L_meta_48709

theorem PEqualNP.Outside.L_meta_48709 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4001941632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4001941632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48709.table2_from_lowerBin (4276676776 * 2 ^ 32 + 4001941632) 13 PEqualNP.Outside.L_meta_48709.root_lb PEqualNP.Outside.L_meta_48709.wg 18 rfl PEqualNP.Outside.L_meta_48709.wfits PEqualNP.Outside.L_meta_48709.weval
