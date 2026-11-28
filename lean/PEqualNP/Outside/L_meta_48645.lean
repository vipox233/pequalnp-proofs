import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48645

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

def m_0 : Nat := 0xf000f0000000000
def s_0 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_0 : Nat := 0x100070000000000
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_1 : Nat := 0xf0f0
def s_1 : List Nat := [0x5050, 0x3030, 0xf0]
def g_1 : Nat := 0x1070
def ep_1 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_3 : Nat := 0x3300330000000000
def s_3 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_3 : Nat := 0x100130000000000
def ep_3 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_4 : Nat := 0x5500550000000000
def s_4 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_4 : Nat := 0x100150000000000
def ep_4 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_6 : Nat := 0x5050505000000000
def s_6 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_6 : Nat := 0x10105000000000
def ep_6 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_7 : Nat := 0xff000000000000
def s_7 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_7 : Nat := 0x17000000000000
def ep_7 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_8 : Nat := 0xf0f00000
def s_8 : List Nat := [0x50500000, 0x30300000, 0xf00000]
def g_8 : Nat := 0x10700000
def ep_8 : Nat := 0x600000000000000000000000000000102000000000000010400000
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

def m_9 : Nat := 0x5500000055000000
def s_9 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_9 : Nat := 0x100000015000000
def ep_9 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_10 : Nat := 0xf0000000f00000
def s_10 : List Nat := [0x50000000500000, 0x30000000300000, 0xf00000]
def g_10 : Nat := 0x10000000700000
def ep_10 : Nat := 0x60000000000000000000000000000000000000000000000000000000100000002000000010000000400000
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

def m_11 : Nat := 0xaa000000aa
def s_11 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_11 : Nat := 0x20000002a
def ep_11 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_12 : Nat := 0xff0000000000
def s_12 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_12 : Nat := 0x170000000000
def ep_12 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_13 : Nat := 0x4444000044440000
def s_13 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_13 : Nat := 0x4000004440000
def ep_13 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_14 : Nat := 0x5050000050500000
def s_14 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_14 : Nat := 0x10000010500000
def ep_14 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_16 : Nat := 0x5555000000000000
def s_16 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_16 : Nat := 0x115000000000000
def ep_16 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_17 : Nat := 0x3333000000000000
def s_17 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_17 : Nat := 0x113000000000000
def ep_17 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_18 : Nat := 0xc000c000c000c00
def s_18 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_18 : Nat := 0x40004000c00
def ep_18 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_19 : Nat := 0xf000f00000f000f
def s_19 : List Nat := [0x500050000050005, 0x300030000030003, 0xf000f, 0xf000000000f]
def g_19 : Nat := 0x10007000007000f
def ep_19 : Nat := 0x600000000080000000000000000000000000000000001000200000200000100040000040000
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8428408027657607607226e26e06e06a26626416406216206016005e15645415405215205015004e1464460270032001 0x106901fd002a92024240a4681d53038a20203405028194901a0a0613006068154d00a0a05120020480d4d0221203c2406840125002098038400606805490121a01c34028200a4c0109001830020482a938532509a4611c84228f8431d07a360dc641a5282ea30593a09a6c0b118061b0082e0103d7c8fee91ddb6379fc67394fe629dc91377b266eb4bdb895b0527442467f0fcda1b9782f2004e2b07c020b8000f 12 4095 5 31 10 1023 19 524287
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9866094650942508ca308c221791e0781e0709c0701b15d09e24090240901c870148050000000000 0xe130c120d9243414d934e244dd3cd5344814b9341414b924c234bd4cb5442814fe4afa46f63af236ed4ee94ae546d142cd3ec93ac536b13208260816a24c9e40653444346244953c913440444814 10 1023 4 15 10 1023 16 65535
def cc_19_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc1d80300600c0170ae05829cb382704a28c51823042270ae01c0342604b85702c1580a855028140880008000 0x36695af46d5276992b448d8e42c49ee14d5125b8129be92ac486086d0426b6a65a502a4692034a7a2584a2ba491c4492125449220494e30861a4c49038292e34a0a64f51030482814989a050525a401014891a48052302911209320478c22a810d34bba75cd2ace8d5b42ab255291a8a7ac9393c9ace4c66a5b29258423410fa085c0c16 11 2047 5 31 10 1023 17 131071
def cc_19_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc1782d1505a0140261482901202213a5740e81b13226404c090101200400800c21803005082404000400000 0x798d23049e344fa947c49228692424f29244093c4610c24e29a0f0538489d53ce89a0e0909029c5241a0a704c06029fa4dd324d9917dc83ea3def1af6535d2929945e6a0f24f77a6bb84edc1f42098582d9e30ca92440932c699f44cc94644924848c120 11 2047 5 31 10 1023 17 131071
def cc_19_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x8408217c37827807807616e46a26a06816806615c55c05a15815615605605604c52162001e11e01e01e01c11c01c000e 0x9e4927e349d5123414994d01414994926e349a53261440a052543c930d25524934925a349413248448e0f2342c908d0152405492392d8d4aa31268b4962924a18f6723abf8daf635ba8d2e54eb7536d94cb152abd46ad516a544a450a8d3ea14f6812e9c4b4b01d9706a44168f0562414678c0e130879361a455d8f61639848d58e318353609452a4f60539804d4d1316e119b836 12 4095 5 31 10 1023 18 262143
def cc_19_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0313c4310972508c9f47c1d2705c06c58360171548f63c0f03c0a5280a0280a0190601442308002 0xab512f93c8b052e13db54eac136ae4d6a934bc4baed2d300766c1a9605a40158a052793495052e234b45126818940527934b30527924b3492d634b4512c814b0492641893052ba34a8532893c9d4b2601892052892d9d4aab126ab496a924a85329d3ca64b294149e4927e34a251238149e4d01414 10 1023 4 15 10 1023 18 262143
def cc_19_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a49a07727607607607417026656416216205e25e05a25245014e14e04a24a0462460460403384361341340077060003 0x27e34a8532d1440a053aa4ae991ba23ee78f70e359c8cb994ee552b9146e050b7d36c34d7792e9c4b4f42d16094c81ddd057644cd38d33034d2d135234cb5133524d7092d520c84d31d24d30927934d10535240d28c34140c64d2d520c78d32124cc0527934ca0527a30c84c31d20cd9032e30c950319349f4b27d2cdbd3b6b4ad8d1b5b42d592b3e46c38fa823dce52b1546c44fa8d3dc44bb0d29bf48af521ba483083d1e0d5842d4a094f01d13056b144c04f23014 12 4095 5 31 10 1023 18 262143
def cc_19_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a08818618418408408407a54f64c14a14814804804424404213c33c01921611411211010e10e00e00a20a0081023001 0x3fa4406a680d4d1f89ebed3a7d26cf94d5f09a46e4d854952291a4122c76448e29d1b536349f4613d8ba78e04ea2a9b44d3587268a44ca1a974292d1a03b05069fe0b3f4157b828a78d1e11829e3863a48ef091df1a3c34466a48ee091eba53d34679c9cf2929e3233b6426f47ca18f5d09d39d396226ca14c5889337d253107a4d0d44416bb02553248e34c180922f93453270c8491c40a3893471c88d44d1c20a27d20 12 4095 5 31 10 1023 19 524287
def cc_19_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe82ecb82b3ac2929525094241889c66c5b06c1b0595605093140ce2380e0344941c8701846014405 0x23e9f4793d8ca5ae34aa2c934512587a4838076120d410167f02af80521922449347e028c8492060a466446a26908062040a45944838310105229224494c53a790b4b20c0c4001464269124f6169d445368826b0f4d1909203414642690c912169a3ec1483a480d0520e9a4264484279064d0240a40c2c80849034d2029a412447e099020f2001a3ec2c 10 1023 4 15 10 1023 19 524287
def cc_19_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xba1b81b61b60b609329018e18c18a18a08248205f25e05a25054e14e04a24a04623e43c13a13a00d70c0063060003000 0x151a23c2305449933d3a37a6cfa4d9ec8adb8f6791ccee3576c633852a6ea4c9d468da83274da6c9aa0c4d3908a2a0f6741ac8d3490a890c4c14c944324453a78d44d0240a4e24e9bc9b2691615213aa3a6746d3651a4ca2cd53e72a75344d962994cd2e8525a3f0b434128e81d9902b2c8d194124af445a488c94d19a924bc2471a60c749258123212495028b4d0257184a540632490c8f2189649b4e86e9b30935e524b6245974832d8f6511ac9d4e8e29b274fa4c9cc8932902631d4c1d295315269289a26115041e9bc351f03a1705646a6445247d02921532209a3e414 12 4095 5 31 10 1023 19 524287
def cc_19_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81f03c16c6d81a8740e61cc1983305c5b05602c05619c928a50481901185e2bc0742e05b0b606c0d8162816 0x2a00c52814ae68958532ae9e2992ca783149052b5a231e3463c69588f6af1d55a36aac6b548d2a09211024a846952d12a29453d24248494c062940a53234a54694dd128aa65113ca5831490528fa21123422469458f6891d50e36a146b418d2c9a6d874ab5e8d69d16cda25964eb249b638fac31ebb52dafa555e4a6ba9456d26aca4b53491489098c2da70554809a8c12d0024 11 2047 5 31 10 1023 19 524287
def cc_19_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xd80d80b52b21b01ae1a64a41a40a408127e17c17c07826e56e04174003a33a03433403401cc1c01631601220c3082004 0xbc69d64d36f7255ea49b9c8d64906e71b5e6359f29b2d515b69edfd39bf26ae04c50e269e8452e87b7d0d6d91a5aa44b146162d114c943352424848a74f2f7a75eb4db968b61d0af3235ca45bc47d618f5ea9eb55357925b774a6ec92ac5213607a550d4d216dd425b1479628f2549a3452494c88d08d168a235134b802972d3ac7a6dce4eb2c9b738fae51cdae32b4c63668c2e2a6b95496c28b6f5067a9eca1357a25acf496dc26964454307a770d4d61694825b64995649286125aa4caaa4942092d11f59e3d7825b604aab89356925aa248670b6a41553426a384b41092c5a256124a2848c7490881258b44aba49440918e9253024b0688cd492a21452c24 12 4095 5 31 10 1023 19 524287
def cc_19_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x1 0x1514c 2 3 1 1 9 511 17 131071
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_19_12 (Nat.sub p 384)) (cc_19_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_19_10 (Nat.sub p 320)) (cc_19_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_19_8 (Nat.sub p 256)) (cc_19_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_19_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_19_5 (Nat.sub p 160)) (cc_19_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_19_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_19_2 (Nat.sub p 64)) (cc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_19_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_19_0 : Nat → Nat := unpackHintV5 0xa00a8009e0a50a8e1a3808c0a08a7c19f007a09c0a7001c006e09b806c09b00681178a5e017805c097005a09680561130a46189a00290002 0x14555111544450055401554011445101145145145 14 16383 6 63
def hc_19_1 : Nat → Nat := unpackHintV5 0xa22a60a8e29f907c09c0c6e09b806e01b806e017905c0940c4e093804e013804e00aa4280870c1c007001a08680180838a0c0800c0000000 0x5551555515555555155555541555414455555155555 14 16383 6 63
def hc_19_2 : Nat → Nat := unpackHintV5 0x9a926028c323008c022828a022027e29e067801d826c2980c600178254293864e01302422908042010024000f823e00e843028a860a8000a 0x15414455555551554445555455511140155401114404515 14 16383 6 63
def hc_19_3 : Nat → Nat := unpackHintV5 0xd233480d00b18ac01b000be0ad0aa832a00a60a70a961a580940a28a84199205a2940a4040f823230c023000c003000c00262870a0c4000c 0x15551554445555455511150014404514555545555555155554555555 14 16383 6 63
def hc_19_4 : Nat → Nat := unpackHintV5 0xde03780d81b582d603580d603580d40b500d403500d403482d00b382ce03380cc0b282c222a988499e8a7029810543128a4028c102430024 0x11515555555555555555411155554555555155554555555005115555 14 16383 6 63
def hc_19_5 : Nat → Nat := unpackHintV5 0x7f21e8a7431b8c626169058115844a61204480120048011463f30dd03418c842e20a88224059816005801600580131830e0c002460238004 0x155555555555555555555555555555455555555555555555555555545555155555 14 16383 5 31
def hc_19_6 : Nat → Nat := unpackHintV5 0x8f0d1c09d59378c6528ca017092d825614a03140028004f049e013812310401880010001f823f007c08f801f0038186040a86120c230412d0144000a 0x4555555555515455555555545555515555555555555555555455455555515455555555555 15 32767 6 63
def hc_19_7 : Nat → Nat := unpackHintV5 0xa0053e0a7c04f809e053a0a64446987a4ce831b86338e6118b2415c22b805700a8194c11d3234185c30a06110c1b1c2a3034805840b0016002030010 0x155555555555555554115555555555555555551555555545515555555555555555555555555515555 15 32767 6 63
def hc_19_8 : Nat → Nat := unpackHintV5 0xd866062c9d5869c84c12508f98706304168cac456027211906d01ec0838308180063020810008004002000840400200100080002 0x555555555555455555555555555555555555555555555555555555454 13 8191 5 31
def hc_19_9 : Nat → Nat := unpackHintV5 0xce1990330475c90b8053eca646498c8b210839f083c867804bec954a2a024f149231240240248008e08fc81c8c3318640861a0a080f141620185000c 0x5555555555555555555154555555555555555555555545555555555154555555545555555551551555455155555555555555555555 15 32767 6 63
def hc_19_10 : Nat → Nat := unpackHintV5 0xca42c98ac1aa049c323108c023008421f086c41518520948052014805201402500140050014004e093024a092804a012024608f882660026 0x1555555555555555555555555555555555515555555555555541155 14 16383 6 63
def hc_19_11 : Nat → Nat := unpackHintV5 0xd521a80aed95a8caf194e429034e8e95212809ed93a8c6f18ca519012f8a5e0488d10041d8a37106428b06130c1a302638403048e070808180820004 0x155555555515455555555555555515555555555555551545551551555555554554551555555555555555555555555555555554555555155 15 32767 6 63
def hc_19_12 : Nat → Nat := unpackHintV5 0xe 0x1555 8 255 4 15
def nh_19 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_19_12 (Nat.sub p 384)) (hc_19_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_19_10 (Nat.sub p 320)) (hc_19_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_19_8 (Nat.sub p 256)) (hc_19_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_19_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_19_5 (Nat.sub p 160)) (hc_19_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_19_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_19_2 (Nat.sub p 64)) (hc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_19_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_19 : Nat → Nat × Nat := unpackForestF 0xbea737d4d6fa1a8063fbae9d75d36eb235d63ebaa5375496ea128063bb747d6e8e6dca6dc014b72836e134031bdb24ca068d6a93281a2d9e3eb3c7b40d1281275024da047d62d12811ed8344a0255404a6809457344a024d5ad128092d523daa475548daa91ad5234a02494fd129e9454234a7a49400aa93a253234a48314a8d2920a50026a3e8940096831ed063aa0c6d418d6831a5002400c673a9367522cea399d46b3a0d4029fcca4e9949b3251a649f4c9369925d32054029dc964d97849259064b1ecb02494c612a05252a04963592a7d254e64a268053791a98f791a42a63de458f27d1e4f5ef223dd4e7ba9af74fa33223dd3d7ba7916511ee9b452447ba6b0f4f61e9b43d3587a68f74d1ee9742e4485a68f74b60d224193c83a69064d1ee0d4024481a69000f2029a400347b82cfe911ee0abe13d7c274f84d9f09abe1347b828014cdd9a53b3467649cec929d9233bb4477c68ee091d9213b02500a5edd929bb233763e6ec7add539baa53754670c88e24d1c20a375426ea6cdd4b9ba0a8052b6169cc2d29b22630b466b848c2d0985253424069848d08c1a20a341406148cc25298d203301463460ca0518ca031d3063a40c64d184a33092e61252c20f40293b013c44c6cbe4f1131aaed2e5da5a898d112a72e23444a9a89531651a2c94459a48b205112a52c12444a8cae8d112a2aa9265524aaa49112a22954c52a78a54b14a0a2254244a7ca2511129ea252e4ec689e4913aa22252d4c4689853132922614444834928d12a922484c49a4892111120b242344482a8a4b51495229264524a8a491120a005234049a80915011ca02354029a80515009ca01350087e6e934f8941f124374826e8f4f2921e2303746a6e534e89e1d134372826e4f4e2921c1303726a6e0f8021b97f4a2fe8c5f938bf2517e4632688644a0cb1a191242fc845f4f4be9a97d292fa4a010bc83a71074a2d2985a50083a315d282ba4841d0883251512429c6041918829e93d4c27a88414c482969313425a404149487201201421c604605086a01112021a6841118821700427164942c918591d0b2361629c2c52858a30d6441aa78364d06a9a0b1421627c2c4e8589b0b63416a982e4905aa20b1320083e02938052509e4c13c8002918489e0913401484028f8051d07f480fe80028d838a60714401464025283292061300128c024e82a9a051200126c0c500221203130078480c1001a10030340108c044c0121a0112003868040c00a08010240106c02078020b8000f 9 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 384 (dagTraceF m_19 s_19 6 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 384 bds_19 (dagTraceF m_19 s_19 6 f_19) (cur_19 0) (nh_19 0) s_19 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_2 : treeBlockF 64 96 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_3 : treeBlockF 96 128 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_4 : treeBlockF 128 160 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_5 : treeBlockF 160 192 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_6 : treeBlockF 192 224 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_7 : treeBlockF 224 256 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_8 : treeBlockF 256 288 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_9 : treeBlockF 288 320 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_10 : treeBlockF 320 352 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_11 : treeBlockF 352 384 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nj_19_2 : ∀ i, 0 ≤ i → i < 96 → ch_19 i = true := block_join nj_19_1 (fun _ h1 h2 => treeBlockF_at nb_19_2 h1 h2)
theorem nj_19_3 : ∀ i, 0 ≤ i → i < 128 → ch_19 i = true := block_join nj_19_2 (fun _ h1 h2 => treeBlockF_at nb_19_3 h1 h2)
theorem nj_19_4 : ∀ i, 0 ≤ i → i < 160 → ch_19 i = true := block_join nj_19_3 (fun _ h1 h2 => treeBlockF_at nb_19_4 h1 h2)
theorem nj_19_5 : ∀ i, 0 ≤ i → i < 192 → ch_19 i = true := block_join nj_19_4 (fun _ h1 h2 => treeBlockF_at nb_19_5 h1 h2)
theorem nj_19_6 : ∀ i, 0 ≤ i → i < 224 → ch_19 i = true := block_join nj_19_5 (fun _ h1 h2 => treeBlockF_at nb_19_6 h1 h2)
theorem nj_19_7 : ∀ i, 0 ≤ i → i < 256 → ch_19 i = true := block_join nj_19_6 (fun _ h1 h2 => treeBlockF_at nb_19_7 h1 h2)
theorem nj_19_8 : ∀ i, 0 ≤ i → i < 288 → ch_19 i = true := block_join nj_19_7 (fun _ h1 h2 => treeBlockF_at nb_19_8 h1 h2)
theorem nj_19_9 : ∀ i, 0 ≤ i → i < 320 → ch_19 i = true := block_join nj_19_8 (fun _ h1 h2 => treeBlockF_at nb_19_9 h1 h2)
theorem nj_19_10 : ∀ i, 0 ≤ i → i < 352 → ch_19 i = true := block_join nj_19_9 (fun _ h1 h2 => treeBlockF_at nb_19_10 h1 h2)
theorem nj_19_11 : ∀ i, 0 ≤ i → i < 384 → ch_19 i = true := block_join nj_19_10 (fun _ h1 h2 => treeBlockF_at nb_19_11 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 384 → ch_19 i = true := nj_19_11
theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xcccc00000000cccc
def s_20 : List Nat := [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc]
def g_20 : Nat := 0x4000000000c4c
def ep_20 : Nat := 0x40000000000400004000000000c0800000000000000000004000000000040
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb1e54b327d13969924c4a6000f 7 127 3 7 10 1023 13 8191
def nh_20 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x33eb2c33933233133000f 3 9
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 7 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 7 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 7 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 7 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xf0f00f0f
def s_21 : List Nat := [0x50500505, 0x30300303, 0xf0f, 0xf0000f]
def g_21 : Nat := 0x10700f0f
def ep_21 : Nat := 0x600000000000000000000000000000102000000000000010400000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xff00ff0000000000
def s_22 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_22 : Nat := 0x100170000000000
def ep_22 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_12, s_12, 4, g_12), (m_4, s_4, 4, g_4), (m_3, s_3, 4, g_3)]
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_22_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_22 : Nat → Nat := fun p => Bool.rec (hc_22_1 (Nat.sub p 32)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) (nh_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_12 (kn_cons lb_4 (kn_cons lb_3 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff000000000000
def s_23 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_23 : Nat := 0x117000000000000
def ep_23 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_16, s_16, 4, g_16), (m_17, s_17, 4, g_17)]
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_23_1 (Nat.sub p 32)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_23_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_23 : Nat → Nat := fun p => Bool.rec (hc_23_1 (Nat.sub p 32)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 43 bds_23 (dagTraceF m_23 s_23 6 f_23) (cur_23 0) (nh_23 0) s_23 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 ch_23 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 43 ch_23 = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 43 → ch_23 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 43 → ch_23 i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_7 (kn_cons lb_16 (kn_cons lb_17 (kn_nil))))) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff00000000
def s_24 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_24 : Nat := 0x175700000000
def ep_24 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xff00ff00000000
def s_25 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_25 : Nat := 0x17005700000000
def ep_25 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcccccccc00000000
def s_26 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_26 : Nat := 0x4044400000000
def ep_26 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xaa00aa00aa00aa
def s_27 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_27 : Nat := 0x200020022002a
def ep_27 : Nat := 0x20002800000000000000080000000000000000000200020000000800020002002200200000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x4848484848484848
def s_28 : List Nat := [0x808080808080808, 0x48004800480048, 0x484800004848, 0x48484848]
def g_28 : Nat := 0x4000400848
def ep_28 : Nat := 0x40080800000040000008080000004000400040000000000000000000000000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc49807005e1bc160ec0580b0160291d20a4148290520a41292504a0941206404808c2f15e03c0704d841d001 0x8a38431a204e0fa68702c391c1dd20d85868242fa4160f0a868474821a00f4f07260102006100992044801e380d180204022700d2004924d8fe64772a3a8b1bbc8d9d466d53f609daf4dd5a66a92f5295a449d1a46783f321d980dca0664c2f24158d09c60462c1f140d8505c0826000f 11 2047 5 31 10 1023 17 131071
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8ba8e88818080808064595851503b3838383823202020202020040000000000 0xfe3c7c98448f9dc7b0d3e8299400f9e864ee3c731c388d1b870d834660c338e1a690c818620a2ed216a78b13451a427d0130789430 8 255 3 7 10 1023 17 131071
def cc_28_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9189885e5851504925121010020000 0x4b8d226892e36891ab44e5726274392e18c28e1fc71123892a6485023899184084983f0c21478f830 8 255 3 7 10 1023 17 131071
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_28_2 (Nat.sub p 64)) (cc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x8f2a3828e0234289221488029fc27d11ec47721b92673998264118845f1968a51491963b58dc83510cc42d3095023107c819303d40170002 0x0 14 16383 5 31
def hc_28_1 : Nat → Nat := unpackHintV5 0xc806402da5682ae355129893c89a2482a3851c08c14221f10e4a7013611a08c084e92038f8474436218189942921020610110004 0x0 13 8191 5 31
def hc_28_2 : Nat → Nat := unpackHintV5 0x2c699a426a9645090438886110220802000800 0x0 10 1023 4 15
def nh_28 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_28_2 (Nat.sub p 64)) (hc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xc7e063b971b018ea329919408c26461000c6ef63e7a9f428f1ea64f43e7d1e3e4c1e8640636771e018cdb470da346c1c360d00a7ec748671c310618828053b029bacd216278b1340299814bc0a5697484ba0250f12860052702919f8e0fc687d383e9a010fcd690723834161a090087604372ba4150f0a86804330217810ac76903b401c9e0e4c0084e0423020f8106c34901a400d1c068c0082e0d380690024900826000f 7 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 78 bds_28 (dagTraceF m_28 s_28 5 f_28) (cur_28 0) (nh_28 0) s_28 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 64 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_2 : treeBlockF 64 78 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 64 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nj_28_2 : ∀ i, 0 ≤ i → i < 78 → ch_28 i = true := block_join nj_28_1 (fun _ h1 h2 => treeBlockF_at nb_28_2 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 78 → ch_28 i = true := nj_28_2
theorem lb_28 : LowerBin m_28 s_28 g_28 6 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x5555555500000000
def s_29 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_29 : Nat := 0x115155500000000
def ep_29 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_16, s_16, 4, g_16), (m_6, s_6, 4, g_6), (m_5, s_5, 4, g_5)]
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_29_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_29 : Nat → Nat := fun p => Bool.rec (hc_29_1 (Nat.sub p 32)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) (nh_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_16 (kn_cons lb_6 (kn_cons lb_5 (kn_nil))))) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x3030303030303030
def s_30 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_30 : Nat := 0x10101010301030
def ep_30 : Nat := 0x1020002000001000000000000010000000200020000000000000000000000000000000000010101010001000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xcccc0000cccc
def s_31 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_31 : Nat := 0x44400000c4c
def ep_31 : Nat := 0x808000000000000000000000040000000400000040000000c0800000000000000000000044400000040
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_31 : Nat → Nat := fun _ => 0
def f_31 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 1 bds_31 (dagTraceF m_31 s_31 3 f_31) (cur_31 0) (nh_31 0) s_31 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 1 ch_31 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 1 → ch_31 i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 4 :=
  lowerDagV5 (kn_nil) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x5555000055550000
def s_32 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_32 : Nat := 0x115000015550000
def ep_32 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_16, s_16, 4, g_16), (m_14, s_14, 4, g_14), (m_13, s_13, 4, g_13)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) (nh_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_16 (kn_cons lb_14 (kn_cons lb_13 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5500550055005500
def s_33 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_33 : Nat := 0x100150015001500
def ep_33 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xff000000ff00
def s_34 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_34 : Nat := 0x170000001f00
def ep_34 : Nat := 0x800000000000000000000000000000000000000060000000e0000001200000010000000140000001000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xff000000ff
def s_35 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_35 : Nat := 0x570000007f
def ep_35 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x105000001070
def ep_36 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xcccc0000cccc0000
def s_37 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_37 : Nat := 0x4000004440000
def ep_37 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xaaaa0000aaaa
def s_38 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_38 : Nat := 0x20200000a2a
def ep_38 : Nat := 0x828000000000000000000000000000000200000020200000a0800000202000000200000000000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x3300330033003300
def s_39 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_39 : Nat := 0x100130011001300
def ep_39 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcc00cc00cc00cc00
def s_40 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_40 : Nat := 0x40004000c00
def ep_40 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf000f000f000f00
def s_41 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_41 : Nat := 0x100070005000f00
def ep_41 : Nat := 0x40008000000060000000a000000000000000000000000000000000001000200000000000100040005000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcc00cc00cc00cc
def s_42 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_42 : Nat := 0x400440044004c
def ep_42 : Nat := 0x40000800000040000000080000000000000000000400000000000800000000000000000004004400440040
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cc_42_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_42_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_42 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_42_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_42_0 p) (Nat.blt p 32)
def hc_42_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_42_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_42_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_42 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_42_2 (Nat.sub p 64)) (hc_42_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_42_0 p) (Nat.blt p 32)
def f_42 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 64 (dagTraceF m_42 s_42 5 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 64 bds_42 (dagTraceF m_42 s_42 5 f_42) (cur_42 0) (nh_42 0) s_42 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 ch_42 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 64 ch_42 = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 64 → ch_42 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 64 → ch_42 i = true := nj_42_1
theorem lb_42 : LowerBin m_42 s_42 g_42 6 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xffff0000
def s_43 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_43 : Nat := 0x15770000
def ep_43 : Nat := 0x620000000000000400000000000000102200000000000015440000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff
def s_44 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_44 : Nat := 0x1f7f
def ep_44 : Nat := 0x600000000000000e0800000000000010200000000000001040
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff00ff00
def s_45 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_45 : Nat := 0x15001f00
def ep_45 : Nat := 0xa0000000000000000000000000004000e0000000000100010000000000015001000
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
def cur_45 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_45 : Nat → Nat := fun _ => 0
def f_45 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 1 (dagTraceF m_45 s_45 3 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 1 bds_45 (dagTraceF m_45 s_45 3 f_45) (cur_45 0) (nh_45 0) s_45 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45 : treeBlockF 0 1 ch_45 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 1 → ch_45 i = true := fun _ h1 h2 => treeBlockF_at nb_45 h1 h2
theorem lb_45 : LowerBin m_45 s_45 g_45 4 :=
  lowerDagV5 (kn_nil) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xcccccccc
def s_46 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_46 : Nat := 0x4440c4c
def ep_46 : Nat := 0x80800000000004000400000000004000c0800000000000000000000000004440040
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_46 : Nat → Nat := fun _ => 0
def f_46 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 1 (dagTraceF m_46 s_46 3 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 1 bds_46 (dagTraceF m_46 s_46 3 f_46) (cur_46 0) (nh_46 0) s_46 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 1 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 1 → ch_46 i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 4 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff000000
def s_47 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_47 : Nat := 0x100000015000000
def ep_47 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xff000000ff0000
def s_48 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_48 : Nat := 0x17000000770000
def ep_48 : Nat := 0x60000000000000000000000000000000000000000600000000000000120000002200000014000000440000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf000f000f000f0
def s_49 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_49 : Nat := 0x10005000700070
def ep_49 : Nat := 0x60002000000040000000000000000000000000000000000000000000100000002000200010005000400040
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf0f00000f0f00000
def s_50 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_50 : Nat := 0x10000010700000
def ep_50 : Nat := 0x1060000000000000000000000010000000600000000000000000000000100000102000000010000010400000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_8, s_8, 4, g_8), (m_14, s_14, 4, g_14), (m_15, s_15, 4, g_15)]
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
  lowerDagV5 (kn_cons lb_10 (kn_cons lb_8 (kn_cons lb_14 (kn_cons lb_15 (kn_nil))))) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x55005500aa00aa
def s_51 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_51 : Nat := 0x1500550022002a
def ep_51 : Nat := 0x40000000080000000000000000000400000000000800100000002200200000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a192430a123434d263a88d9d3a54d883a10d800f 7 127 3 7 10 1023 14 16383
def nh_51 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6ce3469a10e886c00f 3 10
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 10 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 10 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 10 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 10 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x1111111122222222
def s_52 : List Nat := [0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222]
def g_52 : Nat := 0x111111100220222
def ep_52 : Nat := 0x1000000002000010000000220020010000000000020000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_52 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 10 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 10 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 10 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 10 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x2222222222222222
def s_53 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_53 : Nat := 0x2020200220222
def ep_53 : Nat := 0x20002000000200000002000002000000220020000202020000020000000000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_53 : Nat → Nat := fun _ => 0
def f_53 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 1 (dagTraceF m_53 s_53 3 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 1 bds_53 (dagTraceF m_53 s_53 3 f_53) (cur_53 0) (nh_53 0) s_53 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 1 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 1 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 4 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xa0a0a0a0a0a0a0a
def s_54 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_54 : Nat := 0x2020200020a0a
def ep_54 : Nat := 0x8080000020000000a080002000000020000000000000000000000020202000200000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_54 : Nat → Nat := fun _ => 0
def f_54 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 1 (dagTraceF m_54 s_54 3 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 1 bds_54 (dagTraceF m_54 s_54 3 f_54) (cur_54 0) (nh_54 0) s_54 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 1 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 1 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 4 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x5a005a005a005a00
def s_55 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_55 : Nat := 0x120010001a00
def ep_55 : Nat := 0x100008000000120000000a000000000000000000000000000000000000001200100010000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_55 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 3 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 3 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 3 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 3 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xc0c0c0c0c0c0c0c
def s_56 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_56 : Nat := 0x4040404040c0c
def ep_56 : Nat := 0x400080800000400000008080004000000000000000000000000000000000000000000000004040404040000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xff00ff00ff00ff00
def s_57 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_57 : Nat := 0x100170015001f00
def ep_57 : Nat := 0x140008000000160000000a0000000000000000000100060004000e0001001200100010000100140015001000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_41, s_41, 5, g_41), (m_47, s_47, 5, g_47), (m_39, s_39, 5, g_39), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_9, s_9, 4, g_9), (m_40, s_40, 5, g_40), (m_18, s_18, 4, g_18), (m_45, s_45, 4, g_45), (m_55, s_55, 5, g_55), (m_0, s_0, 4, g_0), (m_4, s_4, 4, g_4)]
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c26a95c75c05a15a05815805425405404e34e04e04a24434404214204014004004003e1364360341340321320038001 0x200983e110a91f94a3b2646e488cc20971183b22066420ac78119c34f3769666d1cbda183a3e2b27c3a0506daf0c93e154a22e8e456b009350144b824d48452f0b452134a620904380a06254080281717c29a984a5e072a40a0500da95134fa06973cd1e75a1ce24f9a4972891e4121c723f8d477008ddd519b614f602967451c70a18d13f182761e4dc34998312f042560449c04918001f 12 4095 5 31 11 2047 19 524287
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x902318c1f4569504c9123c8f03c0a5280a02446318060144320c0300c03004810004000000000000 0x7cd02012f7e4ade9277848efb5cbcd42ea5cb8946aa50a48fe823b928de0a3376171c94454051714c52051693c50051b5606a571613c681713014620b19134600d120145b141734a58d1944504e1012828 10 1023 4 15 11 2047 18 262143
def cc_57_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x944a2190884421f4f87533190c859ac144a04924104803c9548440200e47038150140000 0x29b4ea2d2a634690d0a6c50b2132325cae092da3fb48eec237ac8cea36ca6982006ca2d81f86c9a941f05c9b142584c965427c609d14262607a1b2504c8c97220248c94222508654243608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_57_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b0284a0280a0280731c0701485001400 0x3795d8a557d818f4053eb4ef852fc943dc13f184b8411d8043f007fb813ff17bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5944d1583395ccc1732134c60d3534fd2d2f2b47c4d0f093e 10 1023 4 15 11 2047 18 262143
def cc_57_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0700bc6f0b86e0b82e0b82e0a5690a4290916407d5b46c1745c1705c152541323d0f03c0b406801 0x4fa519b8bd368fa65ae4c350972b92c542542e49c5f9248e2651c289fc89278f6bce857da8ada9157382a6e657da4ada8157372a6e4575a0aca7155362a29a90220261693c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_57_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x28308040 0x24e53a3925fe310b4be8434 6 63 3 7 10 1023 18 262143
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_57_5 (Nat.sub p 160)) (cc_57_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_57_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_57_2 (Nat.sub p 64)) (cc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_57_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_57_0 : Nat → Nat := unpackHintV5 0xdb20369a1fb1b98d8046cad49753a182649c53240092e3248d052468011c03a8c80c464002170d8e8d1668e5c2cc3d966000ac03852e1926b1613182092434386861812108f18c3a46a10c630103b00004000000 0xacf1c73cf1c73ea872aaaa2c06db6db803c71cf3c71cfaa87abaaaaa2e93a83aa66aa00000000000200b2cf4c38395d5cb2c383a8b3c0033c34cb2c72c72cba973cf5d30c34cb4b5cb4b2cb8ba0eac30e830c32cb8b970000000000000cf0c33c71cf430da0ea66000c30c30cf3cf3cf0c30c3aa83abaaaa8fa87a83a99aa800000000000030c30c3a0cf57cb2e8b8b8002bad2c7ad0c37d30eb8b0eb0eb5c30c71df690c30c32cb2d2d0000c30c70c30c30c30ea5cf3c3430c3430c30c32e2e0c32c30ea0eacb8b800000000000033cf0cf3cf3cf3d30c34eaaa25ea8f3cf3cb0175d75e0033cf0cf3cf3cf3d30c34eaaaa0eae5eaa3ea1ea2e9799aa80000000000080ac32c34c38b3ebadf1e1e8bae2cb2c34c34cf7d98b2d9a80071e871e8b9394b820f3d74f55d5cb2c72c72cb2d32c32c32cba8b2e2e2cb8b975ab5a540000000000000f3cf3d5556aaa9454f3cf3d75d75c1200f3cf3d553d56aaa96ad553d51d54d50d556400000000000403d7554c30d3552cb56acb8b800173cf5d51d5543553555554b8b8b8b94b555ab0000000000003cf3cf4f3d3cf57578faa97aaa55ab8fa87a93a83a8b95000000000000000000000 21 2097151 9 511
def hc_57_1 : Nat → Nat := unpackHintV5 0xea001c408376095aca069a60d30017e142bc2050838980491e091d832360286c000cc061641a2a81055000a2040ac4c1201c2101842000780608834110001606020060280c00028000000000 0x9db1eb2eadb9e01b9e76c71c71db9e76c71c71cb00788b8b8b8baa1c70c71c70c71d31c71c71c7471c7471c71c71c71cb1c7a87ab2e2e2e2e0700000000000002bae2d30d92bad0e5e2b4c36b1ad6cadb8c7aeb2e5930d0aeb1badbaeb4e82bab8f3cb52d30c34ea99802b8baeb1eb2e6eb6eb6eb8 19 524287 9 511
def hc_57_2 : Nat → Nat := unpackHintV5 0x6f120c31b14442282064f80c9f001330b266004a82473220dd091b40631c4c60830a71a12a242282c450007f0b0fe001bc402a0d8460e076160ec001a83035000640609434030f8030300006 0x1e1c71c71c74d34d31e22e2e2e2e00000000551c71c7551e2552e2e000000001c71c7694c30d31c71c72e2e2d2d00000aeb1eb2e2ba2c1c71c71e1c71c78872e2e2e2e0000000000c7aeb0d3475aeb2b1c34dad70c70eb11eb1eb5b034dac1eb2e236c34dad1d1c34daeb2e0aeb0e2c0dadb13aeb0d35bac34dac71d31eb8b0aeb 19 524287 8 255
def hc_57_3 : Nat → Nat := unpackHintV5 0xc1c5cbfc10be00ebe000be000bd406bc806bbc06a98928651a81c247d4247c4087b8067602c75008744066ec2c4b51c4b4004901244028434064200a414063d0223d0003ac123542c2a458120c200090 0x134d34c343575d0d0cb8b80130d6b4caeb6c34c34d3575750d46db400c04c30d35d576db0d30d34d5d5d430d0dad34c74c74d35430c34c30d35d574cb4e4cb4e000000000130000b4f6bae2eb2c33c3adaeb1d3d2ebacb8abaeb1cb3cf2eb2a3c71cf2c32cf2c32cb3c71cf2d2cf2d2cb87ab1c7a1c71cb8b8b2e2e3c000000000002bad9aeb4c30e5eadadac7aeb2e58ad30ebae2d30d3a071d1c7530c34e87a99800071c71c71c71e1eaeaaaaaa1e93a83aa66aa00000000000000e0c31c71c70c30c31e20e0e2e2e00000000 20 1048575 9 511
def hc_57_4 : Nat → Nat := unpackHintV5 0x79d519b8d7467437991c5a5b04b95c08052e2113b8804ba1a11a0a43f33a8f60363c5098ed022323488be4542983088291c1ca2006506c1910186380618e00060c161830005e0161401c0400800d01802288c02234000044 0xc31c30c30c30c30c70eb0d0c30d0c71c71c30c30c32c3830c3871c71c30c30cf3cf3c00000000000030c71c31c3ac30c31c71d71d71d75d30d70d34d3535d3534cf1c73d30cf0cf3d32cf932cf973d73c0000000000001571c75d54d0d51dad555553c71cf564b55cf5cf554f0000000000001d745ad530c34c13cb8b80071c71c75d1dad471d5d5d51d31c31c31c71c71c71c73cf3cf3d4f1c71e1cb1e0000000000000c30c351551c71c70c30c355000000001c71c7545551c71c73cf3cf55000000001c71c72cb2cb1c71c7555155000000001c71c7544755aaaa55000000001c05d75d71c71c74051553cf3cf1c71c73cf3cf5551d435554c71c71d555476b5552d5561c71c73cf3cf55100000000000013aeb7d53434c31d5eb4c35eb478f2cf1d71d75d471d1dad5d5d55d37c30d74c71c73c71cf5cf3d3d3cf7cb3e2cf8000000000001534c34c34d5554b8b800034c34d5475535550dad5554c30d3564b55500000000000000c30c30d75757436b50c30d70c30c70c35434c30c30c35d570c30e0cb0e0000000000000c30c351550c30c31c71c755000000000c30c350c30c3555552e2e00000aeb0d36b2b4c340c30c3545550c30c3550000000002cb2cb0c30c30c30c3555551000000000c30c35551aaaa55000000008db8db0c30c30c05540516e38db0c30c35554755430c30d435555550dad4b555830c30d54004000000000004c351c70d30c3a04c 22 4194303 9 511
def hc_57_5 : Nat → Nat := unpackHintV5 0x83868599503d8e0115620008a 0xc35df0c34d53430d0c32e2e000d30c31c3ac30c30c30c35c71c3430d0c30c30c30cf1c73c30c3832c3830c30c33cf5cf00000000000000c7031c700c4c01c71c74c30d35d75d71c71c73c30cf3cf3cf3cf3cf0c70eb0c31c70c30c74c71c71c71d74c30d31d1d71d1c71c71c73c30cf1c71e1cb1e3cf3cf00000000700000030c70eb1c70c3471d430d0c33cf2e2e000 20 1048575 9 511
def nh_57 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_57_5 (Nat.sub p 160)) (hc_57_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_57_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_57_2 (Nat.sub p 64)) (hc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_57_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_57 : Nat → Nat × Nat := unpackForestF 0xa349202d3e841a00b4b9f4a202d1c05a180a4f9b47c0292e55ae4ab50952b92a542542e00a47918bf2291e449380a438f6bc028fc051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37768bcec979dda73b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6b288c2d3d85a5b3560662b8cc17185a3b193463068c2d0d849f0094b3b6b876d40ed2e1da515647eac8ed64262b23757048ac8cced2829b6c534c0768fd45b01da3b4a8c0951413628252604b2a094130ed1ba1360424d88c941092e21a50432a084090ed199e12f3c2567cd00f0939e1233b0b80251ce4a20eb4f1d69669580d0ae1a05c1d68e604d0c416180341d68658d28b628163461d27c3c8fc791d93c50270803c8dc94140f2331e0763c0cc78158f84c1f0883c08c740a009431b6bc024fc649f0093b174722114852b00a25c104a622d48452f082410126e1c050049986254078be0ed4c1d2f04014072a4024bc140a0092b036a40249c04918001f 8 11
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 4 15 bds_57 164 (dagTraceF m_57 s_57 8 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 4 15 164 bds_57 (dagTraceF m_57 s_57 8 f_57) (cur_57 0) (nh_57 0) s_57 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 64 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_2 : treeBlockF 64 96 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_3 : treeBlockF 96 128 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_4 : treeBlockF 128 160 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_5 : treeBlockF 160 164 ch_57 = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 64 → ch_57 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nj_57_2 : ∀ i, 0 ≤ i → i < 96 → ch_57 i = true := block_join nj_57_1 (fun _ h1 h2 => treeBlockF_at nb_57_2 h1 h2)
theorem nj_57_3 : ∀ i, 0 ≤ i → i < 128 → ch_57 i = true := block_join nj_57_2 (fun _ h1 h2 => treeBlockF_at nb_57_3 h1 h2)
theorem nj_57_4 : ∀ i, 0 ≤ i → i < 160 → ch_57 i = true := block_join nj_57_3 (fun _ h1 h2 => treeBlockF_at nb_57_4 h1 h2)
theorem nj_57_5 : ∀ i, 0 ≤ i → i < 164 → ch_57 i = true := block_join nj_57_4 (fun _ h1 h2 => treeBlockF_at nb_57_5 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 164 → ch_57 i = true := nj_57_5
theorem lb_57 : LowerBin m_57 s_57 g_57 9 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_41 (kn_cons lb_47 (kn_cons lb_39 (kn_cons lb_33 (kn_cons lb_34 (kn_cons lb_9 (kn_cons lb_40 (kn_cons lb_18 (kn_cons lb_45 (kn_cons lb_55 (kn_cons lb_0 (kn_cons lb_4 (kn_nil)))))))))))))) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xcccccccccccccccc
def s_58 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_58 : Nat := 0x4044404440c4c
def ep_58 : Nat := 0x4400808000004400000080800040040004000400004040004000c0800000000000000000004044404440040
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_37, s_37, 5, g_37), (m_42, s_42, 6, g_42), (m_56, s_56, 5, g_56), (m_13, s_13, 4, g_13), (m_40, s_40, 5, g_40), (m_31, s_31, 4, g_31), (m_18, s_18, 4, g_18), (m_46, s_46, 4, g_46), (m_28, s_28, 6, g_28), (m_20, s_20, 5, g_20)]
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb205806c01600a62d3029814c0a01bc51d82e427203901c80d446a03405a00cc1640b201804c005432a01500a024e0a3100c4001 0xf2501025e0fa520e9520e04e0d8420c94e0c1420b82e2bc5f2ac532a35e29353253522434b2334322a5e21a531ea521d24e1c24b1b24314a42142331194e109420d04e0b0420301007014069240a0340923408934059240803407024061280284c0493c0204c06a3b05a330513b04133039230183e02839020310181409b4b07b43031240104eb3b4fb2b4bafb47ae343aca4eaba4baa243a6242a323ba02339e94f9a94b91147871437d93f7b93b78937769337492f739237084f6c84b63047540434703f4503b3f8373b0333702f360233181f2c81b0a817008130001f 13 8191 6 63 11 2047 20 1048575
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x992158421078de0709b164990605805c5705c1525415054150504c82c4b0284a0244451001304001 0x4a93a02363c139f836851460b517cd41224e3a139cb4e78979da52724f0502012041b94c100818b50665118c50604d15b506b179a45264d797b525cd256b41584f551350e08129504a9413a5e4c949215238138c842444b8d84e30108f150 10 1023 4 15 11 2047 18 262143
def cc_58_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xb06c0ac6b0a865594232885e4691a06098058960581515053122c8014c4104c10040010000000000 0x2f834ba0d9ca42c0d2ef343b853ad84eb409ac2586a9028b50a0d82126068942b248788f992324e4f9003e829829a38629428a489cd0201507e542845188945f250769397a429e8ea6a364c53a61363e13a58365c9424a381a04060205a9423a38160422460 10 1023 4 15 11 2047 18 262143
def cc_58_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x8840a00e470381c0d25328140a049241208232180b2582c1289041200e47015080400400 0x3f2886524309a7c493c068e42473217850bec9fee432c937a13bc879dc26e11a734d38ea5c152eb2f7457f92a7bd25da136b8d35269a134cc9b69d2f3e87964ec8a75a05712698434 9 511 3 7 10 1023 17 131071
def cc_58_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xb05602c0580b01602c05809cb382704e09c13825144346288110220386684c09803006009192024048061806 0x25d220d8249b8a53497a65294c15297265240e64418ca0369302d200529e29d335fa56bd4897a8d295115fa02a73e53e78a19d13d9d277384de589aca85e8f0a4b8068680b4682c8c04d1609218a8c113d86ac10297214ae41b5e824bd0254a26294425e872bf0854e00a6bd04d 11 2047 5 31 11 2047 19 524287
def cc_58_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x98a60982608ce308c21284210841f27c1d2741c1701b16c19264136268902409018c330c03004801 0xc02897e112f6b05e15cbb0b9724d2e01a5aa3bb44676490a4c275802492099584f2442657a3bae4675a4eeac99d51239007d86d2f05a1df24fba48f6e8fe3ca75b04eb30596209aa4121e12d9a24a40058ec9ecc9351f02d3091284a20e014 10 1023 4 15 11 2047 19 524287
def cc_58_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9826090a4090204801e2781e0709c0701c06118060144501404892048102220711c0340c00300000 0x3789a6e834df697b8d0f6c276d03cd24939e907591deaa33d28c1a29b330b664960cf8c19c9b32cb664160cc2579648f251de4233d86b9aed4751a869a50d04779a8cf28ae63950b00298a4d3101a5a82caf049840d2d01657024 10 1023 4 15 11 2047 19 524287
def cc_58_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d8362cb19412825044384300600400746b99702e0544798f01e0344490901012004008010020009c10001 0x7fb527f25e7ea52600523f04286c538635f85b5e8525e84a528415e811527205f5f0534f84f3e8431d03d8083b800377e0353281d118157d0187c8157c0145e8517983d7a45e79a5e5e0527b4527aa5e7814d7185f5d0537904d1c9423e0427814e7793c4f04f3d843108257701575a525c8527625e7105f5b85375025740157323b72a332294d7213f719377112f4a83e70034 11 2047 5 31 11 2047 20 1048575
def cc_58_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x982338c2308c212841f27c1e1781d1741b26c1562e8b02c0b020c5314050140501403200c0000000 0x23c9a468188a0291b8ee3519c1a4e8c285164920b264124c89079158ee2919c0d3e89877110ce2011c7f4b8ee870293a38a72804f4208e720fe320c45c15878283c0b5fc1289c151d87afd0d44c0ac143982063074da0c0ac0c14 10 1023 4 15 10 1023 19 524287
def cc_58_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xac247902318c23084a10841d4741b26c1b064990641905515054114441103c8f03c0d21604110004 0x9fa3b9f2338413e2284d5103f438373a02f9e1349d2349c9349db4b9c3439b94e9b13c9724995a419923b98a339746096a6c9406c9286095c609526c9386c920609412b9392392a3b922339a35c99b519835097a509623b94a339305c918508b01490a34901348d8188a814 10 1023 4 15 11 2047 20 1048575
def cc_58_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a13422c4508a0f61e83c1780f01c9b90720e05c03536a0c8d542a05409cd382432be540a81232403cc07800 0x56a5ea94a5519421aa7d79355389f5d0d4aa0bd634eadc9f5a90e1497bd5275205e8809ca80bd623cab24b55094a40b94017a807a4d0d4980ad393d26a6a4b05aa7a4d4b43a8e83094fe9e93a8c3fa684e4a05e9529485523583b489498a291881aa5cbd3f57e76adcb1578faa749495cc2fb7c5b680aec314e8e129a41f300364805c2609d12529d2b41204685293785a088254597a7cafce15b94aaf1d54e8692b945f6e0b6cd15d8229d04253383e5e06c8c0b83c13 11 2047 4 15 10 1023 19 524287
def cc_58_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x162c3c70a942850a1405 0x15b97ad2a2da0452b82f53942cd1c59250b1ab962542c22e58050 7 127 3 7 10 1023 19 524287
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_58_11 (Nat.sub p 352)) (cc_58_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_58_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_58_8 (Nat.sub p 256)) (cc_58_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_58_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_58_5 (Nat.sub p 160)) (cc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_58_2 (Nat.sub p 64)) (cc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_58_0 : Nat → Nat := unpackHintV5 0xef00bac10e8033960acc993280ac80231808b41220cc483001f4187b819e8067a001d41475001c60e71801b412680519a06610597c08451a1140045000f81c2c12010a0000400000 0x18e342348d00170d78c35c350d2cb05d5742300c8c0000c32cb0005c01000828f003c33c33cbaa2c7004f4f4f64001c1c5c5c5c8554048cb8303cf8d0b08c8e33e38e31f8cfa37ca300000a0003cf3e800000001f2300007df00008b8b055500000400000a000555500000000010000000300b020100aaaa 18 262143 8 255
def hc_58_1 : Nat → Nat := unpackHintV5 0xb80da568a958024e08840fa08087a081e800700a1c0006b051ac006a809a406670218e0e6300984086080982005f019205c458290c0a4082900023c040846c1f020146802828000a 0x71db6e8010007001c08c70f6c30db2e8b000002310000711b1b03cf8b8b3cf3d72e3c33d1713cf3e0c5743e317a38e1b2e8e8b3cf6c1b3cf2cba8b415d7442ea308c08e31053c33e30cf0c030b2c71cf03c58c1c71c71c70c32cb03d5471d5108d635 18 262143 8 255
def hc_58_2 : Nat → Nat := unpackHintV5 0x8a83d1480a10193c8586e0b0afac95b0427e384fc00910e8fd251f8023747c6e800d20b1a0043400065828c6051820a25ca84a018791b0f2001984c199982f0403e200384401060010100002 0x234f8cb000001400c2c5c00000a8b8b03cf3d3d00000003c30cba2c0f4017110000000a0003d3d3d90000000048c00000000300b020000ba30cf0c34f1c5c23033cf6c74f05c200aa0c30a1c0084400a30ba2cb3cb4f17036c70220c2c4b420000c32cb01c70004400b8c32e0cf0d3c5e30e2cb3cb0f0db0cf08b8b003c701c5c40010f0001d0478e30c8c8e8e8c1 19 524287 8 255
def hc_58_3 : Nat → Nat := unpackHintV5 0xf4c08ef82aeec06ea026de45ece480cd806c5840ac0cc9e86c9902c98c0294c209480293c068447c61d1456c583f8ba3f8003f8003b8203ac063701e36c022e0461f07804cd204c0004c0000c2000006 0x23a38c3c44e4f8c34e0c4e5000008b8b3d3d008c3031305c00000b0e2c0130c34cb2cb2c0000000230003d4ba2c0f00000000008393000c34e930000003231300000000002c0220100000b0d30d3022c0002e3d3d0004c03c71cb8d3e3234b58c5c5cf03c30d38b2e443d33cb2e934e2173d304e822e8ba8b002cb2d32c32c32cb00134d34ea8b2cb4b2d004d31313223a0a97170000f0c34e580f4e813000000002a80134d34ea8004c000088c0000004c00c08100008d2e0d638e32d45e341471c750d2d1c704f1c71c0751c7a8b8b5441c75d73c5c51c078701c7a401555551c01554354b565001c01d717172048d4163232e0c23 20 1048575 9 511
def hc_58_4 : Nat → Nat := unpackHintV5 0xe202addc22d9822d9402d9400d9400d8806d7808cc45ac2052c1406bf410bf400bf400bcc14b742c990f28d0607e0786e87c54cce4786a4003c3a82c37818374023302232c0232c003140c2207a00110 0x234f053a3175d3e35c0d3d7038d7178e3c1122e2cf3cf3e8303173c030235c08c300000b5c58e31d400074001400c2c0030005db0204e0e4e932e932c030d75753a4c000c8c30c030c34d32135c5c000000838300555500000000000430d2e8b000c30c33e9300c0000000008383000c30c33e9300030000000000008383000c30c34e9300032300000000000302c080400000300c0004d38b8b0f4f40302300200aa04343030230c70cf8cf638c38e308d436317235c0f414e2e2cf0c30c33d30c33c5c5cf0c3000c300c08134e830e832e0e0c030d0c30d0c30c34e93000c30c3003234c85c5c 20 1048575 9 511
def hc_58_5 : Nat → Nat := unpackHintV5 0x95c4d258624506488028cc451801a2f0143e207f488fd019f70339e5071c20c122982002fc085ec0cba03974002dc0c5ac0c9c990e1581962c2ec404a9307520082680986c12808141100028 0x8e3073c13e38c38e33c238c0313cf238c2c13c00002a2e2cf4f400238c00002801555400000000f2e0000f0c32e8b003c73c73e8700100041c008c8e3073e48c00002800f3cfa000000001c000000280071e8700023000001c000000c02c08040000236c00138c5c5c170c8c5c6c0022e2cf4f40000802a81408230c0c04c000934d32d32d40230c0c2c0f1c73e34f5c8c235758c1740f8d3e317 19 524287 8 255
def hc_58_6 : Nat → Nat := unpackHintV5 0xc480d8880b01105aa58a4d0917b21f53a37a706e80cd9839793a26e844d00c978291d1222a10440147d0b0f7031e806300d05e818b60711458089a01100022000242003c0c02058010300002 0xb238c2e2c0000022e2c71c747400001c00000b2cb2c0071c71c71c71c000000000000280071c71c7a1c08c00000000700000c02c02201007000000020e0c0030c30c7a1c00000000000002a2e2c71c71c7474000001e38c5c0000280071c71c7a1c0000000007000000b2cb2c0071c71c71c71c00000002308c38b8c038e305c230e2e302e3178e300001c71c70008787a000000008e31700000a00555500000000040003000000a0002c00280700040071c71c7a1c0000230000001c8e30b8308e38cb03c 19 524287 8 255
def hc_58_7 : Nat → Nat := unpackHintV5 0xe560072b0037f0b59cd16c86305f7262d09594710a9a24b4a9142540052a0008d63d3d14d1cc0e4cf0b86202c28a43125100924024163e1714d09d8d8328e2168160a6070468641ec240d2120102c8078040001e 0x170418b8b0c0c5d73cfa3cf0c70c7070f6d587938393a4cba3cb1d1d43630c350c30cf4d94c71c30cf0f13a4d3cf40000020e0c0155540000000071c34701c0c30ba2d0471c71c30c30d3a4d55430c30e1c7871e0e0d550d555471c71c30c30d3a4d5430c30c31e1c7871e0e0d550d8d55551d1150d4b5655471c71c30c30d3a4d5554540c30c3141c71d34e2e2c71c343631c1c1d717078301ea9431c3436303005d1138b8b3c3c0c35c30c30d34cf3c30c303030c30c3561e4d3a0c3a0cb83831d1d0c30c3543633d91c70c3030c3030c30d3a4d3cf4701d471e2e2c75630d0d3d3c5c4f0c70c71c71c71c72c38b5555551c71c74c30d32cb2cb551c71c073c0ba2d0471d7550c71c31c7871e1c78393475555436353554744554b5599551c71c70c34e935555141cb0d30d3a1e2e0452e1c7884c755c5c22cb9704c30d3414d3885d34e8b2cf3d31c74eaa2e8ba8b1c1c2cb2d32c32c32cb547474f4d3d4d98e96a1c74d34d3aa2cb2c2cb13cf61d34701d30c34e090471d34e95471c71eaa1ea9554d555598d1d1154d50d595471c71d34d34ea9555148b8d700e3178d702e35c0f3d8e3171c305e38d71702e38c5c00003001b0002000ba00000471e87023000000000700238cb830 21 2097151 9 511
def hc_58_8 : Nat → Nat := unpackHintV5 0xb000d5a85a872e50806a040d2c94251084287a85001080220d034100a8200101031ff033827c59570a68c13b1220a6c354c047a30543b0a20612c18258004b0007e1808c7009088011100002 0x238e32d471c701d471ea2e2d511717238c00002801555400000000b97401005c30cba2c000005c5c5c8404048d8e345e18c701e1c071e900555551c075d75e8054701e1c071e94018d555547554354b5650000084105114236c441d38d3c73c4f0d8c73c76c4471e2e2c71c30315717078701ea9471e83630d0c301c74c701d6934d32d32c71c3630d0c32c701d431c70e33c078c300c51c71cb3c708e3001471c01471c750d2d05633c3d74323433cf3c 19 524287 8 255
def hc_58_9 : Nat → Nat := unpackHintV5 0xd084962beac40156a1eac80d5880aa1104fe44934c8fcaa1c534326646400cc4839573223a744680c8a82903121f6103d814700b0dd031b4062b0b854818a2070e0640418008000100000020 0x8cf1c72e354701c70c71c70c76e1c071e871e872e818c1401d1d1c76400701c7002101c08e32e0c0b238d2e2c0000022e2c1554000000000b2cb2c0155540000000000002818c0155540000c02c0220100000000000000000020e0c00343476400000000000002a2e2c0747474740000238d3c000028000747476400000000000000b2cb2c007474747400000002308c38b8c038e313c230e2e302e34f8e300000000000a00001d1d1d98e34f00000a0001d1d1d90000000000003000000a0002c002807000631d1d1d9000000000000008e34b835 19 524287 8 255
def hc_58_10 : Nat → Nat := unpackHintV5 0xe0e466d51932124d85c56bd22e5c014abe90d47cbc9ae4849d1d200274ef8846fa4131335189800b44845a20029d1a12e1048787c43c001f1168f88007105a2828310b1b0808283406218c0a0951880d1ec00034 0x300c541c1c78b8b1c73d1d8cf1e970f073c0000008b8b3d3d05c08d7085c30c0038c30c30213134e0e4e932e932c701c31c31c76db1d6c753a1c000306db06c132070203aa08c0e80347431c000930c08e80ea8071c747400282a8701ea871c0220070001308b2cb2c0071c71c71c71c00000000004c28c02a80130030200071c71ea8041c00000000000021cba08f0c34c541c1c71cf998cb1d70f073c0b80130c34c0003d3d013808cb05d313134ea8028ea2ea2ea2d32c32c32cb00701d31d31e2eaa1cb2c74b1d004c4c8b0a02cb02c07013130c32c131c30c7001c71c7000000000c008c0c0934e0e2c701c71c74740000004d30c34cba0d38b4c31c31c76c76c72c74c74c0306c6c2c4c1c074e0930c34e8b4d471c74cb1cb476301c4c0130c34c8b4c1404cb0b023130a932d32c701c74c72c71c004c2c0700c30c388a2e2e082e833d3d2e5c5c2e8b3c1a658f0c3a0c35c3c3e2d7028823d3d5c30e830d70c30c3aa8baa3a830c303030eaa0c30c30e2ea830c3430d0c30c38baa0c30c0c30b2d34c8a8b8b8203838f4f5717232c5e2c38f096963cf4e8b2d70f0f4f8cb8b0e5c20a08f4f574d3a2cb5c34c34eaa2ea0ea8cb2c2c2cbaa834c30d3aa2cb2d2cb530c34ea8b2cb0b2c8b8cf0c70e34f 21 2097151 9 511
def hc_58_11 : Nat → Nat := unpackHintV5 0xc2094b50688f92c7f880644da5348844c7438c602a4741b478000da 0x1c070c11471e2e2c71c30c3630d3c75c3c1cf00000022e2cf4f4030230c4c170db0c038c030c08134e832e830e0e0c701c30c3430d0c30c30c74e87000c300c0300c132070000002c38b001c30c71c71c70000000000e300006c000138393002c2800070c31c041c07a1c000000000000000c0020c30c0030c30c71c71c000000000030c30c021e1c0020e0c000000000000020e0c01555400000000000000000020e0c000030c30c7a1c0000020e0c0030c30c7a1c00000000000c00038c28000b000838301c001000c30c31e870000000000000 20 1048575 9 511
def nh_58 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_58_11 (Nat.sub p 352)) (hc_58_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_58_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_58_8 (Nat.sub p 256)) (hc_58_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_58_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_58_5 (Nat.sub p 160)) (hc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_58_2 (Nat.sub p 64)) (hc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_58 : Nat → Nat × Nat := unpackForestF 0xb4145b404500b4fb323800b4bb0250b015cb0150b005cb005000b47ae935ae83500b43ad24fad24300a4eac23c00a4baa925aa82500a43a6b49a6b43a6b41a803da6927a713da682700a42a3a5ea5252a3925a4252a382500a3ba0a5ea2252a0925a1252a082500a339f23b9f2330094f9e1349b34b9ca349c9349b3439b14e9b13c0094b91b5c91b5198a3b98a3391b5091a5096c6096a6c91a3b954609526c91a339392b939239185c9223b922339185000947902349013487b4b8f13487b438794e8d23b8d233878188c142878158b1248823b882338803b8903c880338802387814009437e4537e35f7e35e7e25e7e2527e15e81936818158203982031818147e1527e03b7e0377eb527ea5e7ea527e0350093f7c0187c0157c0140093b794527925e79c5e79a5e7904d009377714e7713c77015009337525e75a52750250092f74015009237123b712337113f711377112f0084f700346d34b6e9346e8346d3436d04e6d03c0084b63b5c63b516aa3b6aa3363b5063a5068c6068a6c63a3b674606726c63a336592b659236395c6423b642336395000847621346203454b4b6103454b435f9445f84454a4f5dd605d95c5d85c54a475c1345c03454a3f5484e5a23b5a2335482c5924254826580245523b552335513b5613c5513355123548240084347c5347b5f47b5e47a5e47a524795f50944479534794f479434793b479374bc524ba5e4ba524b9524b932479354785e4803648016488394883148014478520083f4582c45826458240083b404524025e4015f42d604295c4015340b5e40a5e409524014d008373f1443ba4f3e1243ba433b84e3b83c3c1423b8260083337a5e3795f39934379533835238152379250082f368260082335234351343234b3413432343331363224e3214e0081f30934308342d34b2f8342d3432e8362d14e2d04e2d0260081b2c2580b45f2b2480b4530b35e29a380b35328a4825c5125a3a2734025a3625936258360b35224a380b34b23a380b3430b25e224600b2531f4511f3511fa361f8361f3500b2521da5e1da520b24e1c93c0b24b1b94c0b2431545e15452199441535e18450181341535215349153411513d15b50151350b2420b2331225e1225212a50121520b14e1112e0b1420da5e0da520f2500d9520d84e0d8420b04e0b94e0b9420b82e0b042008170a0340134b082340813408034013430702403a3b0612803a330393b0493c0393303923011240203902031018140104e008130001f 9 11
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 4 15 bds_58 362 (dagTraceF m_58 s_58 8 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 4 15 362 bds_58 (dagTraceF m_58 s_58 8 f_58) (cur_58 0) (nh_58 0) s_58 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 96 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_3 : treeBlockF 96 128 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_4 : treeBlockF 128 160 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_5 : treeBlockF 160 192 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_6 : treeBlockF 192 224 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_7 : treeBlockF 224 256 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_8 : treeBlockF 256 288 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_9 : treeBlockF 288 320 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_10 : treeBlockF 320 352 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_11 : treeBlockF 352 362 ch_58 = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → ch_58 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 96 → ch_58 i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nj_58_3 : ∀ i, 0 ≤ i → i < 128 → ch_58 i = true := block_join nj_58_2 (fun _ h1 h2 => treeBlockF_at nb_58_3 h1 h2)
theorem nj_58_4 : ∀ i, 0 ≤ i → i < 160 → ch_58 i = true := block_join nj_58_3 (fun _ h1 h2 => treeBlockF_at nb_58_4 h1 h2)
theorem nj_58_5 : ∀ i, 0 ≤ i → i < 192 → ch_58 i = true := block_join nj_58_4 (fun _ h1 h2 => treeBlockF_at nb_58_5 h1 h2)
theorem nj_58_6 : ∀ i, 0 ≤ i → i < 224 → ch_58 i = true := block_join nj_58_5 (fun _ h1 h2 => treeBlockF_at nb_58_6 h1 h2)
theorem nj_58_7 : ∀ i, 0 ≤ i → i < 256 → ch_58 i = true := block_join nj_58_6 (fun _ h1 h2 => treeBlockF_at nb_58_7 h1 h2)
theorem nj_58_8 : ∀ i, 0 ≤ i → i < 288 → ch_58 i = true := block_join nj_58_7 (fun _ h1 h2 => treeBlockF_at nb_58_8 h1 h2)
theorem nj_58_9 : ∀ i, 0 ≤ i → i < 320 → ch_58 i = true := block_join nj_58_8 (fun _ h1 h2 => treeBlockF_at nb_58_9 h1 h2)
theorem nj_58_10 : ∀ i, 0 ≤ i → i < 352 → ch_58 i = true := block_join nj_58_9 (fun _ h1 h2 => treeBlockF_at nb_58_10 h1 h2)
theorem nj_58_11 : ∀ i, 0 ≤ i → i < 362 → ch_58 i = true := block_join nj_58_10 (fun _ h1 h2 => treeBlockF_at nb_58_11 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 362 → ch_58 i = true := nj_58_11
theorem lb_58 : LowerBin m_58 s_58 g_58 9 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_37 (kn_cons lb_42 (kn_cons lb_56 (kn_cons lb_13 (kn_cons lb_40 (kn_cons lb_31 (kn_cons lb_18 (kn_cons lb_46 (kn_cons lb_28 (kn_cons lb_20 (kn_nil)))))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xff00ff00ff00ff
def s_59 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_59 : Nat := 0x1700570077007f
def ep_59 : Nat := 0x60002800000040000000080000000000000000000600020000000800120002002200200014005400440040
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 6, g_42), (m_25, s_25, 5, g_25), (m_49, s_49, 5, g_49), (m_48, s_48, 5, g_48), (m_35, s_35, 5, g_35), (m_27, s_27, 5, g_27), (m_51, s_51, 5, g_51), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d3095a5d209935a3958856791d447109c01f 6 63 2 3 10 1023 14 16383
def nh_59 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x14000b9756c2e738cf318c23af650009f3ce719de3182d5abb053bb1b6e1adeb008140e338c72132a8d005d001c671800433cb5009469d 16 65535 7 127
def f_59 : Nat → Nat × Nat := unpackForestF 0x205d191da5d111cb5a2958856109c01f 4 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 9 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 9 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 9 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 9 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_42 (kn_cons lb_25 (kn_cons lb_49 (kn_cons lb_48 (kn_cons lb_35 (kn_cons lb_27 (kn_cons lb_51 (kn_cons lb_10 (kn_cons lb_11 (kn_nil)))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xf0f0f0f0f0f0f0f
def s_60 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_60 : Nat := 0x107070705070f0f
def ep_60 : Nat := 0x40008080000060000000a080006000000020000000000000000000001020202000200000104040405040000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 7, g_19)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 6 f_60) (cur_60 0) (nh_60 0) s_60 6 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 6 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 7 :=
  lowerDagV5 (kn_cons lb_19 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xffffffff
def s_61 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_61 : Nat := 0x15771f7f
def ep_61 : Nat := 0xa0800000000006200600000000004000e0800000000102210200000000015441040
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 5, g_43), (m_1, s_1, 4, g_1), (m_45, s_45, 4, g_45), (m_46, s_46, 4, g_46)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x4080e5c3862c0681 0xcae3d73e9f7478a7a51ca6e01f 7 127 3 7 10 1023 13 8191
def nh_61 : Nat → Nat := unpackHintV5 0x3287ca03005b21ec80a61a8820144000 0xe3ee2fcdaaaad3a550040010000 14 16383 7 127
def f_61 : Nat → Nat × Nat := unpackForestF 0x3a7e570e8e54f7ae151ca6e01f 3 10
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 8 (dagTraceF m_61 s_61 6 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 8 bds_61 (dagTraceF m_61 s_61 6 f_61) (cur_61 0) (nh_61 0) s_61 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 8 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 8 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 7 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_1 (kn_cons lb_45 (kn_cons lb_46 (kn_nil))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xffff0000ffff
def s_62 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_62 : Nat := 0x175700001f7f
def ep_62 : Nat := 0x828000000000000000000000040000000600000060200000e0800001202000010200000145400001040
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_36, s_36, 5, g_36), (m_44, s_44, 5, g_44), (m_24, s_24, 5, g_24), (m_34, s_34, 5, g_34), (m_31, s_31, 4, g_31), (m_1, s_1, 4, g_1), (m_12, s_12, 4, g_12)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b0a0e80a021784201711c0701936419064181601715c107401003c4d2340d0340c1288a006401 0x8245ea35512ada5d8a55ba45aa3d7a35d152412a7234c35d8b55bb456a36ac56a356285a72447244945a8c56835a7b566a56185a6042495c534b4347204c2a3f1a37e34bcb47b2479a3f5a37392a3126104a0846001f 10 1023 4 15 11 2047 16 65535
def nh_62 : Nat → Nat := unpackHintV5 0x20d077a325e5077861dbcca6f201b58e637418b0561e1d5ed256c1d540e546154b8c5103d3b914e01d0d5642a150a8041628cb7526d80988526200938a1898c2f66001780000 0x10c2eb0582d6a000043861ee2c0161750000e043860dee22d60085d001021c3027dc3ac58ab75ab438757d43870c3c3b97bdef72f77de0556ad5b870eaf7d0e18eaf7380a2a8738739ce0039cf21c355870c000000001541000870c00156f7180002800004c0086318d18d0022a8026401e3d7a00400000f00045000e1c38838870d1cc03 18 262143 7 127
def f_62 : Nat → Nat × Nat := unpackForestF 0xea350b4bd25dd1520b47bb5dbb450a47a456a3560a3f645a6456635a63567244625660420a37434b495c4347092a09261a3f204c1a37084a0846001f 5 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 30 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 30 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 30 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 30 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_11 (kn_cons lb_36 (kn_cons lb_44 (kn_cons lb_24 (kn_cons lb_34 (kn_cons lb_31 (kn_cons lb_1 (kn_cons lb_12 (kn_nil))))))))) rc_62 nc_62 (by decide +kernel)

def g_63 : Nat := 0x117175715771f7f
def ep_63 : Nat := 0x146008280000164000000a0800160040006200600106060204000e0801121202102210200114145415441040
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 7, g_23), (m_59, s_59, 8, g_59), (m_50, s_50, 7, g_50), (m_58, s_58, 9, g_58), (m_32, s_32, 7, g_32), (m_62, s_62, 8, g_62), (m_57, s_57, 9, g_57), (m_61, s_61, 7, g_61), (m_38, s_38, 5, g_38), (m_2, s_2, 4, g_2), (m_29, s_29, 7, g_29), (m_22, s_22, 7, g_22), (m_3, s_3, 4, g_3), (m_11, s_11, 4, g_11), (m_60, s_60, 7, g_60), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_18, s_18, 4, g_18), (m_54, s_54, 4, g_54), (m_4, s_4, 4, g_4), (m_30, s_30, 5, g_30), (m_53, s_53, 4, g_53), (m_42, s_42, 6, g_42), (m_9, s_9, 4, g_9), (m_19, s_19, 7, g_19), (m_28, s_28, 6, g_28), (m_15, s_15, 4, g_15), (m_13, s_13, 4, g_13), (m_51, s_51, 5, g_51), (m_52, s_52, 5, g_52), (m_24, s_24, 5, g_24)]
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x90048024012009003f25f80f817c03c09e00f007413a01d00e416c1b601b00d41680b401a00c826403201882ac65602a040d2001 0x1156f10c6f104630fc5b0f4570e96f0e1570d94f0d1470c16c0bb570b1560a16c0986c0845a094570885607846065650437f04d650445702d6a06d6f05c6f0545703b6f033570234701056f445ff2c57edb5fecb5beab57e6b53e4b4bdab47cd25fc8257bd247b6a3fad237a995fa795b9e9579a9539a14b909478693f8493b82937801337e92b6c1276385f5f85b548574c8534b84b368472f03f2b03b15837148331182b0c8270a81f0701b01817008130003f 13 8191 6 63 11 2047 20 1048575
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88110220402801002003a3740e81d03a0740e8182b005c2b81608d0180284500811002003080300000000000 0x7b169e257759c9cc60709fdae7f695a99b7264da98b505e139696fa95be946ea118e6c629916e445a8d15a0a6f7e95df24f765bdb9576c53d81275c16960565415940444b1693c5b4c1592046 11 2047 5 31 11 2047 18 262143
def cc_63_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x83401f2f87c3c5e0f066b2158a850a8132984c20d008040200ac50211008040200582002 0xd75bf4b6ecad5b126fbe95ec835ba17ad45ab855ad856b211ac02cae092ac68931825c586a49e9c55a2d9a4b5a9ed5e7356975ba536e92d8a1a6f7a5bda1278f58a126f8b59624688716a14567055d685681181e17f 9 511 3 7 11 2047 18 262143
def cc_63_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8750290d20a4130e604c0981302604638c110620440804650c0142280408801002002104008008410020002 0x40b7e806d8fed51f62c3e6737b8e4f5181d9bf3ab6c744fee49fdc1b937b6096add2958e46b147b6f8c6c716d7e21aea3355876a7069be092fbf23f7946ef05bddcafb993f7126edc49d701d16036686d8d8d91a22eb545568adccf58d9ab131a6f646c8c6d5987393036c 11 2047 5 31 11 2047 19 524287
def cc_63_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8e8e8e1d2a6a09290908280807270696868535050503b383838380700000000 0x4e05c9d69736d1e9e2dd2457a20ad3e11a78164d0242e28d3011a55a2be2379369724d1e42b444c6c8e6d91ad522a3744b62844df0d5a215b2c235d426aae84fdc89b96836 8 255 3 7 11 2047 19 524287
def cc_63_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x81401f2f87c3a9d0e870b49a0d06130180b2582c152a84997cb0431c8e03818088402002 0x2eda4d7237bd8ab775f2e9be5ba4fb8ae36d5c2d2b859b5db16f960d5ab5add757dac8e15716afa36de36db96976ad1ec923d7a3faa46f40152a0224e8249c0294c5b29436518549b04946d16862d5035a 9 511 3 7 11 2047 19 524287
def cc_63_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4290a4290a424566d90641905c970585605455050540501314c1304847b1c061180511405010404 0x6f56fdd8dfb915f6db76d356faadfef1bfc62bf4362e46b5c0d2b7cad6406f6e0ae6011f641eeb561d50bda6d7745ab67c5acc6ad92d6a5a2ea935dd7697a8d1f4923e823fce46f9a51f2c9fe5137c824f8c113103660c5ac58b78715f082b60046 10 1023 4 15 11 2047 19 524287
def cc_63_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8282a028085e10841d4741b26c1a1681555414148920481114410122080200800d4300c03000c00 0x3fd2b7f156fc8cbf6da395b073b58e36946a11f781efcd65f86d1ccd6b741efa370f66b1e99cbd739f7b72f36c5e4d83701ef826cec48dd4097b13375266ef8afca96bb92bf6a56eb48ee015ccc23f4827e7addcd1bf95316486f3208fc75bf893770a56 10 1023 4 15 11 2047 19 524287
def cc_63_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82739c2709c22588220791e0709c0701c0701c05d4e9380d1340b22c0a128046100310c03000c00 0x8e45d8f4553b0478e56e8dd638d5628ba6f6606f8c3648bb563a057880358ab6c8783589d6f8936288b5a8826f87a578fd6f8eb6e8cb568b26f8a2576586f39857870350d8278616c85b5785156390578456f83a6f832576506f388570d0278216c81b578115680934 10 1023 4 15 11 2047 20 1048575
def cc_63_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8e95a42639825194250906047c5f07c1c3701a26818260180601354c11244110441103503a0c003 0xa0d7da04709fc5aa746da636da2b47a12479f2379e16c9d1549b8149d2459ba479db579c9569c0189b0146fa3699b47990471d037985689285d9746e9526f9656895b659535d9205d1c037944609186d9356e92b6f9226f91a3798d6297b6f96b5d94a6f93a377f92a6686f9105d1b8370e0278e36c9036489835 10 1023 4 15 11 2047 20 1048575
def cc_63_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2709c243631805c57054950504e6380d1340b2284a024481200801886014423080200080000000 0xaf56faec6eae456b556fb4567b1462afc5aaa16f9f167939576706f550673c857ad84d02017aca5fabb5d1e037aac5aac347ab247aa2373c0471d8370e827a916ca8b57a8156a0a37a6c55a3a6da524fa4a47a3e80a5d71a4570a325fa2570a1b5d 10 1023 4 15 11 2047 20 1048575
def cc_63_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c08258208015755605035004e14e04834804044004004003a32a82a02a02052001e11e01a21a01a01810e50e00e0007 0xbf46eab96fa19676986f59867be56ec7562c5b6fc436bc2367bfb63beb5dab16fa896ba11679d9638a13f8593b83137819336906f59067bd85d2f83f1f8370b81f03017b9b6cbcb64b8835bbb7cb9c5dbac5540847b9d6e6886f580673f845b8d6fb8362b7b5abc56fbb567ba36eb93566806f578673f057b7035b6468b0460b0c58b5865af04db4c70b386db2035b2366b035ab3357b2b563d857b1837b0d6eb0362aa96f9f9676786f5586702817 12 4095 5 31 11 2047 20 1048575
def cc_63_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2b0a868267d81601715c17054950541323d0f02d0b02c092240901c8701c07010c401004010004 0xced60cf45dce347d9c6fd8c55d736fd6363d4355d2b4bcfb47949478b13f83937cd855418473103f2083703817cb349cc455cb57ccab7cc9d71c9570ccc6dcbb6dca34bc8b47c5369c1b61c78473083fc6d68c6065c5670c4b6cc3d70c317cc2970c1e70c136cc0b54c0035 10 1023 4 15 11 2047 20 1048575
def cc_63_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41d0f90f20e03a8f50624c40dd9b0303600a114028048490101200400800b29602c04888090020038470007 0xdf67aac97fa3177d0a7fdd846dd6726b5726a87edc56ed026f530620a01ae456ee356be0d63dfd62cfa6fc8a67dea5fac16fa2967de15f789276a06f6186b5a86752063dc85fdb85d23055db0530f0270901b05017d9464d5365da355d945ed835f2283704817d8465d7c55d4c64d6b56d5c6dd545fd4b529594742847d3b64d3035d116dd1678d2569d1d68d095fce065d005d2105504017 11 2047 5 31 11 2047 20 1048575
def cc_63_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x8608608226306205e25e05c15a15054e14e04c14c04444404023083003002c218a161160122120120101100027020001 0xeec5dc6247f246fe445df1c57f0c55d726ff0257c5a47ef957979477b9272905def057ee055478471082705817ed356c4257c3137c2a47ec46de936dc2247eb96ceb160e8b54e9c55e8c6ed6a6fc0a4546845e7b5ac0257ea56fe936ee8356d626fbfa5746057e703510027e5b62d326fe636ed2a6fca2676b86f6286b5c86753863e50351382b0f827e3d6ee3c6cdf26ddd87ce2a47e21477a927dd06d6b04de1847e1045e0047 12 4095 5 31 11 2047 20 1048575
def cc_63_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0168ed0581b0150aa0502a0130a604c0943282504819011849d1202402904088010001000000 0xfd57cf1454fc368fc46cda26f7e127fa37ce8b54f957cd9454f7d7cf657cb5a37f236fea363fcb5fe435dfbb5bfb357fab55f9b53d9a6ff8a5ff8257bc23fb5237f715ff69578f93f841377d127f585f4b05df5057f48553583f2a0371102706817f3b6df326cbb23fb4237f1464f145ed7a5f7c92706017 11 2047 5 31 11 2047 20 1048575
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_63_15 (Nat.sub p 480)) (cc_63_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (cc_63_13 (Nat.sub p 416)) (cc_63_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 448)) (Bool.rec (Bool.rec (cc_63_11 (Nat.sub p 352)) (cc_63_10 (Nat.sub p 320)) (Nat.blt p 352)) (Bool.rec (cc_63_9 (Nat.sub p 288)) (cc_63_8 (Nat.sub p 256)) (Nat.blt p 288)) (Nat.blt p 320)) (Nat.blt p 384)) (Bool.rec (Bool.rec (Bool.rec (cc_63_7 (Nat.sub p 224)) (cc_63_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_63_5 (Nat.sub p 160)) (cc_63_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_63_3 (Nat.sub p 96)) (cc_63_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_63_1 (Nat.sub p 32)) (cc_63_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 256)
def hc_63_0 : Nat → Nat := unpackHintV5 0xaeb23aa6f9ee9f55e998c1a592958b8de12d89592282e19e7d815878ed2573f53e6e7d5e660a1d5fe18a5a55635405944f113d454274419ce938c6362fee362bb50e29e8732285d91b75c417c8eb10e9b80c013a06915c02151f000085000000 0xda73e1cd874eac183060ea371b8183060c1d40eeea87551aaa6d46aaa351aa0d506a9b56555555555501987c362c0d8b00603221160a0884c26132604c980301904c51ea027700003830e0c38b060c387060c3c1e0e2e8387a0733950ea875543a1d550e8b551aa0d546acaaaaaaaaaa001dc0e0070001600000000000000000020801dc0058b0e1c38716ac183060c0570785b3a162e81c0e543aa5d55168b5545a8d506a83551ab2aaaaaaaaa8000030060077000000004000000000010400ee00ac1870755552ba83d40ea4f402a1d52eaa3541ab2b2ab28d55995555555554005800001dc80800000000000000020980820077000560c38385d41ea0750baaaaa0150ea97551aa0d55916aaccacacaaaaaaaaaa000001040077000000000000000010400ee000cf833e7c183543aa8d546a83551ab2aaaaa801f018022c14110984c06130984c51ea0277000e1c3870e1c387060c183060c002aaaaaaa9554001455400000000800000000000000000150ea87060c18350754caad54aaaaaa0deeaa001c0000002000003801c0400110001800c0808041e0220000000000000001dc0000e1c3870e1c387060c18302aaaaaaa83870e1d3a3c7a7478f060c183aa00000000000000000000000000000e0c383aaaa0e1c387063c1d50007000800000e00700180040400f01000000000000ee000130e1c387260c18307015501447c3871e4c7931e0c1830754000000000001f00098000c0080780006cb870e1c39b2e0c183074001554001447c3871e6d1e3cda3c783060c1d50000000000000000000000000001b2e1c3870e6cb83060c1d55503a0755773e1c38f368f1e6d1e3c183060ea800000000000000381b000000000000ee001f003806c000d8bc00060030220217803c040000f9f0e1c3873e7c183060c03f079bafa4ebe81c0e3e1c38f468f1e8d1e3c183060e1e8e0000000000000000000000000000060c183aaa2a3e5c3870e1cf97060cdd0001f0e1c783060c1d523478f468f1e000000000000000000000000007c187066cf870e1c39f3e0c1af36bc1838fd5552f803e1c38f063d183468f1e6d1e3ea91c00000000000000000000000000007c187067e0f03a3e1c38f063d18387a38000000000038000000077000f801c0060010000f010000060c183060fb830e0c1830e0c3c1e2e5e8b9ba070383870e1cba3c797478f060c18387ab80e00700582c00160b0001800c0801600b010000e00002c160000b000000003800017098000000000007707517061c1d5523d1e2c1600b05801c0e03019102c40003c00001c003bd41c187065cb83065c183abbc1ea0f55070e1c397478f2e8f1e0c7ab075407003802c16000b058000c016040400b010000e00002c16000400000000700002e13000000000000ee6cb870e1c39b2e0c1830755540e81d55dc3871e6d1e3cda3c783060c1d502c00e00b058002c1600030018101002c04000580b058000001000000001c0d84c000000000000003b830e0c1a87066e372aa0d5ee83160b00582c00e070180c816220001c5800007000eec736f7ee8f4160b0580b1604c99dd0e87061c1aa0d50f0795936a0e90ef755555506aa0700380880082c000600b0200580808000700004160000b0000000038000213000000000000eea8754b83060c1a835707936aac0e072aaaaa837baa82c00e020b00110001800c0801602020002c00000005800000001c000000000000000ee9c1d170e1cbad52aa8b0380c0060440b05802c1602202e00000e00001dd5830e0d50ea97555075554b2aaaaaaacf705801c00600b010580088010100808000b0004160000400000000070004260000000000001dc187070781d070e3c18f070f816007001802c0801600b01000160002c00000000e00000000000770e1c3870e1c387060c18302aaaaaaaa83870e1d1a3c7a3478f060c183aa00000000000000000000000000000e0c383aaaa0e1c387063d183aa00000000000000000003b81c00e00300080801e0200000c183063c7831e0c78f060c78f060c78f 24 16777215 10 1023
def hc_63_1 : Nat → Nat := unpackHintV5 0xb3a63daf2121ada85ea316a59de94b98356d9698678c5691825e7e8098717cc0f677f93273412e6e4140671dc96065ae5b314d57a0e44fc9f649ad8743bd7c3f411f3aa9263499842ec97429dd3b24c147207d1116ce6c0de63a06d9c30001b6 0x1d833e0c993267c99326ac18326ec993060cdc6e071b805daa1d506abf547a3d8115551eaa8f47aaaa8f555661f018cc26ac09930885045822130980c464c9955011dd41811e280001c183060c1d55070e1c387162c3870e1c3870e2c58327008745a3d1e1dc381c8000000043a2c5870e2c9abbefdc59dc00e0c3830e2c1830e1c1830e1c3870e1c3870e1c58b0e1c3870e1c3870e1c58b060d993660c1d5555555001c3870e1d0e1c3a1c5831e0d9a3c793478faa03b81c00e0002c1600004000000000000cc20800ee00000c187160c00e1c3870e1d997060c1832e4c9c366ed993265d997aa047a3d1e8f00000018033099101dc183060eaaa19970e1c387665c183000a000761c38f060c183aa668f1ecd1e3c0000000000000000180000000000c716b5c9a4c58b77dd1e8fefdc58b0e1c387160c183060132e1c3870eccb8b164c98b162c58b162c58b16cc183060c183060eaaaaaaa800e1c78b458b168b1e0c18306cd1e3c9a3c7d50000c01801dc0000000058000000000c20800ee0000ec187064c9870e1c3932e0c193764c98307555400b361c3870e2c583062c58b360c18000003b0e1c7831efc193563c793263c7d50b458f168b160b0000000582c00201600000013082003b80000000077279c9974e0d6ea74e0d26bbefdd383a2e1c397064e010ecf41a9d068366553afd54ea79550018022077000000e1c3870e1d997073d98305555069d383670dd932e4c9b326ccb97aa400000019c407700661313832e1c397060d3a7060c1830555861c3a75669dd934e4c9a7269d3a7aa400000001c407700760c383aaaa5555594665c3870e1d997060d9a7669c1835000500000000000000000000000000000061c1932e1c3870eccb8306cc9b3060eaaa80543aaaaa0d5526935559aacacaaaaaaaab2a000000b000000041003b800033082003b8000000003060c193264c9933e0c183060c19b366cd83a070300dc6e070380ee0007c79f1e0c183064c78f263c79b1e6c7c3cdc00000000000000c183064cf933e0c183060c19b8dc0e07007c79f1e0c183068c7931f0f3700000000000000c020000001ea4c9a8306824c9a0e0740c98307dd8da4e277700ef75547a0d1e82c264c993060c18300993264c183a060c1d03060c983060c1f75f1f8993a0713bb8381c00f3e3c98f263c183060c98f263e1ebe661f0984c06030984c881e33019f064cf87261c183260c1af8fc0e5f003cf8f063c1a3c793478f87af83e0301604c58440f026130184caa808ee3c26001f3e7c39f0e7cf83060c19f0605555555551f1e7c7a3478f468f1e0c18f060c1d5000000000000000000000000400001f067c1d5551f1e7c7831e8c1d50000000000000011dc00003e007001800403c04000000060c183aaa2a3e5cf873e1cf9700060c280015555555554000000000000000000000000000183060eaa0777aa8fd41ea0754aaaaaaaaaa000000000000000000000027700000f801c00600302020220020004000000f9f3e1cf873e7c19f060c18300f9f3e7dbaf4f275ede060c183b60d55555555554000000000000000000000000000183060cdc6e060c066e3e5cf873e1cf97060cdd0002aaaaaaaaa800000000000000000000000001f067c19b3e7c39b0e7cf8306bcdaf060cdc6e071b80555555555550000000000000000000000000003e0cf833e7cf9f076c1aaaaaa8000000000000009dc00003e007001800400080000003060c18307dc187060c187067c3873e9d3a793db4f03060c1aa1d52eaaa351aaa5d46a83541aa8d59555555555400e07138b04e2c0180c562b1160a0884c0e132604c98030184c2628f5013b80547c187066d38306ad3830707bb870f41c387071b950ea975551a8d552ea3551aa0d536acaaaaaaaaaa0070386c581b1600c564422c14110981c264c0993006132098a3d404ee007c187075507bbd547e81d49eaa543aa5d546a83565655651aab32aaaaaab23d5540888888a0a060504426070184c88a20a264c147a809dc00183060eaa0777aa95d41ea0754a87551aa0d506acacaaca355665555555647aaa811111114140c0a0884c2603019114113051ea027700 24 16777215 10 1023
def hc_63_2 : Nat → Nat := unpackHintV5 0xdc811fd5dda9d0d542ca8594c4b175bebd7dbbecb4b8a4d2b3a141ab6e0d9e534795c2248e6dd58849897c2709770d466eb6166729e35a633252a9ee4a8a0843a5b93c35dc335e362c25ce26cd56209d8c1c211f181d010f4e3408d59e000235 0x33e0eaaaaa83d40eaa0079f1e0c783aa987cd444444505044130980c2611de828784c00264c993267c183060c0ee7cf9f3e00001f8fc0c1c4c9c0e07030703071f1e7c7931e3c98f1e0c183068c7a31f0f470000000000000133e4cf83060c1807e3f03a2740e071f1e7c7a31e4c783060c1c3d1c00000000000000300098000007cf9f0e7c39f3e0c1830601f8fc0c1d272740c1c0d7c7c79f1e8d1e3d1a3c783060c1c3d1c0000000000000000000000000000cf83060c1d55151f2e7c39f0e7cb83064e8000f8f3e3c183060ea91a3c7a3478f0000000000000000000000000003e0cf83264c987261c99f060c993260c1d555007c79f1e0c7a3064d1e3c9a3c7d5000000000000000013082003b800007061c1d555070e1c3831e8c1d50000000000000000001f067c19f8fc0e5f1f1e7c7831e8c1c3d1c0000000000000000007c19f067e3f0397c7c79f1e0c7a3070f4700000000000004770000000f801c00600003c040000000060c1833f0781c0e060c1830e1c183060c183060c183a03e51f0e1c783060c1c3d7cdd1e3dba3c7870380c064437160dc580f3384c0e030183064032809c03c260003060c18307dc187060c187064cb870e1c39f2e4cb9326ddbbb26dc9934e5dd83060c1bb060c183060cfc1e4e6e979ba0703803e1c38f4e8f1e9d1e3c183060dda3c793478f87af8381c4e2c1b8b006031d8b0262c22078130384c98132600c060c1955011dc784c00060cb97060c183064c1832e0c183060c1d1b3745e0f0307033727478f4e8f1e5c3871e0c183070f37171605c58070380c06440f0b80c18132604c0e030603264030784c00267c997061c193260c193060cbc1e264cf838dc5c3871e4d1e3c9a3c7831eac1c3cdc1c0e131604c58030b9103c2e130384c993061320983c260013060c19f069c1930e1c183060c3870e0c183060c183064d383060c19b8dc08f47834e9c7931e2c16170984c260307511dcf830e0c993264c3870e1c993060c9bb264c183366e0e6e071b80264c98306eddbb060c3870e1e80d947c3871e0c7bf064d58f1e4c98f1f0f373b478f768f1e1c0e031984cb81326110cc58331603c6613260726030f93265540477a02700f098004c183065c197065cf9b8dc4c983060c1832e5c1830707e47a3c1ab2e3d58f160b0b85c264c984c82613260c183060c1832e0c183060cb832f07939ba3e6e81c0e2e1c38f4e8f1e9d1e3c183060d38387a78381c2e2c0b8b00603220785c260709930264c0180c8060f098005c187065d7c1cfc0e5f13264c1832e0c1d01f28b870e3c18f560e1eae2e8f1ead1e3c381c0617220b8b02e2c0785c264c0e4c06132099404e01e130001bb060c183264c99f264c9bb060c183060c993060cdc6e060e066e01dbb3e1cf874eec183260c18307400ca763cf8f060c18326ec78f264c78f879b93a3c7a7478f661f0180c26ec09930884e2c198b01e330984c060c060c193265540477aa00700c0784c00060c19f83c9cdc9cdc7d3870e1c39fee7c9930e1cf87261cfc038f870e3d38f4e3e1e9e4e3d38f0e071389c884e270789c260709930993201900c1e13000b972e0c183060c183060c183060c19783c0c1d173740e07170e1c797478f2e8f1e0c183070f57070385c58171600c06440f0b84c0e030604c980301900c1e13000183060cbc1e07038b972e0c197a02e5170e1c783060c1c3d3c5d1e3cba3c7870380c0644171605c580f0b84c0e0301900ca02700f098000c183060d7c7e060e06be767c39f0e9c18327400ca1e7c783060c1c3d7c9d1e3d3a3c787c060322138b07e2c078130980c180c9900ca00700f098000c183060c193264c183060c183060cb97839b81c0e2e5e8b9ba2e1c7871e3c183060cba3c797478f879b83807006030b8b02e2c220785c264c0e4c060309930264c20183c260013264c3930e4c183060c193066e371326bc1c0e1e7c793478f268f1e0c183070f37330f84c58131600c06440f1984c2613264c180c8060f098000c78306a7c1a7264d3a74e9c9934eedd970e1cb83060c19b8dc0aa8357ba0d54582c160b0984c060ea23b9f061c19f83c0e5f0f1e1c3870e3c78306ed3bb4e0c1a822aaaaaaaaaa870380cae443b160ec5822130380c2642502822000f4f83418358da0d3970e1cbaaa74ea77ea8327041deeaa8347a3d550582c162130193881e930e1cbaa938e9326aa0c1a4c1b1b49af0ef7555547a3d0682c160b10984c9a3d3e0c383541aa4cb870e1c39f2eaaaed499355060dd93060cfc1e564da8397c021deeaaaaaa0d55551e8f550e071411600c1d8b0262c22110981c50498030f932aa023ba20003060c1af8fc0e073b2e7c39f0eecb83060c183060c1a822aaaaaaaaaabb0f80c06443b160ec5822130980c060c1942540a08800a8755f83060c1a8326acf87261dfab5264d55555d83060c183060c1af8fc9b55607038055555506f75555550f88b05006031f8b0262c22110984c498280301830655404774400 24 16777215 10 1023
def hc_63_3 : Nat → Nat := unpackHintV5 0xb0f9e9b0a814af2860a8a1a2a2299e993a3c8dbae083ae837f890979ed67788c58705e0c6f204f67220062313c5d1d455555f24eb9a748ed734052273a51803439862e95692aa8fb24b97c1ec97c19d93c15fcf70f6da40b90f706a13c0001a8 0x13567c3930ecd583060c18155555554aa1d566aaa4d26aa8341aa0d565555555559eeaaac450504444283022130980c183060c006778a85105264c1100150fdc9930e1e7a4d6eade363defdcb873e1c3979e5c1830366cdc6e56f3db932e4c9cf26dcb97060c183073d383878f955554582c160b018306033b9f5e4cf84f264c060c183371b81c0e6e5cf873e1db975045a1e3c78fa5555555555661f0180c88662c198b04426130183101c2326bc060c14110009ab3e1c987560c1830602a1d55549a4d556eaa0d5066e371b3744cdd0381ca3d5555555555567bb30f8cc58131600c0622c142211e284c2603060c1830019dd260a108c9af1100000e1c3870e1c3870e1c58b0e1c3870e1c3870e1c58b060c183060c183060c183003c1e0e2e8387a66ce89b3a070383870e1c3a1c387438b668f1e4d1e3c183060e1ece03b81c00e02c160000000b000000000001803003b8033000009930e1c387265c183060c016dc3870e1c58b000000670789b3a264e81c0e162e85b3a6e1c38f26ac78f264c78f060c183168b1e2d162e1ece05800002c160000c05800000003006007700000026000005070e1c397264cdb36e6c9932e6cb83060c185045523d1e8f478000000030181dc8183060cd970e1c387365e8002a8a80281b870e3c183060cda3c79b478faa0580000000000000000000000000035c9ac6d6f13bba3fbf709932e1c3870eccb83060c18155555555541ea675544e275503a81d001c38f668f1e4d1e3c183060eaa61f340b0000000003b9010000003006007700800020980000035c9ac2d170bbba3fbf7265c3870e1d997060c1830217507a85c2eaa170baa81d40eaaaaaaaa800e1c7b3478f268f1e0c1830730b9aaa0000000020800ee0000030060077000000800000e1c3870e1d99706733955559cf6e4cb9326cc9b32e5c183060e366e4000000060303b8cc01984c060c183670781c0e555455665c3870e1d9975000a666d99ba50000000060000000000000000000000132e1c3870eccb83060c180ce0f336744d9d0381ca87555526935559aa83541aacd595555555547aa0000000000300041003b8000c01801dc0198000000004cf87261c183060c03e7c9c4e060c1831e7c7a3c793478f060c1831e3c3e0b0262c0180c01e04c2603060c1830019dc984c1e13000183aaa818307540c1d555054551f0e1c79b478f368f1e0c18307551141411111104c0e132604c9803019103c260003060c18307dc187060c187075555555517a83d45eaa9bd5503a81d007c3871e9d1e3d3a3c783060c1d54c3e6a2282822222828220981c264c09930060308ef4147c784c00060eaa8197060cb838183aaaaaaaaa4e8f1e9d1e3cb870e3c183060eaa8282222222209930264c0981c0603220784c00a8b830e0cb8306ec183aaaa8a0aa2e1c38f2e8f1ead1e3c18f560eaa228282222220993039309930264c0184c881e13000b972f03060c19707555141545c3871e5d1e3cba3c783060c1d5445050444444130384c98132600c06440f098005cd970e1cd9b060e8d9b0e1c383aa2aaa938f363d1e8f888806130193061328183060c1c5cb97060eaaaaaaaaaa8b870e3c183060cba3c797478faa8888a0a0888826070180c060c09930881e13000d9f0e6c383060c1d55541515543cf8f4e8f1e6d1e3c183060eaa228282222220984c060c09930060c064c8a81e13002878faa369c183366c1833e0c3835054aaaa5555555555a0a08888884450264c0981c061312110007a5c3872eaa9e3a6cdaa8306d34c45077baaaaa3d1e834888426030980c9d23d3e0c383541b2d6a95996aa2f507a555a5956075500877baaaaaa835555558850608888a0a04426071412600c2611de828fa2000306a0c18307554fe371783c0e07178bd4fe37502a0d55562220984c8ef11f060c183365cd87361cd97a060eaaaaa951415555555556222282822110984c06030993050484400543aa0c18306a0ea9955aaa57507a5955556a07503a015555541bdd5555562181422222828110984c5264c1440180c23bd05234400 24 16777215 10 1023
def hc_63_4 : Nat → Nat := unpackHintV5 0xd888b4d3cd2fcfad08c94999c59cebc0614fb9fd99b47562ac79ffa6698498e76194f8fb8ff5418736307f020d71a7576bb17d65b97e5c7a504f6346477df9423d503a2a0530e6512a29af25154520b917173e5f0d467e092109046d2d00011b 0x3830e0eaaa83870e1c18f460ea8000000000000000000183060eaa0777aa8bd41ea07547c3871e0c183075530f9a000000000000000e000000000000130e1c387260c18307006e0f03001c47c3871e4c7931e0c183070f3700000000001b2e1c3870e6cb83060c1d46e0f03060c183a81ddcf870e3cda3c79b478f060c183879b800000000000000381b0000000000000f830e0cf870e7c1833e1c38f063d183463d18f00000000000e000000001f061c19f0e1cf83067c3871e0c7a3068c7a31e0000000000073b8000000007c0180040003c040000000060c183367cf87361cf9f0703060c1d1b8dc0e060c1c01f1e7c783060c1a3478f368f1f0f3700000000000000000000000000003060c19f3e7cf83060c19f1e7c783060c1a31e8c7800000000000cee0000000007c00e0030800078080000004cf93060c183064c1970e1cb93264e26bc9c0c183065c3871e4d1e3c9a3c783060c1ab1eac7870384c58131600c06170b83c2e030384c99306030984c1e130009870e0c09d130e1c3d44c993266cf83060c19b3e4cd9b89939b9b36ac7931e8f47b3365c260b0580c183019dc984c364c993264c3870e1c993060c183060c0264c9870e1c3830600c060cf870e7c9b7264c99326dc183060dbb76737671f0e1c793563c793263c783060c1b7478f6e8f1ecc78f0e0709970264c0180c662c198b06633078cc264c0e4c060c183060033b830600c18130f93260f098000c193260c060cbc5e2f544e0f0381c5e3745c7ab1f2b47b444413260c0641301832707260c183064c9830183a8b972e5cb972f178ba3d1e5c7ab1ead58b0585c2e13264c26030180c183060c193264c18300603065c3872e0c183065d7cbcbc5c3871e0c183065d1e3d5a3c7ab1eac7870380c06171605c58170b83c2e13260726030180c18030604c260f098000c183067e0e1c387a060c0180c18383c0e07070f46c3d1f0e1c783060c1b7478f6e8f1f0f37070380c0633160cc58440f1984c0e030180c180306107c9af0784c00a89970e1c3873e5c997264dbbb6e4dd93266cbb75e0c183060c183060c18306041eee1c3d070e1cdb736be899b9bd0381c7c3871e6d1e3dda3c7b7478f268f1e0c183070f37070386c581b160cc58131600c06440f1984c0e132604c9803060c1830019de0f935e0f098000c183067cb870e1c39f2f4115555555547c3871e0c18306cd1e3d9a3c7d5444450504444130380c8060c28220784c003e0c183265c3873e5e82a0aaaa93d5547c3871e9c7a71e9d1e4d1f55111145111104c0e134e107cee0c1838a81e130009970e1c3873e5c183060c0aa83dde6755555547e99d551389d540e07503aaa3e1c38f668f1e4d1e3c183060eaa61f3511414111114141104c0e03060c1830019de2a2882899301e13000993267c99326dc183060c066ccd873e1cdb7aaa00603066dbc6e67138993264c9d0381830713264db8f3e3c9b71e3c9931e3c183060cda3c7b3478f879b9987c26cc0993006030d8b0362c22078cc26130183060c1800cee0c1830600c180c22603264c9930784c002e5cb83060c183060e060e8b97839b8993a2e4e81c0e2e1c38f2e8f1e5d1e3c183060e1e6e0e070b8b02e2c0180c881e170981c264c09930060320983c260003060c19f0e1c38737151baa81d2f8f870e3c183060cd8f5e3eaa2222222220981c064032288983c260003060c1af361cf8736be80180e36be370381830713264c79f1e0c183066d1e3d7a3c7c3cdccc3e030186c581b161103c66130980c06030600c1844c264c1e13000993267c99326dc183060c09bd555544e27540e9bd41ea272f8184554dc79f1e4db8f1e4c98f1e0c183075530f9a88a0a08888a0a08826130183060c1800cef4544c9944140c180f098000c183063c7870e1c38f1ea08a7c3873e0c18306dcdb79b9b6f2aaaaaaaaa870380c0637160dc58572b8884c0e03101830502613110021f0f364c99b366cd93266dbb72e1c397060c18305367cdc6e55555160b0582c2613018306033b9b363d41834b870e5d54d9b57b35608f9f63683064c9877baaa0d550582c162130180c264d1e932e1c3870e7cbaaab75264d54183060d50683500f870e7d5956e4e26de060c18343bdd555555547a3d5506aa1c0e2822c1b8b0262c0180c04426071412600c183060c00677261f26220013264cf93264d583060c180a7543aa3d1e830456e7cfb326dc993264c9b7060c1835653aaaa3d1e8f555506aaaaacc3e135604c9803018a08b06633110984c060c183060033ba820c0988c99311e2800a5c3872e5c99376cdbb3264cbb32e0c18306155554aaaab11104c2603060c0677a060c183665cf873e1d9975045aaaaaaaa55555555558888a0a08844261301880c1828442200273e7d3933e4d3a82a15555554aaaaaaaab11111110884c26134e088cee0c1838a84400 24 16777215 10 1023
def hc_63_5 : Nat → Nat := unpackHintV5 0xc76e3ebee223b69613b1d530abbd86a2b6429e012d9da41794f22d880f39812db87bbd5c7222676d6d2d6911176185e35d091f5cb4155625a450696f477a3c3f72023a494a3341c22dbd6127c97d1e825218957b1151d10b617c069d310001a7 0xc18030183060c1830e0c187061c3870e9d7b79baf4f03060c1830e1c3874e8f1e9d1e3c183060e58f1e1c0e070e01c38030181c0e070381c06132600c1803060326130983c2600070f41c387819b060c183060c1830741c3c0e0f07818307de066e069d1e3d3a3c7870e1c383060c1c3cdc1c38070e01c0e03019101c0e132604c98070180c064130784c00a00e0783830e0cdaf060d783061e0e1c3c1c387060e37030e1c387368f1ebd1e3c18f7e0e1e6e0e07038700e1c0181c880e070381c264c09930061322613260f098000c060eaaaa4f77aa83d550783d5070e1c3a71e9c7d55544444444440720980c88a2260f0980141140c183060c183060c1830755555503aa0e1c387668f1ecd1e3c183060eaa2282822222203904c985003019103c2600000c383060c183060c183060c183aaaaaa81ddeaa0f5541e0f5507a83d40ea83a1c387438f0e1c387060c183aa987cd5050444444505044070e7c3870039dc180c88a08980f0981101c3870f50700e1c3870740c183060e07770703938f363d1e8f0e070381c0e1c984c261303871fdc7a0c183061c38070387060e81c0c18783c0c1d0381ddc183a060e83870e1c183060d1e3f7a3c7c3cdc1c0e030181c38070e1101c0e070e0303830184c981326104c1e1300381c0038736bc3870e1c3870e1c3870e1c3870e1c387060c183060c183060c183a839ba0e1e83c1e060c18307503bb8743870e871e1c3870e9d1e3cda3c783060c1c3cdc1c38070e01c0e070e01c3803019101c0e070e7c3870039dc9930264c0180c8260f09801c0e03060c1a82283060c183060c1870e1c383060c1bf36fe7e6dfcaaaa835555550e070180c0e1c038700e071103880c0613260a04c262200003060c187372c3870e1c3870e6cd870e1c3c0c1c1cd9b8387a060d555554381c0e07039b0e073b930981c380aa8743aaa1d543aa1c183060c183060c183060d41877e1e0e1c3c1c3870eaab03060c1aaaaaaaaaa837baa870e01c38070388705006030381c440e1cf870e0073ba4c140180c26131100381c50450e0c383669c183669c183aaaaaaaa555555555588a0a08888440e213260a00c264422000074e9c3870e1c3870e9e9870e1c383060c1ad55552aaaac444073e1c0e7726130193a003cb060c387060c3830e0eaaaaaaa90eaaa1d0eaa87543aa0d556555550e8f555567baaab4141111110a0c0881c39f0e1c00e77061322141260881100c01830e1c1a1d0eaa75baa9d4e8353a0d066e37523d55567b870381c40e930180c993101a7061c187061e0f038dca08a0c1a7d69c183a1e3c387a555555655550e070181c880e1c03870438a070e207061320984c98282200703801c1a7060c183061c19b83c0cd874efc3870e1c3870e9d3870e1c3ac3c1caaaaa1c0e070381cf87039dc984c0e1c00e0c1870e0c187061c1aaa1d0eaa87550ea87555061cdd070f41e0f038dca3d5555555555567b870e01c38070380c0e21c142210e281c39f0e1c00e7706131260a104c4400e07000e0c1870e0c187061c1870f070e1e0e1c387060c3a1c387438f0e1c387063c18f1e1c38070e01c0e030381c0e070381c39f0e1c00e7706130984c1e1300381c060c183aaa2a3e4eaa8001830a0003e1c38f060c183aa468f1e8d1e3c00000000000000000000000000183060eaa0777aa8bd41ea07547c3871e0c183075530f9a00000000000000039dc0000000000003e00c006044040110010000f0100200000261c3870e4c183060e00dc1e0600388f870e3c98f263c183060e1e6e00000000000981300018006c078000001b261c3870e6c983060c1d0001b83c0c18000388f870e3cda3c79b478f060c183879b800000000000000000000000000d970e1c387365c183060ea37078183060c1d40eee7c3871e6d1e3cda3c783060c1c3cdc00000000000000073b86c0000000000000f81b000362f000180c006011006c5e00f0100200000365c387365cf83060e800037078183066cdd127bb9f0e1c79b479b47a31e8c7c3cdc0000000000001b000ee000000007c983060c183060cf83060c1807c3873edd7a793af6f03060c1833e1c38f468f1e8d1e3c183060d183463d18f000000000000000000000000000060c18337078183019b8f97a0f1f2e0c19ba0003e1c38f060c183879b91a3c7a3478f00000000000000000000000000060c183375030603060e2f5503a5f1f0e1c783060c1a31e6c7cd3000000000000000000000001f061c19b2741e3e7c1835e6d783066cfc1e3e0e36be00f870e3c18f460d1a3c79b478f918f368e000000000000000000000000000 24 16777215 10 1023
def hc_63_6 : Nat → Nat := unpackHintV5 0xcac12cc6890ec20920bcc950b7b545b29548ae4913a58a30a189009cb5358faf428ad1378152607d051375b5d470a145677e495c22d7580d054f6e284762034315133b21fd33c1d82ea94627c1ba21998a18e62d11bdca0b958a053d9600014f 0x60c183ee1c187065e37070e1c397265c993265c9b7264c983060c1c4d7caa0000001c00410a2e0d383aee1e0f070e1c397265c993265c9bb264c983272c1d52a80000007001040b870e5e81c0eaef0c387266c9f3264c99b266c993260c1830754aa0000004c2613001040387261c187065cb83065d383061e0f172f45cdd03a1c2a00a0aaaa000000b000000000000000000000013970e1c3874e5c183060c193072e0f273749cdd0381caaa000a2aa0000000000000000000000000000c38383c0e89870e1c393260c193264c183a264c9afa555555000000000000000009800000080080000c38383c0e950eaaaa835559555547aa0070380c162c88516a02770380c20414110000060c183060c183060c183aaaaaa81ddeaa2f507a89c4eaa3f1faa81d51f0e1c793478f3e8f1e0c183075530f9a88a0a08888a0a088039dc38700e1c38301911411301e13000b870e5e8d93364cf83a060c18381ddc1c0e4e3cd8f47a3cb85c160b0984c264c0d870e7c993264c99b364c9870e4fb930e1c98700183a266c1830703bb8f1e9c79b1e2c59b0d801b2e1c3870e7cb93266c99f3e7cf9b3e6cf93264c183060c183060c183060ea3707899ba366e8183060c1d40eee7c3871e4d1e3cfa3c7a7478f368f1e0c183070f37070384c581f1606c581b1600c06440f198073b870e01c387264c9813261f0060320983c2600003060c1970e1cb93364cd9b367cd9f266c9c0c1c6e370306aaaaaa2c160b0581cee1c0e1c984c0150ea97554fa7d552693060c183060c183060c1835067c3873e4d59f8f9f272aac0c18306aaaaaaaaaa0deeaa1c0e131607c5822c140180c562b1100e770e1c03870e9305006030984c440002e1c397269c99f3e7cf9f3e4d393060c1835aaaaa5555588880e770e070e4c26032601f061c193560c19f3e0c1d555555525d50ea9349aaa7d3eaa8355595555555567baaab1141411110a0c088073b870e01c387061322141260880007c183060c19b8dc0cd970e1cb934e4cf9f3e7cf9f269c9ac3c1caaaaa2c160b0581cee1c0e1c984c00f830e0c9ab060cf9f060d50ea97554fa7d552693555066e0f133746cdd038dca3d5555555555567b870384c581f1600c5622c142211e28073b870e01c38706131499305108262200001c3870e1c3870e2c58b162cb8b3e2c58b162c98b260c183060c183060c1830600783c4cbd173f42d9d0b1740e07070e1c393478f2e8f1e2d162c5a2c783060c1c3d5c00000003006007700001601dc0e0070161300000000000000e1c387265c997367cb9b364cb93060c183aaa80a47a3d1e8f000000ee1c0e00001c187064cb83065cf83075555555507a83d44e2755178fd540eaa003870e1c9a3c797478f063d583aa987cd01c00160b00000003b90100007703801c0000000209800000001c187064cb83065cf830707a83d42e17550b85d540ea175555555540070e1c393478f2e8f1e0c7ab0730b9aaa0000000020800ee0007703801c00000000000000e0c183060cbc7e5550e1c387265c9973e7cb9f3e4cb9358d9b900000003b8703800007061c1932e0c1973e0c18783c4cbd173f40e672a1d50eaa974faaa4d26aaa0d566acaaaaaaaaa3d50000000000580020801dc0ee07003800002130000000000f830e0c983067cf83067c3873e4cfc7cf9381833e1c38f268f1e7d1e3c18f063c7870384c581f1600c007801cee1c38070e1c184c26130784c00060c183aa8aaa0e1e8001830a0000e1c387060c183aa468f1e8d1e3c00000000000000000000000000183060eaa0777aa83d41ea07541c3870e0c183075530f9a000000000000039dc0000000000000000e00c00604040440040003c040000000e1c3870e1c387060c183a0000f078183000071070e1c39b478f368f1e0c183070f3700000000000001c0000000000000003870e1c3870e1c183060ea0f078183060c1d40eee1c3870e6d1e3cda3c783060c1c3cdc000000000000073b80000000000000001c0d8001b178000c0060401b0078080000000c183061c383060c183061c1801c3870edd7a793af6f03060c1870e1c3a3478f468f1e0c18f060c1a31e8c7800000000000000000000000000030e0c183061e0f030603370783870e1e81833740001c3870e0c183070f3723478f468f1e000000000000000000000000001c187061e0e1c387a060d79b5e0c18783870f038dc0070e1c3831e8c1a3478f368f1f0f37000000000000000000000000000007061c1870e1c383061c3870e0c7a3068c7a31e00000000073b8000000000001c0180040003c04000000 24 16777215 10 1023
def hc_63_7 : Nat → Nat := unpackHintV5 0x84811280b0f47ce8f276d1866df6376a2cf2652d405da1e35d50145bec595b1c345828bd52f54d4bb9cf4aa844458948413d133ac19f39f03436a0d435f42b32a8d32d256127756c2329131d716e17618412b12c0d9d450889450331560000cc 0x3870e1c3870e1c183060c0aaaaaaaa555555555550000000000000000000000000000e0c383aaaa55555500000004ee0007003800c0020201000000000000000007550383c5e81a1d0ea9b4daa6d968341b32ac80b8594103644ee4c261b11060c18783c0e072aaaaaaaa8306a0c1aad17365cbd2822870380c060c1910881c38070e01c0e030190dc442e4c0b93000060c183060fb830e0c1830e0c3c1e2e5e8bd0381ca87543aaa5d554baa8355068355595555555547aa0070381c38070e00c060c1910a1d404ee1c0e172e05d9803019020a088000ea2e0c383aaa553a9d54ebf43a1d0683665547a3e422206c89dc984c4e207061c1b5552aaaacaaaad03065d3972e0c1ad2aa822c44444225050070380c664422172605c9800541c187065cb83065c183abbc1ea0f552a1d50eaa975552eaf55506acaf5665555555559502228282285910b2809dc381c2e5c0bb3006332210504400eea872e1c3f70f0d36ac31e82fbf71e970e875059b0e1e81c0eaeeab30c38786ab2b2a0c440d620d86c26130183060eaa995555656b970e1c387ae5d69556955411622281910a234140cc0e030191088cc9833260006cb870e1c397060c183aaaa0740eaaeea87555536af555541aa0d595955555555654088a0a08a06442ca027766070db3036cc0180c884141100143b03aaa5588261303870e1c387865e81c0eaeeaaab0e19b2e5cdc3370cb97060c183070d383aaa19b906a222198cc2613106a1c197070e870386aaa8743a83060c1832e5c18307179143870e070381c66330b828306aa0c3834183065c18783c9cdd273740c1c0d3caaaaaa1d0eaaaa1c0e070e01c380301910881c0e272609c980301909c440007527066e861c65073e1830f50cbcaaaa0cb83aa8b97a91685c2ca08866330b8cc0e0c04e0c98a800e7b3073367202832e0e2ece400000000383319a170b84c0003830e0c3c1e074aaaaaaaa83065c183a2ebd7d2822870e070e0303910881c38070e01c0e0308110b930260000c1830f078bc5e55555550e5c3870e1c3f7543875564e9e450e070387038722110380c0e070b85c84e22271380141c183060c1d770f0795543870e1cb972e5d3a72f2dd972e5d6a90622a20b8cc26131060c18783c0e072aaaaa870e5c1832f45cb97374a08a1c0e0301910881c38070e01c0e0301909c442e4c0b93000060c183070781c0e5555555a74c3870e1d3ab49d7cb5f4a08a1c0e0306031644220b1600c1801c060320444e4c1393000060c183ee1c187061eaa5550e1c3872e5cb97366cbaf665cb97060c18354188a882e330984c0e1cb87061c1972e0c1974e0c1d54ad2ad52aaaaaaaaac45050444422070385c98172600c66442200272e1c3870e9cb83060c183360ea9556a9a95555555556228282222111381c4e4c1393006032211000187072faaaa55555555e1c3870e6d783066d7af060d550458888a2844a0a06607018cc8844364c0d93000060c183aaaa555541aaaaaaaca8000030004100000000000000 24 16777215 10 1023
def hc_63_8 : Nat → Nat := unpackHintV5 0xa385809db175980d699458ed8e697c88cd67836d587fc8e97929a87411466d29ba67e95062316e5ca56358750c54b0f14ed1784a611c45d9223fc9843a69583609182d36352689ab1fe5a91b691f16b52d1009ab0a616a08308c0371300000dc 0xc1d55032e0c1870703075555555549d1e3d3a3c7870e1c383060c1d5505044444444272609c98070380c06440f13801507061c197060dd83075555141541c3870e5d1e3d5a3c7831eac1d55145050444444070385c981b2600c22078ac000e1cbc0c183065c1d5545055070e1c397478f2e8f1e0c18307551141411111101c0e172605c9803019103c3600072e5c3870e1c183a0e5c3870e0ea8aaaa4e3cd8f47a3e22a20d86c2e1b0183060c1c1c397060eaaaaaaaaaa83870e1c183060cba3c797478faa8888a0a088880e070180c2e4c0b930881e27000d870e1c383060c1d55541515541c38f4e8f1e6d1e3c183060eaa2282828a222200e1b2606c9803019103c4e005070f545cb83065cd83061c18706a0a95554aaaaaaaaaaa14107228848442e4c0b9300e070186c884420160743870e1d553c74d9b55060da6988a0ef7555547a3d069111489c261310e87061c1aa0d96b54accb5507a83d2aad2cab03aa8043bdd5555541aaaaaac1c894182208ef4152207038a0b300611141022100b0183060cd970e1c387365e8183aaaaaa545055555555558888a050484436070180c364c0d930884400543aa5c183060d41d532ab554aea0f4b2aaaad40ea07402aaaaa837baaaaaac2c896160a2110477a0a911581c59828030191141022100b0183060fb87061c1d5070e1c393264cb936e4c9932e4cb83060c18023d1e8f478000070984c0001c404c03830e0ea2a8387260c1972e5d3830740001c3870e0c7ab07545d1e3cba3c780000000002c000000000000000000060c183aa8a4e5c3870e1d397060c9d000270e1c783060c1d527478f4e8f1e0000000000000000000000000001d41cb5a43870e1d549bb4993541a7260c003bdd5506aa8f4780000711000271020874ba0e589870ead264d55526ec183060c01541bdd540000980088038810061c1d55513261c3870e4c183264c9830600001c38f063c1d513478f268f1e0000000000001300002610010004c000061c1d5555507a81d540070e3c18f075530f9a85914411de82a880380c2228201e0402c0e1c3870e1c387060c183060c002aa9556a9554001455400000000800000000000000000150ea87060c18350754caad54aaaaaa0deeaa00000000477000003801c0400110001800c081010000000000000000000003870e1c3870e1c183060c0aaaaaaaaa0e1c3874e8f1e9d1e3c183060ea80000000000000000000000000003830e0eaaa83870e1c18f07540000477000003801c00600100f0100000000000000000183060c183ee0c383060c38383d41ea170baa85c2eaa07503aaaaaaaaa003870e1cba3c797478f060c183985cd55445050445540477880e070b9702ecc0180ca0858440f158008743830e0d506e3583d41e95569616ab03a85d552b32d500877baaaaaa8355555588506088aa808ee881c0e282cc0185042c221100150ea97060c1835070ba83d2c2d55556a07503aaa6556aa015555541bdd55555621814222aa023ba22b038b305006032821611088000c38385d41ea0750baaaaa003871e0c783985cd5544445540477880380c282161103c0003870e1c3870e1c183060c183000aa555aaa555400015106aa00000000000000000000000000a8754383060c1a83aa6556aa55555506f7550380082c000000008ee00070038080022000300181020f01100000000000000000000003870e1c3870e1c183060c38302aaaaaaaa83870e1d3a3c7a7478f060c183aa00000000000000000000000000000e0c383aaaa5555550000000000000000000e0c383aaaa0e1c387063c1d501c0000008ee0007003800c00201e0f010000000000000000000e1c387060c18302aaaaa9555555554001600c00004000000000000 24 16777215 10 1023
def hc_63_9 : Nat → Nat := unpackHintV5 0xac15dda4b1d9a0a10499f5ab9650e9909d6d8dccb489b50686ccba824d207dad2879dcf475fcf86e35f26869735d46c9577d7251418f4b298646952542ecea3a163634c5542d41e1274d7d22ed181f44ea1bb8e315b5810eddb608c985000232 0xe0c1870e0c187061c1aaa1d0eaa87550ea875550755555554b2aaaaaaaaaaacf783d07023bc430284430a073e01c38070380c3e27c14221108058007060c387060c3830e0c3d070f41e0f03a0e870e1d0e3c3870e1c18f070f83870e1c3801cee0c0e44070381cf8070e01c0e030f907c1e1f00e02c5550e1c183060c183000aaaaaaaa5550005155000000002000000000000000000543aa1c183060d41d532ab552aaaaa837baa8001cee0000004000007040011000180c00601010083c04400000000000000000011800aa870e0c18350002a9956a95555511ef755000000000000000000000000e1c183060c183061c183060c0aaaaaaaaa0e1c3874e8f1e9d1e3c183060c1d500000000000000000000000000007061c1d555070e1c3831e8c1d50000000000000000002a1d50e0c18306a0ea9955aa95555541bdd54003800000040000000000000000001c1870755541c3870e0c783aa000e0010000000000000007061c1d555070e1c3831e0ea8000e7700200000380300080801e020000000000000000003060c1d555070e1c383060c1d50000cee00000001c00e003080801e02000000000000000003061ea07507160caa83c5e2f17aa47a3cb8f563e5742e165044331985c6603061c006007160c0019cce2f3391e8f2e3d58f000000e030b85c26003315803060c183061c38b060c0180c18783c0e07175f4be83870e1c183060cba3c7ab478f87ab838703870180c060c01830880e070381c06030b93026100f158000e060ea8387a060c22aaaaaaaa83870e1c183060cba3c797478faa8888a0a088880e070180c2e4c0b930881e2b002a0e1c3870e1c387162c58b165c58b162c58b2e2d783060c183060c183060c18157783d41e85cbeaaaaa83870e1cba3c797478f168b162d163c183060eaa2282820740c08ef11142c0e070b9702ecc0580b1600c06440f158001c397818307540c1d555555555070e1c397478f2e8f1e0c18307551141411111101c0e172605c9803019103c560003060c1af0e1c38736be822a5f55540e85c1c38f060c183368f1ebd1e3eaa222282828a221981c06030d930364c22078cc00060c1830e1c3870e1c38750450f0781c0e2e6e8b97a55555555550e0701880c18284422a070380c06172605c98447110020f42c58b362cd8b162cd8bce1c3870e0c183060a1eaa55555170b2801c0c8eea4c261b0581d418343870e1d54d9b57b356083cd30317077baaa0d55222291984c2621d0e1c3870e1c38755516a2c5aa83060c1aa0d06a00783caca8ba162e81c0e43bdd555555545a3d5506aa1c0e2821c0183060c1800cef108a81c0e282cc0580b1600c064088000c183075554acb870e1c3ab2ea08b5554aaaaaaaaab11031288a0506157b8ac0e0301910ac982b26088002c5870e1c38b560c1830602a1d52eaa8b45aaa2d541aa0eaaaaaaa965555555555559ef1103a06047760508861551581c1602c5803018b30508844000e1c980c18300060c03c1e2e5e8b9ba070383870e1cba3c797478f060c18387a78000001600000000000000000000005070e1c397265c993265c9a7264c983060c1805770f07aa91e8f47a3c000038002c0180743870e1d5499349a755060d006369393c1deeaaaa8300000e000b00609c3872600874baa4d4ea9349a0d0754caaab3dc00000982c01a1300009870e1c393260c183060001078993a26be81c0e0e1c793478f268f1e0c183070f800000000000026000b0001800000002c5870e1c38b060c183020f0ba162e81c0e0e1c78b458b168b1e0c183070f8381c060c183060033bc40b058b00e0b0162c0180c807800030755503060ea8183aaaa0a8aa0e1c3872e8f1e5d1e3c183060eaa0e4541411111101c0e172605c9803019103c36100b0183060c183ee0c383060c383aaaaaaaa83d41ea2f5545eaa81d40e800e1c3872e8f1e5d1e3c183060eaa61f350722a0a08823bd055101c0e172e05d9803019114100f158402c 24 16777215 10 1023
def hc_63_10 : Nat → Nat := unpackHintV5 0xa8ad8ca26d909b75be946dc28fe9218e9455836acb7ed52575ee3a71911769c5f3627dd25e590958398852b1624e411c460a0e3fc1923921a83594e33554103438472e39802dcc1b2c944e21d6b01b7d9616d52a0dee3a0a38ed04e156000138 0x3060c1f70e0c3832e1c3932e4cb93264d393364c993060c183371b8783c5544160b0582c267c99f0264c980c1a9f26a7c993264cb830e0cb97060cba7060cbc1e2e5e0b9b0071b95551415554381c2e2c0b8b0061722110993039314140184c82622001b2e6c39b0e6cb83060c183260cdc6e366c0d9b8070395541515554d86c362c0d8b0060322110984c55050180c183ee0326038364c9888000cf83264c3930e4c983064c993060cdc6e071b878f01e3e15555415155987c0633098b0262c221109930988c1830980d58464c988a808c260306a87555541af97c0e5f28f555555559ef40e9168a9548f55468c1a306a2a48d7cab2385870e2c5a1d1fdc7bdc5c0070e1c3870e1c3870e2c5870e1c3870e1c3870e2c583060c183060c183060c1d555555503a0755770e1c3870e870e1d0e2d1e3cda3c783060c1d511de0e107a170b0a2088a22880e07038b00e1c0db3036cc0180c881e330000183060c3870e1c38b161c3870e1c387162e07555035555558ee1c0f500b85942c0e1309802a1d50eaa8743aaa1d160c183060c183060c18306a0c3c1e0e2e8387a55581c0e555555555506f755039dc38700e1c3a1c140180c85901d10381c0e2c03870598280301902200007060c183075541c3870e1c58b0e1c3870e1c38b16b54aaaab1dc381ea8816070984c003830e0c38b060c387060d50ea875543a1d550e8b5550755555554b2aaaaaaaaaaacf723bc1c20f442c2c1442889850381c0e2c0387006331660a1108800007061c187160c1870e0c18783c1c5d070f40e83870e1c3a1c387438b063c1c3e039dc38700e1c3830390b203870381c0e071601c380308078002870eaa0c183060c1800555555552aa8002a20d540000000000000000000000000150ea87060c18350754caad54aaaaaa0deeaa073b80000000000001c1000440006003020201010000000000000000000000183060c387060c183060c38302aaaaaaa83870e1d3a3c797478f060c183aa0000000000000000000000000000e0c383aaaa0e1c387063c1d501cee000000000700600101003c0400000000000000000060c0180c183060c187060c3830f0793afa6ebe81c0e0e1c3874e8f1e9d1e3c1831e0c18387c1c06070e00c180306030e44070381c0e1f2607c980301907c1e1f000387aaa066c183070381c0eaaaaa81ddeaa4e8f1e9d1e3c3870e1c183060eaa828222222220f9303e4c0381c0603220787c00a08a0e0c38336bc1835e0c1d507a0f40ea83870e1cda3c7af478f063df83a1f54450504451444070386c981b2600c3e511f0787c000e1c3d41c20e1c383a81c0c1d5dea879b1e8f4787a2220d86c26132163c7a1cde3063cdc8f1633018307070e1140c1d555540eaaaaa83870e1c183060d1e3d1e3eaa0e4511414111101c0e030187c981f261103c3e100b11e1d1e9b0e1d3a1d1fdd1e3dee0070e6d7870e1c3870e1c3870e1c3870e1c3870e0c183060c183060c18307555555540e81d55dc3a1c387438f0e1c387478f368f1e0c183075507a0e0477a0a08888880e7c038700e070d9f0367c0180c881e1f080580c18306a08a0c183060c183061e0f0381cacdd2b374aaaaa0deeaaaaaa1c40603038705088440e070180c3e4c0f93083e2200003060c187372c3870e1c3870e6cd870e1c3c0e83c6eaa81aaaaaa878391de20d81c261321602aa1d0eaa87550ea87060c183060c183060c1835061dfd070f41e0f2aac0e072aaaaaaaaa837baa870e1c3870039dd0e0a00c064422073e01c38070389f050060320f8880701603081870e0d0e87553add54ea741a9d0683aa6555559ef1150924c261f103830e0eaaa94114183569d5a7060eaaa9555555555560e25111140a0c281c0e030f9107c981f26088402c00e0d383060c1830e0eaa83bf7e1c3870e1c3874e9c3870e1d6a9555543c1c8ef107c0e130990b 24 16777215 10 1023
def hc_63_11 : Nat → Nat := unpackHintV5 0xb34daeacada8a5f5ae9eadd29a09299505418d61e9880d557fea097a715e7565437089376b614a66c52761d93b5ced3b57d1475418ee4d4db348bd243f2e643799e52d9a802d042527bd521fd5fa1ec0451a591a1395b10d3199068da90001a3 0x5cb97060c183060c1c0c1d172f0736ad2a8381caaaaaaaaaa1e0f171705c5c0381d54aa5c3872e5c9970b932e03060c1c6cdcab172f03060c1af361d78736be8183060c1c6e37038183072aaaaaaaaaaab40e071b1706c5c552a9b360c183066c99b0d933646cdcab1b3713264c183060c18306030605c3872e5cb978b9b2f03060c1aaaa282aaa870385c58171600c06170b8884c981c98a0a00c061309888004c987261c993060c183060c0183063f3e7d993264e26bc9c0c18306aaa0a8aaaacc3e131604c5803018cc662213098a8301830613261311a2a002a1d5060c183506aab03060c1aaaaaa837baaa2d150183060d551a35150183060d1a355468c183555418306aa0c1ad55555552aaaaaaaaad5545455552a9f0e1cfab267c564cf80c1830754ab540c183060c1f7061c183061c1d555555525d50ea9755556aaa0d506acaaaaaaaab3dd555aaa8a8aaaa5464553e1c39f4eacf89d99f0183060ea951455aa060d554183555060d0755555554aaaa1d0eaaaab2b5151555554aa7c99f0f933e070e1c383060c1d52ad503060c187060c383060c183ef55555554875550e875543aa1d506a8356555550e8f555567baaab5151555554a8c8aa1cf8703870e070e1c383060c1d52a27d156a8183555065c1832e0d060eaaaaaaaa955547a1d555556a2a2aaaaa9553933e27267c2e1c397060c183aa55aa54b830e0cb8306ec183aaaaaaaaa55555555555aaa8a8aaaa552e1c3972e4cf8ec997019f0754ab545cb974183060cb83aaaaaaaa5555555555aaa8a8aaaa552e1c3972e4cb85c9970183060ea956a93d30e9c3d3a60c18306ad555555552aaaaaaaaaad5545455552aa3469c9a313934603060c183aa55aa060c183ee1c18707544c3872e4c9934e4db93264cb932e0c1830704aa8911104c2603074aa5c1870755544c993060cb972e9c183a08a5555555450888888a0a044264c0e4c061322141411000183060eaaa93973e1cf874e5c183274114aaaaaaa8a11111114140884c26030603264428282200033e0eaaa8993261c987260c193264c183a08a5555555450888888a0a04426130188c9932889545400060eaaa9543aa0d556555559eeaaad555552a322aa3460d183aa545156a9060c18306ae0f0381caaa0c1a8306ab43c78f1f4aaaaaaaaaa1e0f0381d54ac5c2b170aa7c3873e0c183071f5f2b267c564cf8ab1f57030060c0621d2ea9349aa4d4e83419b89c8f55559ee2c160b107a4cf93260c1a4c98a07c983060c18307dc187060c18706a8754baaaad554baa835506835707939ba566e81c0e51eaaaaaaaaaaab3dc3c1e4e2e158b807039168a9548f553e1c39f4eacf89cf80c18306a2a47d7cab1f57030e0c1a0c183ee1e0f0381ca0c1aaa8306ab43c7870f4aaaaaacaaaa1d0e1e0f0381d541c3c070f087550e1c387060c1838f9f8f933e1f267c5583878183060c383061c183060c1f75543a1d550eaa1d50ea83541873741c3d0783c0e0728f555543a3d555555567b870f01c3c0783c0e0721d152a90eaa1cf8703870e070e1c383060c1a7d1523e7e5583878180c19f2683060d54b83060c197065d79b8dca0c183060cb97060c1c3c7caaa8f43aa8b0580cb978bc4f01cf2e7cba83060d554197060d060c1f7065c19783c9cdd273740e072aaaaa8f43aaaa8783c5c5c171700c1c0cbd54aa5c3872e9c99f13933e03060c1a7071f4f2ac5cbcf70603069c187264f060cb9b45073e7838d9b94197070f1f00aaaaa2c16170b85cb9f9e5cb97264c2e172e5cb83061c1832ebe0ebe072f95060cb830743c78f1f4aaaaaaaaaaa1e0f038bd545c5c17170aa5c3872e0cf838faf8b933e132e2ac5cbc0c1835707939b939b93a70e1c3874fdd50e1d55878395555555543c1e4f27aa93c9e553e1c39f4e7d39f8fa7939f4e7d563e9e4183060c19783c0e07172e5c1832f43c78f1f4aaaaaaaaaa1e0f0381d545c5c17170aa5c3872e0c183071f4f17265c2e4cb8ab172f03060c1835f2f818381af9fd34e1df874ead0f1e0c1d2aaaaaaaaaad0381d549c5c3f170aa8d183060c1c8d7c9c9a31393462ac8e 24 16777215 10 1023
def hc_63_12 : Nat → Nat := unpackHintV5 0xbd1daebb4c74b5f955aecdcba95d5ca02a4d9971ae9229d28dc11a88854f8181c17da8f6768dc76d2a5966a9a061d9345946255279b34e0d1b44aa5940acff3b714f346dc12d51c727298a2334fd197e6e14cd2c0fb5460b21250748f60001d2 0x7cb8070f97060c183064c19f0e1cfa7369e4e6d3c0c18306aaa8a0aaaa1c0e271609c5803018cc662213038a0a00c180c984c2622001702e0e818381c882c16133e887c98f01e5c3872e4cd9b264c993264c9a7060c183a371381830703bba22a8b0582c16133ea4c993099f053e4c78f00e0f1e7c187064c183264c1833e1c39f26bc9c4c99381b306aaa8a0aaaa1c0e131604c5803198cc66221326070faa0c26130988a807c2623d061c1aa0d50e1d595060d0ef755555506aa1c3870ea88b4061c1870eaa7c3873ea8a033e0cf9f550e7c383061c383060c183060c18706a870e1c3a75ede6ebd3c0c183060d555555555543870e1c3870e070e1c060c383060c3870e1d543870e1cf933e1f267c060c1833e0cf9f3e7d543870e1c387a0e1c3c0cd83060c183555a0f078183419b9555555555438780e1e03c1e0703aa954f93361f266c0e1c387060c1838d9b9560e1ea0e1c3870f07061c19b5e0c1af060c3c1c38795071b9555555555543c1e0e1e038780707a83d07550e1c387364cd86c99b019b3e0e366e5583878187060eaaaa4f776a83d4aaad4aaaaaaaab555555450aa1c3870e7cf9f3f55547e55aaa0e1ea8183060c183555aa555a9a5543aaaaaaaad5545455552a870e1c39f267c3e4cf80c1830754ab54a1d41aaa83060c18306caad5503bbd52caaaab507a83d40ea955543bdd555555559152aaaaaaa2a1553e8a81c3870e0c1830755511f855aa0e1c387a83870e1d565060c1c0eee0d550ef755550f078381c3e7cf9f26130183060c3870e1c3870e1d69543c1e074d0306aaaaaa1deeaaaaaaaa1e0f0381c1c3c070f154aa1c3870e0c183067c99f0f933e47cfcab070f287536bd555543870e1c3870e1d06aa83060c183a936aac1e0f03060c183a81ddd55543bdd555555550e8a81e0f070f01c3c0381d54aa9f4540e1c3873e7cf87cf9f0183060e3e7e558387943aaa830e0c38355583870e1c18355550ef7555543a2a070e1c3830e1c1870e1c3aaa7d1503870e1c19f3e0cf9f3e7d543870e1c18345060c1835060c18300f977f3f8bb37e5d506aaaa2c16170b85cb972e5c9930b85cfbf2e5c183060c18354183060c183060cb870e5c183060cbaf7f3f5e5e5555541aaaaaa870e1c383060c197161c2e2c385c3970eaa5c3872e0c183065c99f09970fbf3eaa1cb970e0c18306aab40c183060c18306d07a0703838755555555555550f0781c0e562e158b8aa553e1c39f060c183564cf8ac99f23ebe558faba090e97549a4d5269b060c18341870386d6555506f7160b05884cf93269326281f267c9d4a8754baaaad554babc183060c183060c183060d41c1eee1c3d070e1d36aac0e072aaaaaaaaa837baa8783cac5c2b1708b4540703aa954f870e7d5ab3e2b3e2fd150183060e3ebe558fab8183060eaa9aaa81d3faa5541aaaaaaad55555552a83060c1973e7cbd5552ad503060c1a870eab40c1d54d552aad2aaaa0d555556aaaaa2a2a9543870e1c183060cf933e1f267caa55aa543a1d50e83060c1a8383ddea9955aaa0f2caaaab503a81d54aaaaaa0deeaaaaab54c8a955555150aa1c3870e9f454060c183aaa88fc2ad503060c1ad2a83060c183060c187a681c0e565d555555541bdd5555543c1e0703838780e1e2a9543870e1c183060cf933e1f267c8f9f9560e1ea0e1d50ea87543aa1c183060c183060d418783c1e64daab0381caaaaaaaa0deeaa1c3870e1c3870e9f454060c1838f9f95550ea87060c1835074ccaad54aaaaaa0deeaa00000000000000000000000000152aa1d0eaa87550ea87060c183060c183060c1835061c3ab0e1ea0f774daab0381caaaaaaaaaa0deeaa1c38780e1e0e0783c874540703aa95439f0e070e1c0e1c3874fa2a03060c1c7cfcab070f03060c1d55545eeed540eef52aab52aa0d5555595eed55555552a83060c1972e5cbd5552ad503060c1aaaab2f40c1d554d52aad2aaaaaaaaad5555454552a9f0e1cf83060c1ab267c564cf954ab549c18306aaa5deeaab354d52ab2aaaa8f7baaab5554cab54aa7c3873e9cfa73ea755aa55aa43a5d072c4c0fa4c9aaaa4dd83060c1c12a837baac244133e4d054060ea96950e8754ba0c18306a0eaa0f776556aa95cb2aaaad40e07503aaa55555506f7555647aaad5322a555554542a9f0e1cfacd150183060eaaa2855aa 24 16777215 10 1023
def hc_63_13 : Nat → Nat := unpackHintV5 0xc8053abe9a5bb48685b43414ad5db6a0db2198f5f9908e1a87764681498b7d250971170468f6086052295b0952569d1b4c8a85482d1740e5d23a1db23519413011422971a824594620d4e119c1c5164cdd0f81b30f3c110e1c48094536000251 0x753a1d0e83068390e1d54387438f541d03361d81a0e0728747a8350e8f551ea070381c43e070f86d3a7369d3ab53aa1d51e8f060c183a9506ca6e3703060d5906a0c1d40eeeaa8f47a3d5555506aa8f568daba369e9511680e07552aa7369cd9b4e6d19b4e6d1aa29d0183060e366e558d9b8d970e1c387365c59b0e1c387162c00183060eaa0aaaa81d415503aabb870e3cdab1e3cd9b1e3c5a2c78b458b060c183aa85911142e1610ba28191510b2236070d9b0366c058b0166c0180c881e1b080585c0985cd970e1cd872e0c1c40cd9b0e1c3806cd9b265c983a066cd8301c0e070f1e8f47a3d1e2c160b0587cd9b360c1933604c986cd8f1e6cd9b366cf9b366cd9b261cd8726000c18307550038183371b8183060c18030740c1d40eee9c79f1e6d38f1e6cd8f1e4d1e3cda3c783060c1c3cdc6c361b3606cd8131606c5803019103c36130986c362f266c9930266cd8301830641b266c1e3c260f0361b0993260c183060c183018302f078b9782e6c01c0e2e1c38f2e8f1e5d1e3c183060e1e6e0e070b8b02e2c0180c881e170993039309930264c0180c8260f098004c987261c993060c183a007030dc6e060c018380703879f1e4d1e3c9a3c783060c1c3cdccc3e131604c5803019103c661326130993260c060c190bc993078f0983c0261b366cf9b366cf83060c1d46e3703060c183a81ddcf8f3e3cda31e3cd9b1e3c183060e1e6e0000000000000f8000006c5e000c003603c000003e00700d84c060404003007808000000bc3af0e0c1830752f97c0c183060ea07771e3d1e3d7a3c783060c1c3d7d42e178b80703aa87d2f1780c183072f5f0fb63e83a0e81aaaf8e8306aa0c1a0e07070ec6d2e5c1830ef7555541a070381c43e1309887418306aaa3c7a8306aa0c183ee0c38306aa0c1a835061c1872e1c3870eaca972e5e2e5e060c18343bdd555547a3d5555506aa1c3870ea88740e1c381c3870183060c3870e1d543970e1c387544fa172e5c2e7cb80c183067cf9f3eaa1c3870e0c183ee83060c1a820c1a83060d3a74e9c3870e1cb972e5d5506aaa8f57baaa1c3870e1c3870e1c3870e1c3870eaa7cf9f3e1c3870e5cb972e7cf9f3eaa1c3870e0c18f1e0c18306a83060c18396bd3c9d7cb8387960c18306aaaa835555eeaa0d5698b0e27161c0e1c387060c183961f187554e4cf89c99f0f870e7c183060e59f3eaa1cf87061c1838e5dd8f1e3c78f1e3c78fa50e0c183060cdc6e0f770f070eaa835557ba0c381c0e070984c2e1f01c0e4ebf553a9d50e97061c1a0c1a0e0f31b41a75547a3c3bdd55061c0e2070984c43e21da955478f5a550e5c1870e0d506a972e0c197060e0f770e1e95694daf50e1c38397c877baaaaa8f47aaaaaa0d543c1e5443a070f01c3c0383d54aa1c3870ea89f42e5cb85cf97019f3e0e3e7e55838783a1c18306aa9dfa9d3aa1c1aa0c1ab54d35541deeaaaa8f47aa834888a43e130980cfa1d0e0c383541b2d6aa0f7755a596aa0f2aad2c3d56075554877baaaaaa83555647aaad52a32555554542a870e1c3aa27d019f3e0eaaa23f0ab549cbd079397060c183066c19b83cb4aa0c1a0cdcaaaaaaaaaaa1e0f271709c5c0381d54aa7c387369c99b13933603060c1c6cdcab1b3741e0ebcbb71e3c78f1e3c78f1e0c183060c18307dc3830e0d43872f1b955554381c0e070984c2e1f283f7bbddd5e0cd830e0c38397d07aa9557baf755555aaaaaaaa55366cd9b0e1c387066cf83aa55aaa1e3c3c3c7af060cdaf060c18706a9b5f0781c6e55555555555362e0d8b80f0781d552a9b266c364cd87c387360cd838d9b956366ea1e3ea9541835060c1835a55aa9a5555555555a8a8aaaaaa557e4cf8fc99f0f870e7c183060ea956a87a8306b4930e1cbaa934e9326a80c19041deeaa835548884260307548f4183060d506835aa566581ddeaa2f507a555a59560754877baaaaaa83555647aaad52a32555554542a9f0e1cfaa2cd0183060eaaa2855aa4e1c3c3a1e1c38f55941830703bb8355555564f0b0589cfa73e4c2603060c18f1e1c3870e3c7ad2aaf83c0e6060d555555555555543c1e0703a38b8862e2a954f870e7c183060e3933e43267c8faf9563f1e4505a6d459b4efdd1e0b858f4b870e4d54993499b55060d88636830181deeaaaa834160b0584cfa824c984c983067c9a9f268f53970e1c387865d5554daf55060c183541a0d6a5f0795936a0c183060ea077743bdd555555547a3d5506aa1e0f2a22d05c271700e07552a9f0e1cfaa289cf89cf80c183071f5f2ac7e 24 16777215 10 1023
def hc_63_14 : Nat → Nat := unpackHintV5 0xcf2f1ac7020bbed20cb7fdb5b10dbcaba959a2425a9cbd619a08ad91921e87aa7a8109a87a49b07399ac6c99c066a97c5ffdab5b412f5451bc4e617c48358b43b1213bd1f832a24c251f6123ac5c22b83d21904a1b81840e8b3e09155d000245 0x1401c397aa002e0c383366c18326ec1832e6c18336ec18383ddc387a361e838700e1c3838dc5c3871e6d1e3c9a3c797363c79b763c7831eac1c3cdc1c0e171604c58173605cd8030b9103c2e132e070b932e5c997264c02e1f061320d93360f09805c2e1b2e01c365c183060c193060e0f1b3706cd803a0747c3871e6d1e3cda3c783060c1c3cdc1c0e1b1606c5803019103c36130384c98030600c180c9906c9930784c00a00e138f830e0c983064c983066e0f130f01c38038dc7c3871e4d1e3c9a3c7831e0e1e6e0e07098b0262c018cc881e3309930387c993260c2641f264c1e1300f84ca818706bc183060e0f770e1e83870e0e5f070e3d7a3c7a3c7831e0e1ebe0f07978b81700eaa87d1f0e1cfaf3e1f019f071f5f0f3e3e3f03060c1870e0c183060c187075555555555070e1c3a7478f4e8f1e0c18307555551515555541c3870e7c99f0f933e03060c1d50f3e7c7d507061c1c1eef555507a0755541c3870e0c783aa987cd555555545455070e1c3833e7c1d55447e079f3e3ea8183a0703060c183061c1830e0c3c0e4ebe8183a060e06be0e1c3874e8f1e9d1e3c1831e0c18387af83c1e0e1e038780703aa83c1e0e1c3873e4cf87c99f01833e0c1838f9f879f3e3e0e1ea0e1c3830e0c3830e0c3c1e0f0781cbe0e1c3870e1c387063c1c3d7c1c3870e1c3870e0cf9f071f3f0f3e7c787061c1d555070e1c3831e0ea8000000000000000002a0e0c1870e0c187061c1870e1c3d41eee0e5f0743870e871e1c3870e0c78387af83870f01c3c1c0f0781c1eaa0f07839f0e070e1c0e1c387067cf838f9f879f3e3e0e1e060c183060fb830e0c1830e0eaa0f77aaa8bd7eaaa0f45e5f550381d540e07503aaa0e1c3872e8f1e5d1e3c183060eaa61f3555515155555151541c3870e5cb970b9f2e03060c1d55447e079f3e3ea8183aaa065c1830e0e060eaaaaaaaa93a3c7a7478f0e1c387060c183aaa8a8aaaaaaaa3e4cd87c99b03870e1c183060ea879b3e3eaaa0e0c3832ebc1835e0c1d5de0f507aa83870e1cba3c7ab478f063d583aaaaa8a8aaaaaa0e1c3872e4cd86c997019b3e0ea879b3e3ea81830703060fb83060c1d100c1d5555517aaa0e1c3872e8f2e8f4e3d38faaaaaaaaaaaaa0e1c3872e5cb973e5cf9f3e7ea879f3e3ea93af060c183060c183060c1d55555555541c38f4e8f1e9d1e3c183060c1d555545455555551f0e1cfa7267c4e4cf80c183060ea879f4e3ea8183060eaaa8f9700e1f2e0c193a08a3e1c38f060c183aa4e8f1e9d1e3e222222828220981c060c064c88a0a01e13000f830e0eaaa899300e133e0c193264c183a08a3e1c38f063c1d513478f268f1f1111114141104c981c3e0c3e4c9944550f0f9326044030e0eaa0f77aaa81d555070e3c18f075530f9aaaaaaaa8a8aa3e1c39f067c1d554503cf8faaa8183060c183060c183060c183aaaaaaaaa2e1c38f2e8f1ead1e3c183060eaaaaa2a2aaaaa8b870e5cb933e3b265c060c183aa1e7d58faa060c183aaaa264c9830183060c28228b870e3c183060ea8ba3c797478f888888a0a088264c0e4c06032228280784c00060c183aaaa264c987261c9830183060c2822879f1e0c18307544d1e3c9a3c7c44444505044130980c060c1944550f098000c183075503bbd55507a81d50f1e0c183075530f9aaaaaaaa8a8aa060c183aaa8a078faa2ebc183060c1af060e0f1b5ebc1c0e2e1c38f2e8f1e9d1e3c183060e1e6e0f078b8b82e2e01c0eaa1f178b870e5cb93361b265c060c1838d9b879b4e3e2e5e060c183060c3872e0c1d0381830e5e0e1e07038183a060e83870e1c38f060c1832e8f1e5d1e3e1e6e0f0781c0e0e1e03878aa0f0783870e1c183060cb932e17265c8d9b879b3e3e0e1e0e1cdaf0e1c3870e1c183060c183a83870e1d787060e81c0c18737070f03060c183a81ddc183a060e83870e1c38f4e3c79b5e3c783060c187438f0e870f0f370783c1c3d070f40e07070f01c3c550783c1c3870e6cf9b3e6cf9b3e0c183061c387039f0e46cdc3cd9f1f070f174e1c7a3d1e1c7f71e8f47970e1ca0e77170b8b9b0e1b3e1cee7c99b2e1c383a2606c3870e013264cd933e0c183060c18381ddcdc4e4e3cd8f47a3cb85c160b099b264c984cd87c993364cd93365cdaf0e1c38736bc183060c183a8d9b361c3870e0c1d038183366e0e6e060c18307503bb830740c1d430e3c38f1e9d58f1e6d58f1e0c183070d1e3d1e3e1e6e0f078d97a365e81c0e862e05c550fa3e1c39b366cf9b5e6cf83060c1c3361b2366e1e6d38f8d9b81832e072e0c183065cb83818300b9b371b81c0e1e3d1e8f2e3d58f160b0b85c2e5cb972e4c985c2e7d5972e0c183060c1975ebc183a0703065d7c1d7c0e07030740c1d170e3c38f1e0c183065d1e3d5a3c7c3d5c1e0f0381c5c5c17171543e2f170e1cb83060c197267c265c8faf879f563e2e5e 24 16777215 10 1023
def hc_63_15 : Nat → Nat := unpackHintV5 0x86a7184047c31f5eb14f1626571efb0b6c28d5a93b36cbae3c61ab0b2e13b095955d2a4fdeb4ce167a34cc9109544478431a3543b79857928b35bd850325f2598a0102aa88640f522483610e070e84e188813d4ce00027a 0x30e0c183060c180c818307de065c183060e2e5cb9bef0381c0e07171e3cb8f1e0c183065c7971f0f4f178bc0e07178bd543e2f172e5cb83060c1972e5cbc7d3c3cfa71f172f03060cb972f540c183ee0c383060c383065c18383d178b9736be8b976e0e07170e1c7972e3c7974e3c797478f2e8f1e0c183070f4f0783c5cbd172f45c5c171700e07550f8bc5c3872e5cb97365d3972e5cb970ba72e03060c1c7d3c3cfa71f172f172e5e060fbf7061c1f7065c1d545ebf545c3871e5c7971e0c183075555555555545c3872e5cb972e0c18307543cfa71f540c183060c1f7061c183061c1c5eaa2f5555503a07507a9bcbe07503aa8b870e3cbcb1e3d3b71e3c183060eaa61f3555555555555151545c3872e5d99f3e9d9973e0c1830755513781e7d38faa060e8183060c18307540c183ee0c383060c183060c1d030e0cb9781c5cb972e5cb9b5f517af83818307170e1c7ab478f568f1e5e58f1e9db8f1e0c183070f570783c5c5c171705e5d176f40e07550f8bc5c3872eddb9f17b73e176e7cda76e5cd83060c1c7d7c3cfa71f172f030740e060c183060c18307030746d7c0ebe6d7af0703060e0e1c7af478f368f1e0c183070f370783c6c5c1b1700e07550fa3e1c39b364cd86c99b0183060e366e1e6ed8f8d9b8183aa0a060c1f7065c183061c1d555778bd55171e5c7971e5c783060c1d55555555555172e5cb972e5cb83060c1d50f3e9c7d503060c18307dc187060c187075555517afd545e8bcbe07545c3871e5cb8f1e5d38f1e0c183075530f9aaaaaaaaaaaa8a8aa2e1c3972e5cb9f2e9cb97060c183aaa893c0f3e9c7d5030e0d418344418307dd063c1832e5df972e5c183060cb972e5d51eaf755506aaaa5c3970e0c183065c3970e5c3970eaa5cb972e0c183065cb972e9cfa73eaa1cb970e0c1834ba8f4783060fb830e0c1830e0d41970e1cb972e5e597965cbab32d4183060d551e8f555555506aa1c3870e5cb870e5cb870ea88b4060c1832e1cb87552e1c3972e5cb9f2e9cb975453a03060c1a73e9cfaa872e5c3aa1d5060c18351e3c18307dc187060d06aa83061c1970e1cba9d558ba74edd3b72e9c183060d551eaaaaa3d1ea0d5550e1c38745a2a174e1c397561c383060c1970e5c3aa970e1cba9d150ba73e7d3a72e7c183060d39f4e7d543972e1c187060c183060c0600c183ee030e0c1978bc0e07178bc5c7971e0c183065c7971f0f4f0306070e2c3f70180c0603220381c2e170180c2e1721383c4e0003060c38716000c183ee0c383060c383061c1870f078b97a2f2e858ba172e81c0e0e1c3872e5c78f2e9c78f168b1e2d162c183060e1e9e060700e070e2c38b00e2c383019101c0e070385cb8174e02c580b4e00c064270789c00060c0183060c18306000c183ee0c383060c183060c18030e0c3c1e178e858ba2e5e8bb7a070383870e1c5a2c58b458f2e5c78f2eac78f060c18387ab83870181c38b0e1c58716007038301830644070381c0e0b6e02c58172e05d98030190dc1e2700e02c061c183060c18301803060fb80cb83065cb972e0c183065cb972e5c7971e0c183065c7971e9c7a71e5c2e030185c2e170b83c2e030617265c9f70180c06030984c1e13000183065cb9700060c1f7061c183061c1832e0cf970e1cb972e5d9976e5cb932e5e2edc9c0c183065c3871e5cb8f1e5d38f1e4d1e3cba3c783060c1a71e9c7870385cb8172e04c58171600c06170b83c2e03038170f932e4c98132e7c180c26130784c00060c0183060c18306000c183ee0c383060c183060c18030e0cb870e5d3a727136e9e2e9d3b34edcba7060c1832e1c38f4e8f1e4d1e3cba71e3d3a71e3c183060d38f4e3c381c2e2c098b02e9c0bb3006030b85c1e1709970185c9972e4cb93260170f83018306130983c260170b80c18030183060c183060c180c181f0e1cf935e4e264c9c0c183067c3871e4d1e3c9a3c783060c1b31e3c381c262c098b00603198cc1e3309930187c993260c060c184c260f09807c2603060c18307dc187060c187061c3d03060c1870e3d1e3d1e3c183060c78f0e1c387161c161c060c1830e1c7870e7c3873e7c3e03060c19f3e3cf8f0e7c3830740c1838183a060c1c0c183061c38707070e1e0703060e368f1ebd1e3c3870e1c183060e1e6e0e1e038780f0781c0ea0f41c3c1e364cd86c99b03870e1c183060e367cdc7c79b3e3e0e1e5555060c183550e1c387060c183550e1c387060c1830e1c387550e1c387060c1833e7cf9f0e1c387060c1830e0c187060c18307dc38783870f070e1c383060c1870e870e1d0e1c78f0e1c387060c1831e3c3870e070e1c0e1c387060c1830e1c3870e1c3870e7c381c38703870e1c183060cf9f3e7c79f3e3c3870e1ea060c183060c1d50381c0c183060c183ee0c383060c183060c1832e0c183061c1c1eee1c3d070e1c1838bd172e6d7d0381c1cb870e1c397478f2e8f1e5d1e3cba3c783060c1c3d5c1c3c1c3c1c3c070f01c3c070f00e07550783c1c3870e5cb970b9f2e172e5c2e7cb80c183071f3f0f3e7c7c1c3c0c1d03060e060c183a8197060cb83060c1832e0d783060c183060c1d070f507bb870f41c387060e066e568f1ead1e3cb870e3cbaf1e3d5bb1e3c183060e1e6e2e2e0b8b80f078bafa2eee81c0eaa1f179dbb363b766c2e1c3972ebcd9f36ecb9f060c1838d9b879b563e2e5e060c1f78183060c1c103060c183060c1c1e070781838b972e6fbc9c7a71e1c3870e5c7971f0f4f0783c1e0f0783d541e0f1f3e7cf870e1c3972e5cbc7cfc3cf9f1f070f030740c18381af060c183060c183a0e1e81c1e060e06be4e8f1e9d1e3c3871e0c183070f5f3f1709c5c0783c0e07550fa4e4cf89c99f0f870e7c183060e3ebe1e7d38f8fca8756a9478f2e0c3835faaa0cbab060d5bb060e0f770e1e90eaac1c387071b9551eaaaaa3d1eaaa3d50f079168a85d5d175740e2f552a970e1cbaed150bab367cdbb2e7c19b760e366e558b97a82aaa000e0c383166c183162c1832e5c1832eec183abbc1eaaa820f55070e1c38b458b168b1e5cb8f1e5d58f1e0c7ab0755072285d0b858114445444070382cd80b1605cb8173600c36440f0d8402c 25 33554431 10 1023
def nh_63 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_63_15 (Nat.sub p 480)) (hc_63_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (hc_63_13 (Nat.sub p 416)) (hc_63_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 448)) (Bool.rec (Bool.rec (hc_63_11 (Nat.sub p 352)) (hc_63_10 (Nat.sub p 320)) (Nat.blt p 352)) (Bool.rec (hc_63_9 (Nat.sub p 288)) (hc_63_8 (Nat.sub p 256)) (Nat.blt p 288)) (Nat.blt p 320)) (Nat.blt p 384)) (Bool.rec (Bool.rec (Bool.rec (hc_63_7 (Nat.sub p 224)) (hc_63_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (hc_63_5 (Nat.sub p 160)) (hc_63_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (hc_63_3 (Nat.sub p 96)) (hc_63_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_63_1 (Nat.sub p 32)) (hc_63_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 256)
def f_63 : Nat → Nat × Nat := unpackForestF 0xfd57cf4b5ffc46cf4b5bf4b57f4b55fa37cf4b53f957cf4a5ff4a57f7d7cf495ff4957f657cf485ff4857f485500c5ff336df326c00c57ee46fee457f145eee455ee257ee157ee057eec5dee05500b5fed35600b5beb46deb16ceb16000b57e756fe9c55e736ee8c6ee7356e7b5ae703500b53e536ee5b62e503500b4bdb56ee3c6cdb56be1247e1147e1047e1045db563e0047db562df67adb25fdb15fdd846dd672db05fdc56edb05ddb05300b47da355cdc6fd945ecdc55d7c65d7c55cdb6fd6b56cdb63d4c6dd4c5fd4b52cdb55d3364d3035cdb4bd0569d0568d1678d015fd005dcdb47ce45dced60ce347cd85500a5fc8c6dcc455c8b6dcad7ccab7cc8b4bc9571c9570c8b4700a57c7847bdd62c6568c6065bdb6fc4e70c4b6cbdb6bc2d70c297cc2970bdb67c0670c036cc0354c0035bdb63bf46ebdb5dbe56ebd85d00a47bcb64b756fbbb7cb7567bac55b736eb9d6eb7356b7d6fb7b62b7b5ab703500a3fb5c68b5865add6fb4c70add67b386db1b57b1b56b2366b1837adc62b056eb0362adc5aae56fae46eae456ad84d00a37aca5faa347abb5daa247aac5aaa2370095fa916ca8357a81560095b9f46da6c559f36da3571a4a4fa4a47a3570a3e80a325f9f347a1d70a1b5d9f2479fd7d9fc709fc5a9f237009579e16c9b3579d2459b1569b0189ba479b014009530094b993479904791562985689136f9746e9135d95568953659535d9126f944609123791d6e91b6f91a6f91a379105d00947903648756f8f4558736e8d56e8d5638d562873568bb648bb568726f8ab6c8725787d6f87b6287b5a87a6f87a57870350093f8616c85357851560093b8356f8326f83257009378216c80b578095680934009337f2567f1560092b7dc657db686cd6f7c5657c3686cc6f7b358796737a67279362793606cc577826c74c5774a5774a567626674a4775266748276cb6272d6e72c6f72a626cb5a70d6f70a6e70a566cb4a6c95a6d56f6d46f6d4576d36e6d3566c83d009276434b6ad616a85e6434769b5d6424768b566423f67c5a6423764147663566413f6413764b5a641270085f630446045b6206c604576005660c5a600460085b5546d5ec555536d5d57c5d37c5534b5b5715ba4f5b5705534759d7059b5d552475837c583565523f55d7d56b5b55c7055c5a5523700857540444d45b5296c5286c4d45751b454d0565045a5035a4d0464d02c4db4b4e05c4db474d024008534c0460084b3756e4ab45375634934b4934737562485683736f46b6c46b54373633735f44c6e44b623735d3735342568423654235d3726f3725f3fb7e3fb6c3fb543723f3ec583d6733d4723d460372373716f3715f3a37e3a36c3a27f3713f3927f3713737b7237b603712700847363642fd6f354552fb6e3356e33563335622fb5631b6431b562fa6f306723036c2fa570083f2e85e2b9562b8562d45a2b8462b82c2b8240083b2ac681656f29c551646e28b66164632735727356164621645b24d6e24b6e24b621645a23d621645621565214682145a214561626f20460162571624f1e45a1e2571616f1c6721c4601c27f161571614f18e7f18d6a18b7218b6a18b50161271784e1605a1696f16056008371505600833140441245b1205612c5a120460082b0d56f0d46f0d4630d45b0d4570d16f0d1570d14f0d147008270c16c0b3570b1560081f0996c0986c07c57078560845a078460081b0256f065650246f0245704565044570236f0235702d6a023470081701056008130003f 9 11
def ch_63 : Nat → Bool := dagCheckNodeV5 fullMask g_63 ep_63 5 31 bds_63 507 (dagTraceF fullMask rootStock 11 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 fullMask g_63 ep_63 5 31 507 bds_63 (dagTraceF fullMask rootStock 11 f_63) (cur_63 0) (nh_63 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 64 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_2 : treeBlockF 64 96 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_3 : treeBlockF 96 128 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_4 : treeBlockF 128 160 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_5 : treeBlockF 160 192 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_6 : treeBlockF 192 224 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_7 : treeBlockF 224 256 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_8 : treeBlockF 256 288 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_9 : treeBlockF 288 320 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_10 : treeBlockF 320 352 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_11 : treeBlockF 352 384 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_12 : treeBlockF 384 416 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_13 : treeBlockF 416 448 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_14 : treeBlockF 448 480 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_15 : treeBlockF 480 507 ch_63 = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 64 → ch_63 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nj_63_2 : ∀ i, 0 ≤ i → i < 96 → ch_63 i = true := block_join nj_63_1 (fun _ h1 h2 => treeBlockF_at nb_63_2 h1 h2)
theorem nj_63_3 : ∀ i, 0 ≤ i → i < 128 → ch_63 i = true := block_join nj_63_2 (fun _ h1 h2 => treeBlockF_at nb_63_3 h1 h2)
theorem nj_63_4 : ∀ i, 0 ≤ i → i < 160 → ch_63 i = true := block_join nj_63_3 (fun _ h1 h2 => treeBlockF_at nb_63_4 h1 h2)
theorem nj_63_5 : ∀ i, 0 ≤ i → i < 192 → ch_63 i = true := block_join nj_63_4 (fun _ h1 h2 => treeBlockF_at nb_63_5 h1 h2)
theorem nj_63_6 : ∀ i, 0 ≤ i → i < 224 → ch_63 i = true := block_join nj_63_5 (fun _ h1 h2 => treeBlockF_at nb_63_6 h1 h2)
theorem nj_63_7 : ∀ i, 0 ≤ i → i < 256 → ch_63 i = true := block_join nj_63_6 (fun _ h1 h2 => treeBlockF_at nb_63_7 h1 h2)
theorem nj_63_8 : ∀ i, 0 ≤ i → i < 288 → ch_63 i = true := block_join nj_63_7 (fun _ h1 h2 => treeBlockF_at nb_63_8 h1 h2)
theorem nj_63_9 : ∀ i, 0 ≤ i → i < 320 → ch_63 i = true := block_join nj_63_8 (fun _ h1 h2 => treeBlockF_at nb_63_9 h1 h2)
theorem nj_63_10 : ∀ i, 0 ≤ i → i < 352 → ch_63 i = true := block_join nj_63_9 (fun _ h1 h2 => treeBlockF_at nb_63_10 h1 h2)
theorem nj_63_11 : ∀ i, 0 ≤ i → i < 384 → ch_63 i = true := block_join nj_63_10 (fun _ h1 h2 => treeBlockF_at nb_63_11 h1 h2)
theorem nj_63_12 : ∀ i, 0 ≤ i → i < 416 → ch_63 i = true := block_join nj_63_11 (fun _ h1 h2 => treeBlockF_at nb_63_12 h1 h2)
theorem nj_63_13 : ∀ i, 0 ≤ i → i < 448 → ch_63 i = true := block_join nj_63_12 (fun _ h1 h2 => treeBlockF_at nb_63_13 h1 h2)
theorem nj_63_14 : ∀ i, 0 ≤ i → i < 480 → ch_63 i = true := block_join nj_63_13 (fun _ h1 h2 => treeBlockF_at nb_63_14 h1 h2)
theorem nj_63_15 : ∀ i, 0 ≤ i → i < 507 → ch_63 i = true := block_join nj_63_14 (fun _ h1 h2 => treeBlockF_at nb_63_15 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 507 → ch_63 i = true := nj_63_15
theorem lb_63 : LowerBin fullMask rootStock g_63 12 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_59 (kn_cons lb_50 (kn_cons lb_58 (kn_cons lb_32 (kn_cons lb_62 (kn_cons lb_57 (kn_cons lb_61 (kn_cons lb_38 (kn_cons lb_2 (kn_cons lb_29 (kn_cons lb_22 (kn_cons lb_3 (kn_cons lb_11 (kn_cons lb_60 (kn_cons lb_1 (kn_cons lb_5 (kn_cons lb_6 (kn_cons lb_18 (kn_cons lb_54 (kn_cons lb_4 (kn_cons lb_30 (kn_cons lb_53 (kn_cons lb_42 (kn_cons lb_9 (kn_cons lb_19 (kn_cons lb_28 (kn_cons lb_15 (kn_cons lb_13 (kn_cons lb_51 (kn_cons lb_52 (kn_cons lb_24 (kn_nil))))))))))))))))))))))))))))))))) rc_63 nc_63 (by decide +kernel)

def wg : List Gate := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.and, [7, 16]⟩, ⟨GateOp.or, [13, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3934838912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3934838912)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3934838912) = g_63 by decide]
  exact lb_63

end PEqualNP.Outside.L_meta_48645

theorem PEqualNP.Outside.L_meta_48645 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3934838912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3934838912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48645.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3934838912) 13 PEqualNP.Outside.L_meta_48645.root_lb PEqualNP.Outside.L_meta_48645.wg 18 rfl PEqualNP.Outside.L_meta_48645.wfits PEqualNP.Outside.L_meta_48645.weval
