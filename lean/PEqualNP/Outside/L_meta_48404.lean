import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48404

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

def m_0 : Nat := 0x5500550000000000
def s_0 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_0 : Nat := 0x100150000000000
def ep_0 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_1 : Nat := 0x4444444400000000
def s_1 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_1 : Nat := 0x4044400000000
def ep_1 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_2 : Nat := 0xf0f0
def s_2 : List Nat := [0x5050, 0x3030, 0xf0]
def g_2 : Nat := 0x1070
def ep_2 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_3 : Nat := 0x5050505000000000
def s_3 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_3 : Nat := 0x10105000000000
def ep_3 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_4 : Nat := 0x5555000000000000
def s_4 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_4 : Nat := 0x115000000000000
def ep_4 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_5 : Nat := 0x222200002222
def s_5 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_5 : Nat := 0x200000222
def ep_5 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_6 : Nat := 0xaa000000aa
def s_6 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_6 : Nat := 0x20000002a
def ep_6 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_7 : Nat := 0xcc00cc
def s_7 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_7 : Nat := 0x4004c
def ep_7 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
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

def m_8 : Nat := 0xa000a000a000a
def s_8 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_8 : Nat := 0x20002000a
def ep_8 : Nat := 0x2000800000002000000080000000000000000000000000000000000000002000200000000000000000000
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

def m_9 : Nat := 0x3300000033000000
def s_9 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_9 : Nat := 0x100000013000000
def ep_9 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_10 : Nat := 0x44444444
def s_10 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_10 : Nat := 0x40444
def ep_10 : Nat := 0x4400000000000040040000000000004040000000000000000000000000000000000
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

def m_11 : Nat := 0x3030000030300000
def s_11 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_11 : Nat := 0x10000010300000
def ep_11 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
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

def m_12 : Nat := 0xf00f0000f00f0000
def s_12 : List Nat := [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000]
def g_12 : Nat := 0x5000010070000
def ep_12 : Nat := 0x1002000000000000000000000000000000000000000000000000000000000000100200000005000010040000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_12 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_12 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 7 (dagTraceF m_12 s_12 4 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 7 bds_12 (dagTraceF m_12 s_12 4 f_12) (cur_12 0) (nh_12 0) s_12 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 7 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 7 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 5 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0xcc330000cc33
def s_13 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_13 : Nat := 0x41300000c33
def ep_13 : Nat := 0x820000000000000000000000000000000000000040200000c0000000000000000000000041000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def nh_13 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_13 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 7 (dagTraceF m_13 s_13 4 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 7 bds_13 (dagTraceF m_13 s_13 4 f_13) (cur_13 0) (nh_13 0) s_13 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 7 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 7 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0x3c003c003c003c00
def s_14 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_14 : Nat := 0x140010001c00
def ep_14 : Nat := 0x100008000000140000000c000000000000000000000000000000000000000000000000000000140010001000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_14 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_14 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 3 (dagTraceF m_14 s_14 4 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 3 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) (nh_14 0) s_14 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 3 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 3 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0x3c3c3c3c
def s_15 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_15 : Nat := 0x10341c3c
def ep_15 : Nat := 0xc080000000000240020000000000000000000000000000000000000000010041000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cc_15_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d07a0686d0198720e40c4388300d65ac148a905209c5382704e0944f99f03e07c0f81f03e07c0d901d001 0x1e4d104747e3634970e4b4e85a7025340e100f078582c2c1c9e17130b088542c28120f0b060283c34160a0c0d05858483d221a900b8705a341d140a8513020880c3c041a498fe34770e378519c14fe0276fd376e99b44bd7a56b1275691aa0fd4876a0374619a20bcd85c642b30139308c4844201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_15_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc2c0b9b8b8b8b18d88816b686868684c48483330303030303030301409080100 0xf52ce414f534e534fa44f13ced34e818e014782cda4cd644743ccd4cc944c418c014b83cb430702c9c3c9834942c902438308414 8 255 3 7 10 1023 16 65535
def cc_15_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x183060c112039468100b1020401 0x9b38993496389434422c91288f24403c8a4c88403e2c7d30 7 127 3 7 9 511 16 65535
def cur_15 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_15_2 (Nat.sub p 64)) (cc_15_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_15_0 p) (Nat.blt p 32)
def hc_15_0 : Nat → Nat := unpackHintV5 0xb40590ac054caa414f1a60d28492147123050c684142020850407e23e09f00f807c0354962494e3891a10b8c5822820f280b8002 0x0 13 8191 5 31
def hc_15_1 : Nat → Nat := unpackHintV5 0xd866a13311904c425e22c194109844b0a3911448243f11e88e0a6c23411810aca4491b389244421e20d1050c14a0430200084002 0x0 13 8191 5 31
def hc_15_2 : Nat → Nat := unpackHintV5 0x4311f90f447623629910c425a42b11488948405155852c014 0x0 13 8191 5 31
def nh_15 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_15_2 (Nat.sub p 64)) (hc_15_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_15_0 p) (Nat.blt p 32)
def f_15 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f1d288e92018ee20991040031b818cc0a7e053b029bb8911ea68e13c709a38061ca68e0140299b5931ac88052f60a6305118030c0140295ad0f1686005270291810fc08760437481e240d1205890240219810bd0828723a391b1e4d0e05a702502171a07008560427282614110a058502402118a0f4506a282e1e1a0a0b4503a2c3416160a0540844041f020d8105c10980844041e020d00826000f 7 10
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 78 (dagTraceF m_15 s_15 5 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 78 bds_15 (dagTraceF m_15 s_15 5 f_15) (cur_15 0) (nh_15 0) s_15 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 32 ch_15 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_1 : treeBlockF 32 64 ch_15 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_2 : treeBlockF 64 78 ch_15 = true := by decide +kernel
theorem nj_15_1 : ∀ i, 0 ≤ i → i < 64 → ch_15 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_15_1 h1 h2)
theorem nj_15_2 : ∀ i, 0 ≤ i → i < 78 → ch_15 i = true := block_join nj_15_1 (fun _ h1 h2 => treeBlockF_at nb_15_2 h1 h2)
theorem nc_15 : ∀ i, 0 ≤ i → i < 78 → ch_15 i = true := nj_15_2
theorem lb_15 : LowerBin m_15 s_15 g_15 6 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xff00ff0000000000
def s_16 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_16 : Nat := 0x100150000000000
def ep_16 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def nh_16 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xffff000000000000
def s_17 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_17 : Nat := 0x115000000000000
def ep_17 : Nat := 0x14000000000000010400000000000001100000000000000115000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_17 : Nat → List (Nat × Nat) := fun _ => []
def nh_17 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 0 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 0 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xffff00000000
def s_18 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_18 : Nat := 0x155700000000
def ep_18 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cc_18_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_18_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_18 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_18_0 p) (Nat.blt p 32)
def hc_18_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_18_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_18_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_18 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_18_2 (Nat.sub p 64)) (hc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_18_0 p) (Nat.blt p 32)
def f_18 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 64 (dagTraceF m_18 s_18 5 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 64 bds_18 (dagTraceF m_18 s_18 5 f_18) (cur_18 0) (nh_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 ch_18 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 ch_18 = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := nj_18_1
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xff00ff00000000
def s_19 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_19 : Nat := 0x15005700000000
def ep_19 : Nat := 0x42000000000000000000000000000400020000000000100002000000000015005400000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_19_0 p) (Nat.blt p 32)
def hc_19_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_19_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_19_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_19 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_19_2 (Nat.sub p 64)) (hc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 64 (dagTraceF m_19 s_19 5 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 64 bds_19 (dagTraceF m_19 s_19 5 f_19) (cur_19 0) (nh_19 0) s_19 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := nj_19_1
theorem lb_19 : LowerBin m_19 s_19 g_19 6 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xf0f0f0f000000000
def s_20 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_20 : Nat := 0x10105000000000
def ep_20 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def nh_20 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xf0f0f0f00000000
def s_21 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_21 : Nat := 0x105050700000000
def ep_21 : Nat := 0x402000000000004000200000000000000000000000001000002000000000105050400000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_21_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_21_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_21 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_21_2 (Nat.sub p 64)) (hc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 64 (dagTraceF m_21 s_21 5 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 64 bds_21 (dagTraceF m_21 s_21 5 f_21) (cur_21 0) (nh_21 0) s_21 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 64 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 6 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xcccccccc00000000
def s_22 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_22 : Nat := 0x4044400000000
def ep_22 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x3333333300000000
def s_23 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_23 : Nat := 0x111111300000000
def ep_23 : Nat := 0x1002000000000010000200000000010000020000000000000000000000000111111000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_23_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_23_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_23 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_23_2 (Nat.sub p 64)) (hc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 64 bds_23 (dagTraceF m_23 s_23 5 f_23) (cur_23 0) (nh_23 0) s_23 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 ch_23 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 64 ch_23 = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 64 → ch_23 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 64 → ch_23 i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 6 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0x5050505050505050
def s_24 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_24 : Nat := 0x10105010101050
def ep_24 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x5555555500000000
def s_25 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_25 : Nat := 0x115155500000000
def ep_25 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_4, s_4, 4, g_4), (m_3, s_3, 4, g_3), (m_1, s_1, 4, g_1)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_25 : Nat → Nat := fun p => Bool.rec (hc_25_1 (Nat.sub p 32)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) (nh_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_4 (kn_cons lb_3 (kn_cons lb_1 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x6666000066660000
def s_26 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_26 : Nat := 0x4000002260000
def ep_26 : Nat := 0x222000000000000000000000004000000240000000400000204000000000000000000000000000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc3706d0da0b41606c0580ac3582b0560a4519a304608c1182304607c8f81f03e07c0f81f03e06c8d801d001 0x3e0e15130929869282e9e148e09a706e393318984e4b262543e241e8ed206e80313c1698069202c80123807184d8fe547716378519c14fdf276e5376c99b54bda256bd275691a60fd007c783b3a1b9c0cc8864402f1e158a09c4846201f0e0d8205c0826000f 11 2047 5 31 10 1023 17 131071
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x8dc6231188c3f1e2f06db61b0d868b4192a550281248940a00f2782a9088040190c00c00 0xc08100187e0a3d931e480ec4c7420170c1c278dd342c202e4c16a40cf4865a02c4818878c0305d182d0816468503026182a8e14c68a1384e9a12100a4788c28271e234a0fc7c4a3d4a952449910548426 9 511 3 7 10 1023 17 131071
def cc_26_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x162c5887020408090c980600000 0x364098289624934c91408e4c8c403430892887243240 7 127 3 7 9 511 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_26_2 (Nat.sub p 64)) (cc_26_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0xda36a1b38d982cc0650b205900c61620b101880c025b2aa1d2d2922480a3090c67c5354971c95246222090087463050f480b8002 0x0 13 8191 5 31
def hc_26_1 : Nat → Nat := unpackHintV5 0xde46d134919c4ca2602af856c8ae44c5a0acfc47643911998ad05222520f9855428112108843c41830c005842c01600a080a4002 0x0 13 8191 5 31
def hc_26_2 : Nat → Nat := unpackHintV5 0x14aa724a4850f91b43245c8929111a825022822004 0x0 11 2047 4 15
def nh_26 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_26_2 (Nat.sub p 64)) (hc_26_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xc7f2c289612018ee329919408c26461000c6f0d288692018cc0a7efc187e0a014edd498ea4074263a1000a6edd3c6e9a014cc0a5e052b61a430d018078c0300293ad8c16840b2340291a78e13c689d384e9a010fd0a5485264694210a9084c043e3e0e010ec086e0433251c9a4a0946249392e9e124c4907c4e38269c120f40864042f02158bd205e802d3c16980109c0846041f020d839201c800e3807180105c0826000f 7 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 78 (dagTraceF m_26 s_26 5 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 78 bds_26 (dagTraceF m_26 s_26 5 f_26) (cur_26 0) (nh_26 0) s_26 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 64 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_2 : treeBlockF 64 78 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 64 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nj_26_2 : ∀ i, 0 ≤ i → i < 78 → ch_26 i = true := block_join nj_26_1 (fun _ h1 h2 => treeBlockF_at nb_26_2 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 78 → ch_26 i = true := nj_26_2
theorem lb_26 : LowerBin m_26 s_26 g_26 6 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x3030303030303030
def s_27 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_27 : Nat := 0x10101010301030
def ep_27 : Nat := 0x1020002000001000000000000010000000200020000000000000000000000000000000000010101010001000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xcccc0000cccc
def s_28 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_28 : Nat := 0x44400000c4c
def ep_28 : Nat := 0x808000000000000000000000040000000400000040000000c0800000000000000000000044400000040
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_28 : Nat → Nat := fun _ => 0
def f_28 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 1 bds_28 (dagTraceF m_28 s_28 3 f_28) (cur_28 0) (nh_28 0) s_28 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 1 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 1 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 4 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x3333000033330000
def s_29 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_29 : Nat := 0x111000013330000
def ep_29 : Nat := 0x1222000000000000000000000010000000200000010000000200000000000000000000000111000010000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xff000000ff00
def s_30 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_30 : Nat := 0x150000001f00
def ep_30 : Nat := 0xa00000000000000000000000000000000000000040000000e0000001000000010000000150000001000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_30 : Nat → Nat := fun _ => 0
def f_30 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 1 bds_30 (dagTraceF m_30 s_30 3 f_30) (cur_30 0) (nh_30 0) s_30 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 1 ch_30 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 1 → ch_30 i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 4 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xff000000ff
def s_31 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_31 : Nat := 0x570000007f
def ep_31 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xf0f00000f0f0
def s_32 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_32 : Nat := 0x105000001070
def ep_32 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x333300003333
def s_33 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_33 : Nat := 0x111300001333
def ep_33 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xaaaa0000aaaa
def s_34 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_34 : Nat := 0x200000a2a
def ep_34 : Nat := 0xa28000000000000000000000002000000200000000200000a0800000002000000200000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x3300330033003300
def s_35 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_35 : Nat := 0x100110013001300
def ep_35 : Nat := 0x1200020000001000000000000000000000000000010000000200020000000000000000000100110010001000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xcc00cc00cc00cc
def s_36 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_36 : Nat := 0x400440004004c
def ep_36 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xffff0000
def s_37 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_37 : Nat := 0x13370000
def ep_37 : Nat := 0x240000000000000204000000000000133200000000000010040000
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_37_0 p) (Nat.blt p 32)
def hc_37_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_37_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_37_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_37 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_37_2 (Nat.sub p 64)) (hc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 64 (dagTraceF m_37 s_37 5 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 64 bds_37 (dagTraceF m_37 s_37 5 f_37) (cur_37 0) (nh_37 0) s_37 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 ch_37 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 64 ch_37 = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xffff
def s_38 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_38 : Nat := 0x1f7f
def ep_38 : Nat := 0x600000000000000e0800000000000010200000000000001040
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xff00ff00
def s_39 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_39 : Nat := 0x13001f00
def ep_39 : Nat := 0xc0000000000000000000000000002000e0000000000130010000000000010001000
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

def m_40 : Nat := 0xff00ff
def s_40 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_40 : Nat := 0x37007f
def ep_40 : Nat := 0x480000000000000000000000000004000800000000003200200000000000040040
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf0f0f0f0
def s_41 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_41 : Nat := 0x10301070
def ep_41 : Nat := 0x400000000000200060000000000000000000000000103010200000000010001040
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcccccccc
def s_42 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_42 : Nat := 0x40c4c
def ep_42 : Nat := 0xc4800000000000400400000000000040c0800000000000000000000000000040040
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xaaaaaaaa
def s_43 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_43 : Nat := 0x2220a2a
def ep_43 : Nat := 0x80800000000002000200000000002000a0800000000022200200000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
def cur_43 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_43 : Nat → Nat := fun _ => 0
def f_43 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 1 (dagTraceF m_43 s_43 3 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 1 bds_43 (dagTraceF m_43 s_43 3 f_43) (cur_43 0) (nh_43 0) s_43 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43 : treeBlockF 0 1 ch_43 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 1 → ch_43 i = true := fun _ h1 h2 => treeBlockF_at nb_43 h1 h2
theorem lb_43 : LowerBin m_43 s_43 g_43 4 :=
  lowerDagV5 (kn_nil) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0x55555555
def s_44 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_44 : Nat := 0x11151555
def ep_44 : Nat := 0x4400000000000040040000000000004040000000000111010000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xf000f000f000f
def s_45 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_45 : Nat := 0x500070007000f
def ep_45 : Nat := 0x2000800000002000000080000000000000000000000000000000000000002000200000005000400040000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff000000
def s_46 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_46 : Nat := 0x100000013000000
def ep_46 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff0000
def s_47 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_47 : Nat := 0x15000000370000
def ep_47 : Nat := 0x22000000000000000000000000000000000000000400000004000000100000003200000015000000040000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_47 : Nat → Nat := fun _ => 0
def f_47 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 1 (dagTraceF m_47 s_47 3 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 1 bds_47 (dagTraceF m_47 s_47 3 f_47) (cur_47 0) (nh_47 0) s_47 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 1 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 1 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 4 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf000f000f000f0
def s_48 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_48 : Nat := 0x10005000300070
def ep_48 : Nat := 0x20002000000040000000400000000000000000000000000000000000100000003000200010005000000040
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_48 : Nat → Nat := fun _ => 0
def f_48 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 1 (dagTraceF m_48 s_48 3 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 1 bds_48 (dagTraceF m_48 s_48 3 f_48) (cur_48 0) (nh_48 0) s_48 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 1 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 1 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 4 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f00000f0f00000
def s_49 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_49 : Nat := 0x10000010300000
def ep_49 : Nat := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf0f00000f0f0000
def s_50 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_50 : Nat := 0x105000003070000
def ep_50 : Nat := 0x202000000000000000000000004000000040000000000000000000001000000030200000105000000040000
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
def cur_50 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_50 : Nat → Nat := fun _ => 0
def f_50 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 1 (dagTraceF m_50 s_50 3 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 1 bds_50 (dagTraceF m_50 s_50 3 f_50) (cur_50 0) (nh_50 0) s_50 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50 : treeBlockF 0 1 ch_50 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 1 → ch_50 i = true := fun _ h1 h2 => treeBlockF_at nb_50 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 4 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x2222222222222222
def s_51 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_51 : Nat := 0x202220222
def ep_51 : Nat := 0x222022000000002000000000000000200200020000000020200020000000000000000000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x5a5a00005a5a
def s_52 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_52 : Nat := 0x105200001a5a
def ep_52 : Nat := 0xa0800000000000000000000004200000040000000000000000000001002000010000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cc_52_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d07a0686d0198720e40c4388300d65ac148a905209c5382704e0944f99f03e07c0f81f03e07c0d901d001 0x1e4d104747e3634970e4b4e85a7025340e100f078582c2c1c9e17130b088542c28120f0b060283c34160a0c0d05858483d221a900b8705a341d140a8513020880c3c041a498fe34770e378519c14fe0276fd376e99b44bd7a56b1275691aa0fd4876a0374619a20bcd85c642b30139308c4844201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_52_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc2c0b9b8b8b8b18d88816b686868684c48483330303030303030301409080100 0xf52ce414f534e534fa44f13ced34e818e014782cda4cd644743ccd4cc944c418c014b83cb430702c9c3c9834942c902438308414 8 255 3 7 10 1023 16 65535
def cc_52_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x183060c112039468100b1020401 0x9b38993496389434422c91288f24403c8a4c88403e2c7d30 7 127 3 7 9 511 16 65535
def cur_52 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_52_2 (Nat.sub p 64)) (cc_52_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_52_0 p) (Nat.blt p 32)
def hc_52_0 : Nat → Nat := unpackHintV5 0xb40590ac054caa414f1a60d28492147123050c684142020850407e23e09f00f807c0354962494e3891a10b8c5822820f280b8002 0x0 13 8191 5 31
def hc_52_1 : Nat → Nat := unpackHintV5 0xd866a13311904c425e22c194109844b0a3911448243f11e88e0a6c23411810aca4491b389244421e20d1050c14a0430200084002 0x0 13 8191 5 31
def hc_52_2 : Nat → Nat := unpackHintV5 0x4311f90f447623629910c425a42b11488948405155852c014 0x0 13 8191 5 31
def nh_52 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_52_2 (Nat.sub p 64)) (hc_52_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_52_0 p) (Nat.blt p 32)
def f_52 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f1d288e92018ee20991040031b818cc0a7e053b029bb8911ea68e13c709a38061ca68e0140299b5931ac88052f60a6305118030c0140295ad0f1686005270291810fc08760437481e240d1205890240219810bd0828723a391b1e4d0e05a702502171a07008560427282614110a058502402118a0f4506a282e1e1a0a0b4503a2c3416160a0540844041f020d8105c10980844041e020d00826000f 7 10
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 78 (dagTraceF m_52 s_52 5 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 78 bds_52 (dagTraceF m_52 s_52 5 f_52) (cur_52 0) (nh_52 0) s_52 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 ch_52 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 64 ch_52 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_2 : treeBlockF 64 78 ch_52 = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 64 → ch_52 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nj_52_2 : ∀ i, 0 ≤ i → i < 78 → ch_52 i = true := block_join nj_52_1 (fun _ h1 h2 => treeBlockF_at nb_52_2 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 78 → ch_52 i = true := nj_52_2
theorem lb_52 : LowerBin m_52 s_52 g_52 6 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x5a005a005a005a00
def s_53 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_53 : Nat := 0x100012001a00
def ep_53 : Nat := 0x12000a0000001000000008000000000000000000000000000000000000001000120010000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def nh_53 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 3 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 3 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 3 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 3 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xaa55aa55
def s_54 : List Nat := [0x550055, 0x22112211, 0xa050a05, 0xaa55]
def g_54 : Nat := 0x2150a55
def ep_54 : Nat := 0x84000000000000000000000000002040a0000000000021000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def nh_54 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 7 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 7 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 7 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 7 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x1122112211221122
def s_55 : List Nat := [0x22002200220022, 0x102010201020102, 0x112200001122, 0x11221122]
def g_55 : Nat := 0x100110211221122
def ep_55 : Nat := 0x1022002000001002000000000000000000000000010000020000000000000000000000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1ec351f4250f42b27d8d5ad5951d1540f 7 127 3 7 6 63 10 1023
def nh_55 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0xfa75fa1b4ca5d5a2b0aa0f 3 6
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 10 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 10 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 10 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5555555555555555
def s_56 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_56 : Nat := 0x115155511151555
def ep_56 : Nat := 0x1000000000001440000004400014004000040040010404000004040001101000111010000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xff00ff00ff00ff00
def s_57 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_57 : Nat := 0x100150013001f00
def ep_57 : Nat := 0x12000a000000140000000c0000000000000000000100040002000e0001001000130010000100150010001000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 5, g_46), (m_9, s_9, 4, g_9), (m_16, s_16, 5, g_16), (m_39, s_39, 4, g_39), (m_0, s_0, 4, g_0), (m_30, s_30, 4, g_30), (m_14, s_14, 5, g_14), (m_53, s_53, 5, g_53)]
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x886208821178de0781c26c5b06c1a15cd705c15254141501314c13044910405003c4f03c0d207001 0x38091c682f45175273609196bcc352509228d0968a4aa5e4c9222925048a725e31a9148e4946a3a4e15a1068e824650b437d27b490d747e92333ca79a4bcb24e403f18178809c102e001f 10 1023 4 15 11 2047 17 131071
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x38e15402 0x7a515a41623d8e398a3583496341 6 63 3 7 10 1023 16 65535
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_57_1 (Nat.sub p 32)) (cc_57_0 p) (Nat.blt p 32)
def hc_57_0 : Nat → Nat := unpackHintV5 0xfa867d403e50be796da33ec21f61018f43c3c7e1e030a0b7e8daba7d5c029d2329ca94c040349fa0edb446d80350395b9aad80402d9f21cac9a4f0e27800955000940000 0x2f76e799e19e6739ee79abce758b2867a98e8673af5baf554401c3af73dd7a2bd5b9cef5ea0a0f41c38f71c0aab585ce1c15838741ceb5505881758b070e170d673aa80ac58171c3963738ce3618d121add94701c671a8e862c1c3aae3874316338ce35a583218e1d57bd706719d546315910c70105d3a73a871100f1e5a88 17 131071 7 127
def hc_57_1 : Nat → Nat := unpackHintV5 0x6a00b53ec54d6c3805b 0x4f7bac1c9d6ea9cebc1510e761c3859e6a73dcf339d62c39c70ea 15 32767 7 127
def nh_57 : Nat → Nat := fun p => Bool.rec (hc_57_1 (Nat.sub p 32)) (hc_57_0 p) (Nat.blt p 32)
def f_57 : Nat → Nat × Nat := unpackForestF 0x891cc48d4168703490527b7145b49ce3416c120290d86bcc352051fa714934bca3424c92028cd0492824504a79c978125e63520493928e4946a083f1d27020bc56840827091d048c8102e001f 6 11
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 3 7 bds_57 36 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 3 7 36 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 36 ch_57 = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 36 → ch_57 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 36 → ch_57 i = true := nj_57_1
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_46 (kn_cons lb_9 (kn_cons lb_16 (kn_cons lb_39 (kn_cons lb_0 (kn_cons lb_30 (kn_cons lb_14 (kn_cons lb_53 (kn_nil))))))))) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xf0f0f0f0f0f0f0f0
def s_58 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_58 : Nat := 0x10105010301070
def ep_58 : Nat := 0x1020002000001040000000400010004000200060000000000000000000101000103010200010105010001040
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_27, s_27, 5, g_27), (m_49, s_49, 5, g_49), (m_32, s_32, 5, g_32), (m_41, s_41, 5, g_41), (m_48, s_48, 4, g_48), (m_11, s_11, 4, g_11), (m_2, s_2, 4, g_2)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d27090e318c23071dc07019360580601715c1705c107401003c4d2340d0340c1288a006401 0xca519241ea396a31db498a32283e8350cc51a34e7b42c24e6a42184eb826ab5ea252515e8350845094528b5e7b52725e6a52415e61264944512f41232134294f1943e343d24fb2439a3f5a33394e3142103e0832001f 10 1023 4 15 11 2047 16 65535
def nh_58 : Nat → Nat := unpackHintV5 0x210807a341e50770325b98e6d81db287637298a0761e155ed25584553855303d460c50a1d3b8e4e01d0d5642a150a8041628d463285989e8527a00998a17dd42f60001780000 0x8171015ac09e387200010c5aac2e2c16038700017ba1cb82c0b8b5001c380000e07b82d5ad6ead5e387529c397b8fbdef7bdc1d0c3de56adc15abe86fa18e53872f7184008d1800c631a8000130000001e00f57852d54003c0000022f73a09c0e002a9ce738e613d5470e1c3800001540015470e00100000100518435870e0038870e40c 18 262143 7 127
def f_58 : Nat → Nat × Nat := unpackForestF 0xea390b43db490a4fbc51ba4eb8260a43a35ea2520a3f6452635e84506352625e625261260a33412f49444123094e0942194f21341943083e0832001f 5 11
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 30 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 30 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 30 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 30 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_27 (kn_cons lb_49 (kn_cons lb_32 (kn_cons lb_41 (kn_cons lb_48 (kn_cons lb_11 (kn_cons lb_2 (kn_nil))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x3333333333333333
def s_59 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_59 : Nat := 0x111111313331333
def ep_59 : Nat := 0x1222022000001002000000000010000200200020010000020200020000000000000000000111111010001000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_35, s_35, 5, g_35), (m_33, s_33, 5, g_33), (m_51, s_51, 5, g_51), (m_55, s_55, 5, g_55), (m_11, s_11, 4, g_11), (m_5, s_5, 4, g_5)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10974d1ab35d246c9168dab1256768ea91c51b801f 6 63 2 3 11 2047 15 32767
def nh_59 : Nat → Nat := unpackHintV5 0xdf00ac66ac00707870006791620b3658006c0000 0x156ad5d8de36e73c79d270000018d7ab1ac631ec6f39e3be867000001ec73b65bd68d1aa354f1e9a000005aac63469e3cc7471e000000000 16 65535 7 127
def f_59 : Nat → Nat × Nat := unpackForestF 0x425d168ecd74523945a26ac495851b801f 4 11
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 9 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 9 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 9 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 9 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_27 (kn_cons lb_29 (kn_cons lb_35 (kn_cons lb_33 (kn_cons lb_51 (kn_cons lb_55 (kn_cons lb_11 (kn_cons lb_5 (kn_nil)))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xf0f0f0f0f0f0f0f
def s_60 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_60 : Nat := 0x105050703070f0f
def ep_60 : Nat := 0x2020a080000040200000c080004000200040000000000000000000001000002030200000105050400040000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 6, g_21)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 6 f_60) (cur_60 0) (nh_60 0) s_60 6 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 6 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 7 :=
  lowerDagV5 (kn_cons lb_21 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xffffffff00000000
def s_61 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_61 : Nat := 0x115155700000000
def ep_61 : Nat := 0x1442000000000014004200000000010404020000000001101002000000000115155400000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 5, g_16), (m_17, s_17, 5, g_17), (m_21, s_21, 6, g_21), (m_23, s_23, 6, g_23), (m_1, s_1, 4, g_1), (m_19, s_19, 6, g_19), (m_18, s_18, 6, g_18), (m_25, s_25, 7, g_25), (m_4, s_4, 4, g_4), (m_20, s_20, 5, g_20)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x7971696861595851494841390e01 0x204d433810e42488cd824590cc342d0f233b4ce92370cd023104c01f 8 255 3 7 10 1023 14 16383
def nh_61 : Nat → Nat := unpackHintV5 0xaad2a8d6eb736d0736006de2c508eb508004b02c310d0310002b22f124c70009200000 0x18c6319eaa3d43aa39ce739ce7aa86739ce318c754739c3ace1ce738c631d51ce74ef3af5ac6318c678f1e1c30e00000c1800700e00c3604001ce738c631be80004780e639d553aa16000000444c038070060400f9be6f18ea80004784718d7ee1620c6318cf1e3c386739ce318c6ba4eaaaa8d1aaaaa754ea8d76aca8aad151ee979c62c41cc73aaa754b9ae6b18ea97aaaaaab32ab354ea9d51ab28aad1585af59c7b8e0398e74e9c3858000002f555555000564c0380700606c080010731ce9d3872e6b9ac635d3e6f9bc637d3d6b 20 1048575 9 511
def f_61 : Nat → Nat × Nat := unpackForestF 0x63314cc523909223310cd824590c42330d0b43104c01f 4 10
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 13 (dagTraceF m_61 s_61 8 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 13 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) (nh_61 0) s_61 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 13 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 13 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_17 (kn_cons lb_21 (kn_cons lb_23 (kn_cons lb_1 (kn_cons lb_19 (kn_cons lb_18 (kn_cons lb_25 (kn_cons lb_4 (kn_cons lb_20 (kn_nil))))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xffffffff
def s_62 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_62 : Nat := 0x13371f7f
def ep_62 : Nat := 0xc4800000000002400600000000002040e0800000000133210200000000010041040
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_40, s_40, 5, g_40), (m_42, s_42, 5, g_42), (m_7, s_7, 4, g_7), (m_37, s_37, 6, g_37), (m_44, s_44, 5, g_44), (m_10, s_10, 4, g_10), (m_43, s_43, 4, g_43), (m_39, s_39, 4, g_39), (m_15, s_15, 6, g_15), (m_54, s_54, 5, g_54)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x940ca023871c08a145022811408a0420e1010808404201f08f807c03e01d86b0f5802c01504a80540280940090448023040c4001 0xf954102640f14c0e9340db48071300c5680bd600b3500a16c099640914c0893407a560724e069461bc5f1ac5b18c571645314b521434a1315f1215b109570e1530d14f0c94b0a94708143061310496c0395c03b55033450545f044570295e0214601252b4b4fb334bae347a9b43a2a4fa0a4b9f2479ca439ba3f9a23b98237952339414f9194b90947819438013f7e13b75937711336f12f6092b5a127551235104f500474f83f4683a43837338361c02f058270181f008170001f 13 8191 6 63 11 2047 20 1048575
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9926098251942234fd304c11244110440e3380e0380e0290a0280731c07018460144501401400400 0x845b2096480511f93479141ea5e76919d146cd17f245bc115edc53ae97ab246a857e895b9e55e51539053e394b8651df143724a55b606cd21a360665b1916060d217a445c5216944571655246445553b584a5311b6044d4101501e4c0f93c 10 1023 4 15 11 2047 18 262143
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8c8c8aca8a1a08b88887a78786a615250494848333029282821200400000000 0x2fb44bc912e948b8512d150b2d56c345a6566aa547a4a29b6ca44d27150a09b269509c9726a6498512593492911e1288d5a22d6088971d928 8 255 3 7 11 2047 18 262143
def cc_62_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa86a0a0a80a0280a0244902408897b5c1615816054523481114411038c6818060144501404101000 0xf00d1f4263a82479482f0535c8113601a76480ea4d1fe28bf25d7c46ae2509ac953d84e6e084f40d5dc1a3482a7404ce44d1bc1238952700bcdc149b01a359526a0bcd214a15a1c194f8225b0249e0092b98436d066d006d95222d25c634d8b297188b630960 10 1023 4 15 11 2047 19 524287
def cc_62_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x881f37c1e1781e0781e074594641906416358151540d8340d0340b22c08320053140230802004401 0x260a8cf14992283384a65c1e4c35d94475244ea589b4a252932bd2454a40af4ea4f9b487348ee651bca943912571e48e381b4595c8a2891914a24a9c41417f0a30c0a5b810bf05184092d2105f021bc844 10 1023 4 15 11 2047 19 524287
def cc_62_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x91482412082402010075ba17cb85c28d40a045a2102802b140a0422010080320a0401201 0x2e4b05f958bd6c178d42ecb05c150b94bb70956dc9ee0352be4bf7495ead1edb152b5079645b2c0ae56944b06ab5ed16401d56b56b38bf6315eb8af56146ab25d1e12a912354146a58b148562a5a2d3949a6277464de84a8c7034 9 511 3 7 11 2047 19 524287
def cc_62_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb07602c0542a4338a704e0983302604a180b00200400800f09e03636c0d81b036058ab0131a604c014401000 0x1c297b812e6fa54dc2d99257355306a250c72b9ae515b01a6ab5dd46aba651a502535846cf4759c8db422966c50cc29b92d5721a2e3a5593074d40daf49b4904a6908dbb17f6e2bed35fd96afb0d1f592f69252d14959691b28afe315ec52af8854b0ca3e114691094d011af1aadea36 11 2047 5 31 11 2047 19 524287
def cc_62_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc330b1ea2a82829c67094a507d9f07c1d2741d0741a36810a388c2300a2280a0208800200000000 0x1fed7ff9a9e8a3afd2a54c17d1c1f8c8374605e3009fe91ae812acf2719c4a3dc267c23bf646f9a4abd41ba282f1704fe7163c8ac7825cef489dc4a3ee2c7cc52f48a1e297fb529f624dcb2554617d0c178a8274205e2809d0417898274005a220979817f2827ea2b9d2553a09e73936e42687c0fc401bf1814 10 1023 4 15 11 2047 19 524287
def cc_62_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x8238207e27c17447026466216016005655605415025004c24c04a1462460441440440421328320301094080080004000 0x6a474b88da3eaec2d448ea687d0d236ae45544852687c1122696c41258cc9b124be1e939342f1004f0505cf4221e0348b4bb158d5a695228353b86913d7225322f534884b90e0f21caa43e6486898750d2102242e4a8548c96128e8234243e838644c0b43a12c1764906bb1ed5639a5c6b478c4a8d28e96d1b3f54a8ba8f1451a229fb113a8626f064d92a25224473988c4a0fc381bc10178146b010d0901786827 12 4095 5 31 10 1023 19 524287
def cc_62_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xcdb30c8720bce96a42729c2708d2308c2306e1b06c1b06c1b05956045510405003c4a52445401400 0x9ea5da01518f1416c92b5d1279f85c77935772469d9464e04a9ea5e9e2467f14b769479d1294d84a410449c0349b25e8e1539a9294d04a99c529925f8d153989416c12b4c83a408364003497a5c972549692896124958249245e94a456b12a2a02f13027939565e9369335d929369212e2883f120378c9509125d8c1402782f108276aa3a5ca368b1464c04a3f046 10 1023 4 15 11 2047 20 1048575
def cc_62_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x80074660a6005c25c05c05825425025004084004004004004003c23633603603603602c52c00b10a00a00a0043002000 0xa6a4db092faf9273082f19027af017b2a5da624db215cb1151ae9506d92b589233002f188270401f2f82d17825ac82fac0272e82f170272e01f16817ada38ad235aba34ab138aa934aa0342d82f16027a792da7125a8c5da8151a6950792465fa36a41464f04a42046a935da6355a5b47a5345992379315990151a494ba3949a3147621417f93b789376d12b5f1274e83a41836a2129a1928a11245da365e936 12 4095 5 31 11 2047 20 1048575
def cc_62_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x5f58583c382a281a111002 0x2a52ebf5416ea56b348ccc178dc270503f688d6ce1a1902f1a84e6207c660bd435db1a6d4fd729d2e5803c 8 255 3 7 10 1023 19 524287
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_62_11 (Nat.sub p 352)) (cc_62_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_62_8 (Nat.sub p 256)) (cc_62_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_62_5 (Nat.sub p 160)) (cc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_62_2 (Nat.sub p 64)) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_62_0 : Nat → Nat := unpackHintV5 0x9c401358325e0d4ba0293c39208723e03476068e00d1784a2c0344a0e880150c04206124060680804fc051cd2b314865d850ba80963122c00657c0499960fd3613ac01d4a00c2e8001800000 0x78c13231c418d1c8e30c178e38e31238e3578c8e95e38d5c2231c4c2d3235d704cb2d397800070000002c0000800000100000000700000023008d32d30f2363570b0b8d74134e800174d1d1c000070132cb4c0010d0c30c00c8003001030c00015d5d0d0c00000b0200000001c0001c0000123000030c14020c3801540300030c30c000002c0003020000555500004000300000001231c71c71c71c7 19 524287 8 255
def hc_62_1 : Nat → Nat := unpackHintV5 0xb7072dc00b7002dc00b70028a527d259d81c75809b6206c019aa06690198e166102970145a81958124c0a12e0247840d04e1d1706e06140784a060b0782c00098181214000480000 0x8c2231c5d704cb2d397800070000000000b020000000040001c070008c00000078c3c4e3a32c21c8e38e38c2c8c8e2d3a38cb4e38cb4c2072308d5d300938013575301c00004cb2d300057570700000728cb4c18e38e35702e34c42d8e34e3 18 262143 8 255
def hc_62_2 : Nat → Nat := unpackHintV5 0x81053fc19f80cee1c77003b801dc00c94a49b624c010a38850042801cc90e6006914348018838be0c5e022397118087234232c10030702038000e1c0583020180a0c000a 0x2a38e38c8072304d3a0004d5d4c0007132cb4c00015d5c1c1c80070001d08d1c8cb8c2c8c704078d8e31c4cb5d04c8c1d4231c8e35d170c8c1e36312341e38e38ea3 17 131071 7 127
def hc_62_3 : Nat → Nat := unpackHintV5 0xc60563002fe357b08b9885c80ae2054656a0064f41a7014fc787c833d029e800f40077852fd81780cb50e5a802c42102c0447a16180ac083c341e000d830543006480006 0x1233c30db078362d60cf1c73db6d2c3438f0c38c78c9b3e870cf0d2c3430e835083830e00cb2c2c8700c003408c30c0b2c50c38000b2e326c0c00300c308d0b2c020c38403c3e3e1c71c3c008033c30c20c380c8d32d30f01e3a3807238cb8e30b0b078e3 17 131071 7 127
def hc_62_4 : Nat → Nat := unpackHintV5 0x864007f0747f0007ac4474e5e6d6786cc0a6cc006c60663c8a62e0e62e0062e005c26c5c20057e4451c6247aa240278400023dc2439a4232278234ee234001d4601d400174601185c096820069000006 0x3cf3e3e2c8cb0b2cf51c71c71c7002c8cf20f0040071c0f88c0f0b2000c0d001c1c70f2cb3c0f3ea22343430c31c700071d231e8f4b0d0e835830e00cb1c70c71c31c71c72e3030c318d0b2e0c3940070c71c71c0630b203003001c7002a8200000000c30c300aa003e3e3cfa0cf0e0c3830c71c71c71c71c71c70c31cf3c21c78000f4d5d4c1c231c0700008c70e31e32d30d5c13878c1c1c35c30c132cb4d0c34000300423100002c03e3e01c00000000033c310020c380001c01c00070722300000030070b08cf3c1c02e1c7800000f500003cf3e3e0708cb0b000f500aa08000080c30c300aa003cb2cf003e3e020f808808d0d0e0c380db3cf6c0000000f080000cf0c36c36c0000310 20 1048575 8 255
def hc_62_5 : Nat → Nat := unpackHintV5 0x818328100880a06804067de267d40a7d0047c80876c5c70468610f45e8285e6025c0265b40c5b2025644e550144e26e480623d4ac36c6836a02312582ee242ec022e6062c6201f6d0196600b8de000b8 0xb4d2d4e36307078e34b4b101c1d234630c34b55830d5d430d00c3500c30c300000c000000555500000c30c354b5550d5803030c3155550d5001418c1c1c0c3030c45051c7000418e34cb4c3c63578c2c2e8d74134e800174d5d4c0000238e34cb2d30c00010d0c30c0630003015c342344cb2d3830e100c0000c300005757434300063002c0800000000000000000878703cf000575707200701c004134d701d47978000700001763170c8d4cb4c4638c1c3cb2cf020000000000132cb4c0103cf00072300000700000000b2cf3c11c763cf800070000070f0022cb2cb0000000001000b2cb2cf3cf3c00000072301c00000aa0f00b02000000000030c30ea800c40000088c0000000 20 1048575 8 255
def hc_62_6 : Nat → Nat := unpackHintV5 0xaf9854f8fa9e0150a329b4612a0ca3e1647a028688d0a0320f0540a14744d0cf199920c3240064800c10817f032c63854844a78194e012900c46cb485088eb1f1b620294d819398062c0000c 0x30c30c000030002c02003001555418c0010000c0000000008c3578d32d33cf4d8d5c38cb2d72e35d8d32d2d4e3578d2d4cb078d5e34369b457430d0c0b2da500c348c6318cb8c30d72cb5cba555c5e35c2c0b00b2e0e35e50d75038c32080c308cb2cfa2cf50c38d54302cb694030d748d74cb5d8c74d34d3a4d1174d1071c1c1d178d32d74d3936e4d74c1c1c578e5c3532cb4d70d1036d1030d41c1c30c30c03057574343063505cb2d70e5db0e5400707070300040701c701c70c34d60c384c5110c307078c7 19 524287 8 255
def hc_62_7 : Nat → Nat := unpackHintV5 0xb141254721a53285168988a4083fd2a9fb01cfd8007d80a3e9019cf928e7802736033860a9c2804dec146ea06364089970d8af0e44e848224280fb0b86b094352031a2038a91404905c1448206e1a01c0d800070 0x8e35d170ca4cf4b0d0e970c30c34c4db033c30c1c1c3838f3e0c390cf430d98d690d0c30c30cb0c30d50c0db0c30ca873c7830c30e1c70d430c0c30c0c7830e830e2cb2cb555555830c30e2c72c71c75553070e0e5830e4cf3d34c12d3d5592d55531cf1c30c1c1e33d4cb478e0c3a0c3934d5594f5555830c30e4c71c71d554cb4d538cf6363238d38cb4e3128d4cb2d3030c0c354450c307071c754b5543839433cf51520c394f5555566355473c745447830c30e1c755a93cf3cfaa43436643433c73c7aaa1c70d439a2cb2cbaa430d0cb69a43432c72c7aaa1c70d43aa0000434366000008000003cb2cf413cf3cfaaa0cfa03034343a07071c78d5e3aa3cf3cf6a430d0cf69a43433c73c7aaa1c70d43aa000043436600000800000aa3cf3cfaa430d0cf5a66343438faa2ea562aa8838f1cf1eaa871c350e2871e8a00c30c30e0e00005555000000c0c30c3000055550000000c000000c30c300000c5555000000c00000 21 2097151 9 511
def hc_62_8 : Nat → Nat := unpackHintV5 0xd7478d6408cf438cf400c7042c182caa8b8a4034a18149cc26848c284800820147d8247d8007a41a7980679800738307380071014704067040070002638646200c6040e39d342dc602345407cdc0003e 0x28b4cf3d2cb53cf2cf3c0b2cb2cf3c01cf8d32c30d74130b4cf8c3570d36d38a57df0c30c355655430c30d5f8c30c30c30d34d5430c30c30c71d31c790c34b3d930cb8d2e38c3e30e30da90d3e0e8d30cf6c6c0d2c34390d3c32e0e0e30c1c1c30c37d8e34d2d72d4c7d8d31e34b4cb57134c74e8d71c419b6e4d34d30b0b5d701c1c78c71c1cf0c32c30d32cb4c30d4b2d2d4f0d0cf5757543930e134c2cb2d31cb1c31c31c75d474c1c7071cf2cb3c88f3d693d12541c1eaa80020000000155540002a93d52d593cf3cfaa5451553d98d555553c73c7aaa451c751471d5633d7632d30d70d3 20 1048575 9 511
def hc_62_9 : Nat → Nat := unpackHintV5 0x84d5c20606a7e31a9f88027bb139d74bc72b191ad0ee67a1d1900745dc321640985740e14a89449948919c644331a1004643d5160e846833c328bf0802714589b8062451487e4981bd1e03f1820c01e00d91400419000008 0x2cf2e2cb2e2cf2cb2cb2cb2cb00b233c3cf3c2d2cb2d2cb2cb2cb3cf3cf00b071c072c71c0701c1cf0f1c001c1c0f2cf8f8232c2c2d357530003c3e8f3cf002c8c0015d5cf000f0104d35c1354e5e0000000f2cb3c002c8c0008000132cb4cf3c000100000000000002a80020000000030c30ea80002aa3ea2e803c3c223a0a6c30c30eaa60e680c301c1c28882871c8a00030303cf3e3e08cb000b03d357530003c0d70c308d132cb4d0c3400400c0003e3e003c22300002c06c0033c3830e000c00400000000000003cf3d3824cb2cf8e2c3e83d357531c73cf07072d33e2e9b8cb8c0d70c3570d8d32cb4d0468380d70c30c707076db3cb3cb6cf8f800f3cf2aa02230cf0c35b6c35b830e030c301c1c071c071c0708000c1ea8000030c30ea800002000002a80002030c30ea800002000002a8000030c30ea800002000002a800021555400002000002a800000002000030c30ea80002a8000088c3c00b0080030c30ea8000030400020000001c000013130e0e0c354d30c3445507070c31c750c30c30c3564354cb2d3545030c30d2d8d555554355531cb1d11d1430c30c30c71d54ba2cb53cf2cb3c132cf3c0523cf8b2cf3cb2cb2cf3c4c5d75cf3c1c1c71c30d32d2d5435d5830e1312c30c1c1cb0c32c30cb2cb2cb0cf3c34b6352cb433d3c357575438b2cb3c38b0b2cb2c2cb2c72c70c73cf3c31c75d472c1c72c1c70b2c0c30e0e2cb552d440d507070c352d0d55830c30c30d4542cb2cb0c30c355552d50d555454472c72c70c30c30c31c755a2cb534d4f3d044c4e34c2cb063 22 4194303 9 511
def hc_62_10 : Nat → Nat := unpackHintV5 0xd440363a342c12e154064a0c4a50301a7d025278b88945440a201ec0c8d291c6263731001984020c2000610002f609168098af0285043a271089380048fc6245c111a9428b490048c8c1d638078398220d000088 0x232e8ba2cb2cb2e3cf830e2cb2e3cf975cb1cb1e1cf3cf871d71c7a8b2cf2cba8ba32cb0b2cb0b2cb2cb8f3e0cb4b2c34b2c30cb0c32e0c3830cb071cb071cb1cb1e1cf3cf871c30c7aa00000c30c3aa00000800000a3c0f823cb2cfaaa0c343430c30c3a07071c78cb4e3aaa3cb2cfaa0c30c30c3aa0c30c33c72c7aaa1c70c30c3aa3cb2cfaa0c30c3aa0c30c33c72c7aaa1c70c30c3aaa555553cb2cfaa553c72c7aaa551c7aa000800000000c30c3aa0000aa8ba38faa3cb2cfaaaa2a030c30c30eaa683a6830c30cf1cb1eaaa2871e8a1c70c30c3820fa34e2cb2cb3c8cf14f4c0f3e350e3a2cb433cf2cb3e80b2cb2cb503cf0b934cf8cb884cf3cf2c2c2cb3db575707073cf8d34d32c54d35d7149782cb134c71c1c1cb178d35300f2cb3d36cf8f82c8cb2c0b2cb3c132cb4d354cf3c00701c071c071c1c1c001c1c0b2cb2cf3cf3c012cb63cf8000f00000b2cb2c00000b2cb2cf3cf3c00000f00000030c30c0000315554000003000000b2cb2c2c8c0000f02c200f000b2cb2cf3cf3c0000100003c0000000002cb3cf5d063cf84c2cb3cf070700003c2cb2cb000000002cb2cb3cf3cf00 21 2097151 9 511
def hc_62_11 : Nat → Nat := unpackHintV5 0x7e16a7086c640644191433074200981d81404cc6028120280000014 0x2a8ba32cba2cb2cf2cb3cf3db3c3cf3c8f3e0c32c30cf0d3cf0d3e0c3830cf1cb1cf071cf071e1cf3cf871c30c7a0b2c822cbaa0c343430c3a0707aa000800000000c30c3aa00008ba3aa8baa2cb2cbaaa8a030c30c30eaa60e6830c30cb1cb1eaaa2871e8a1c70c30c3883c3c2cb2cb3cf575707073cf1c755550e0e552cb2cb830e552c72c7830c30e1c72d707a2c3432c3432e0c3835c35d6839430d17032c30d70c31c1c1c32e34b5c7 20 1048575 9 511
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_62_11 (Nat.sub p 352)) (hc_62_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_62_8 (Nat.sub p 256)) (hc_62_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_62_5 (Nat.sub p 160)) (hc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_62 : Nat → Nat × Nat := unpackForestF 0xb4fb3a35b383400b4baea5dae95cb1936ae951af12fb003caf127af017ae95000b47aa238aa235ac02fac027aa234aa138aa134aa03400b43a335da6c5da6951a712da7125a6950a3355a3347a3345a314ba4146a3149a314700a4fa1129a1128a112400a4b9f9519f85c00a479d25e9d2469d9469d12900a439c03400a3f9aa5e9a92900a3b98c5298a5f9894100a3795a5c95a5495928959249582400a3394a450094f939569235d921369212e0094b9125d009478235d8f95d823558e9348234b8d95c823478ca4d82254821478aa5d8aa358214689b5c892648213f8825c86a64871548684c8213783a4a83a468383e84044838328213682b64820170094380a35808340093f7eb5f7eb537e9520093b764587d235764527aa3b7b84c7aa377a8377645079458791587625f7725c7724477128762537624d009377195c719547193c719367282f728277193471814009336fa5e6fa5c6fa540092f6145f6e16c614576135f61357613476b9456125e69b5d69b5569946612526124a664526723a67236664506614d612466115f63b5563b4563a556115e611576115261147611460092b5ab525f9585aa5f5db605db505d9605aa575ba5d5ba555b93d5a9525a83c0092755c5f5916c55c5757b5557b455595e56b56559465592e0092351b4554146519495193b5245852158519370084f50951008470083f4f1494724f4e129472434723b472374b35d4b83c4b13647143492524915e491524712b4815e47123470360083a444524515c451444415344141008374302934343420493414f3412d34127341253a4513a25d3e84c3a2353a04e3a0353c2413c14d3a0343aa403a9343a0263404339134371523705e37824370523403336034349523485e348523401b008361cc5f32a441cc5b30a6c3096c309601cc572e3442e2442e1482e1441cc532d1502c3552c3451ca5e1ca462aa541c95f2936c291341c95b2826c1c9572725c25a6425944259341c95324a441c94f1c94b22568225602225c1c9471f96c1f9641f9441f9341c9431d25e1e4501d2461d1461c9290082f0645f1b3480645b193601916c191600645716b4816a441694816944064531545915246063520634a13b580615f1294c0615b1136011350061570ea640f9540e94c0e934061530db480614f0614b0b5680b5600b350061470896c089640894c089340614306a5606a4e0694606131008270245f0496c0245703355033450215e021460081f01252008170001f 9 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 4 15 bds_62 362 (dagTraceF m_62 s_62 8 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 4 15 362 bds_62 (dagTraceF m_62 s_62 8 f_62) (cur_62 0) (nh_62 0) s_62 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 96 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_3 : treeBlockF 96 128 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_4 : treeBlockF 128 160 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_5 : treeBlockF 160 192 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_6 : treeBlockF 192 224 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_7 : treeBlockF 224 256 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_8 : treeBlockF 256 288 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_9 : treeBlockF 288 320 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_10 : treeBlockF 320 352 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_11 : treeBlockF 352 362 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → ch_62 i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → ch_62 i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 192 → ch_62 i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nj_62_6 : ∀ i, 0 ≤ i → i < 224 → ch_62 i = true := block_join nj_62_5 (fun _ h1 h2 => treeBlockF_at nb_62_6 h1 h2)
theorem nj_62_7 : ∀ i, 0 ≤ i → i < 256 → ch_62 i = true := block_join nj_62_6 (fun _ h1 h2 => treeBlockF_at nb_62_7 h1 h2)
theorem nj_62_8 : ∀ i, 0 ≤ i → i < 288 → ch_62 i = true := block_join nj_62_7 (fun _ h1 h2 => treeBlockF_at nb_62_8 h1 h2)
theorem nj_62_9 : ∀ i, 0 ≤ i → i < 320 → ch_62 i = true := block_join nj_62_8 (fun _ h1 h2 => treeBlockF_at nb_62_9 h1 h2)
theorem nj_62_10 : ∀ i, 0 ≤ i → i < 352 → ch_62 i = true := block_join nj_62_9 (fun _ h1 h2 => treeBlockF_at nb_62_10 h1 h2)
theorem nj_62_11 : ∀ i, 0 ≤ i → i < 362 → ch_62 i = true := block_join nj_62_10 (fun _ h1 h2 => treeBlockF_at nb_62_11 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 362 → ch_62 i = true := nj_62_11
theorem lb_62 : LowerBin m_62 s_62 g_62 9 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_40 (kn_cons lb_42 (kn_cons lb_7 (kn_cons lb_37 (kn_cons lb_44 (kn_cons lb_10 (kn_cons lb_43 (kn_cons lb_39 (kn_cons lb_15 (kn_cons lb_54 (kn_nil)))))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffff0000ffff0000
def s_63 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_63 : Nat := 0x115000013370000
def ep_63 : Nat := 0x1222000000000000000000000014000000240000010400000204000001100000133200000115000010040000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_4, s_4, 4, g_4), (m_49, s_49, 5, g_49), (m_37, s_37, 6, g_37), (m_11, s_11, 4, g_11), (m_50, s_50, 4, g_50), (m_47, s_47, 4, g_47), (m_26, s_26, 6, g_26), (m_12, s_12, 5, g_12)]
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c0450610708084041060810017a1b521a80d406613301980cc06212d11680b015802c01504a805402a0140490448023040c4001 0x3da007d3d0ca6a1d49435a8063400dc74198d82e9b0d34e19e8632d0861278b94f1024e1c09c2c0b83c3409848109081ea10524f09486111381c130302602888090d00da1016420569e08d0c0e27010360106d68d3ecba5d7f47ae6875493ea125d3247a4487468fe871dcea37954671b53e2ea5c394782a87014fdfc9dbd5376f266da4bdaa95ad127552467b12c9c218f43e1d876350cc2a190342b058460306c02098001f 13 8191 6 63 10 1023 19 524287
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa922888211842107c9f07c1c3701c06c5b060d8054d504c9304c13044910350d0304c02c4b002c00 0x8697a0a5280579f85e9ad2e6343788fa514f9051e304f8811df01778071d45072131c2376e0d9b0265849d594d625152125569357a454449953505ad215450520912b4e46538f035300552a30468c1645256d7943524ed05334048979115e420f4c8353a094b815 10 1023 4 15 11 2047 18 262143
def cc_63_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2618ce3088620791e0781e0781b36c1b06c18327c902409018c601445008c20044100400100000 0x2d920bd182d230ba132d83cb4d12a044a00d2c824acd0aaa4aa84869242a252a8132f4d3fc34be6d1f7b43dc93f624bce91f1a43c28fefa3bb88dec233ae13a98369e09a184d96116001592176194d8e515f8168a5761134 10 1023 4 15 11 2047 18 262143
def cc_63_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x986608cd4f501404892048120480e4380e0380b32c0b024890240902405414050140230801104001 0xfe4d201213f1427d27552d3e9da5d13479e6873a93e6d25cb24792487208fe391dc5a37874670c13a041b3e02655088f20d1deb03b25c754a0e8171c91c38a3470068a20d1b41235d606a6b8d2d41a02e3324c65488c8091881a30024 10 1023 4 15 11 2047 19 524287
def cc_63_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xccc8c8c1c0c0c0c0a4a099987c786a685a585843393831222020201918030000 0x50a38a0469061127c1a4e0249aac132d7261a84b85c7f0492a93251223f0349304904112441a3e8348f0491b18229184604c89049128d229a244024842490ad0a0d214112d 8 255 3 7 11 2047 19 524287
def cc_63_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0798730660b8b702e05c0ac75056a2a1540989301a6340680b1141188300600a1140280500a004808000800 0x17e8faecaf5c152230617a8caf0af5d9523f07c440cae52f5c252b727d608c34e2de8c53d06bd9cd6f31a9e3352c569d88d0f09a16025ebe4a57457ad8a9579208b0b6b814cf8271c043200856a0ceb8ae5695cb20516692ec521d614e8a096b410ec011d7149ad28358492bd1a5595e870b6b014ea01a53560a54b9489428c2e42034 11 2047 5 31 11 2047 19 524287
def cc_63_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xcab20c4710b16c0ac6b0a865594232885e46cdb064981589605455054141320c02c4b01945101400 0xf26bfdcd5fb12f7595eea279ce4db7c9a4905b630a6240ef75236e35edb4bdac496402db0853d928d9ed4b612f6b95ed626d1c16d7c29e5b60d46905a10329b061b50d2690581433e2f2183e2b0659e932cc9859120b12619a0a0a82864240cb8b395146342caf0514109c5010b241563826270a18714b05af5e95e3a0824c100941860a32bc2bd72549001f12032 10 1023 4 15 11 2047 19 524287
def cc_63_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9d27094a5094232849f27c1785c170549505415048d203ccf0348d0340b2284a0208802006218006 0x8015e4d85b360537f8184d059358517d83b7d0334c84b350434c04b348437ec587e4527cc507c24c7ba404b05b338537b0407a2547995478c607826c7796c7694674126709244a84b3304374b527415e7195c7115c7282871949711417324b722437094e4a04b3284370023 10 1023 4 15 11 2047 20 1048575
def cc_63_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe01c03614b194128250443843081e1bc0780f01e036354ca81312603c8780f01a2340398700e01c001c00000 0x8f3548ea5494b539434b93b499325f92a536824d9224b91a47902458fa3f8e2338113e761326c12a5d1262303e170328d13c8c9368c134892418ab4988a322283e8946088b6c8826c8b3518a25d89a3f87a338495d2203e86a545ca345c24485a34841446793467b52842528635f853535b2368495e83936830188225f81a5762a3d8115e4e85b370530a02b 11 2047 5 31 11 2047 20 1048575
def cc_63_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0ae2b0ac09224084e107c9f07c1d26c9b0685a0681826012622880200801c452140501405001400 0xa003b9f8335284b3b0435204b3a843a1458a0c529f4509e94c9e1405105b398539d8409ca469a925991245084b390439ab5e9a252989499794198b5c97b5c970189924e9814b969435004b38843960139c35e9ba5e8e15f879579b12899925959244f05b378530401b5e12490b545d9349135190a428f2322383e17832 10 1023 4 15 11 2047 20 1048575
def cc_63_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x8008007087007007007007007006654514404404403e33c13c03632a62a02622601a61a00c70c00c0044040002000000 0xadcbf5e8d652afd753568a4e4c13866210c840ab6830d549e89912c3e188655bd4eb5a5d6749a3c7d388ca4cafc31536829b5852eaea3d55458227ef24cdb896b01252507c300caa69454925a8a48f15069dacbc1322487d4fd46972ed355d81a7eee4cc901f33e5285aa54b97a4aafc29535f26b4a496921451e5e8fabf1355d8a9eaa45b3d0a60a06e8b2f29c5b3c0a7440a14c2c9dc51 12 4095 5 31 10 1023 19 524287
def cc_63_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x16254890b142850a1405 0x169120681859e35b326ad349c9a275925cb1ca162572c2a858050 7 127 3 7 10 1023 19 524287
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_63_11 (Nat.sub p 352)) (cc_63_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_63_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_63_8 (Nat.sub p 256)) (cc_63_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_63_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_63_5 (Nat.sub p 160)) (cc_63_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_63_2 (Nat.sub p 64)) (cc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_63_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_63_0 : Nat → Nat := unpackHintV5 0xc3a0585c1ae328dc600b8c016f426dd815b506aec7f4716a800e4fe029ca3322572438148205862a2dfacd99a5a84af4ca3e98c09250ca004a3fc047e414d428901a718a780a274001400000 0xaaa8c06a73a81d46ccaed07322aa014202288086c4539c0e2001c1546319d44dede08f372f608aaaa738c18f1e28d54608b22d555e00c62bd6b551a22aaaaaa78f2a9cf2d72aaa355676aaaaaaaaa22a3515455554e0782539e94688aaaaaad52a9ce73d52aa35555676aaaaaa9d115945515ded69d966c7ee9554572e4000501400001eaab055aa8c18f5a8d445115505110078f1555182aa83b50555540159554680aa00a0080000aaa00aa002000000aa000aa000ec4040000080000418c6318c63 19 524287 8 255
def hc_63_1 : Nat → Nat := unpackHintV5 0xb6eb3519c67a294569e876370e40a0319ba066698a8a03311a261d4602c0e85800087a890f001a07e3400060080b9071680a2a8285084899080c46e180082b8485502098121141c002280000 0x6a00318c67018c000710000c6318c6739c0e318c60003061c00055400000001541550000155000000005507600aa0020200100700000101ef63d803d8d1aad963d54603539d5e2c3ad46c8a12bb550096b8407a28000021b14555381d1000e0aaaa8d1803b46a8d415182aaaa35955054001154000000015415500010d80a7381cf1e00000515501553ccf33a084c98705555555514650e1d76ca7381d5546a8080506d10055514667099bd8c9a1079cc080039c630d85b60628001c00088001a9c 19 524287 8 255
def hc_63_2 : Nat → Nat := unpackHintV5 0xe142b8500db85f6e00d7c3f5f00d403f024ebd03af202bb416a548a5c3a9502a40164848722017c4c4955d250033560cd00248ec9200131184c0005cd4170005c001205024240009 0x6c6ec6ab77b5ee0454155cb9e3c51aa8c11768f56aab055abc58b51aaabb96ab41784b5caf7aa8d115555555555768d55555555115955455150d88d1011a353b1d00010d8c6280a8c6739e3c00141c38c631ab6d94e718c0ea21c6a354eadb100006318c68368800c0001a8c56440d8f61b6 18 262143 8 255
def hc_63_3 : Nat → Nat := unpackHintV5 0x8ec023b007dd11698e544614f024d865280e48c15170c43824ee203a414e40537c14cf102e854b80227c64910e23014800c1dc245720148144d051201438100cc141c1705c140017 0xa3c25ae57bd4688aaaaaaaabb5546aaaa35546aaa22b2aa8aa2bbdad3a6f68e1364bdee59b1dec6832f7bdef72ef6f04ded1826c1fbd8f363bd8d047ef7bdec4def728fdef72c4 18 262143 8 255
def hc_63_4 : Nat → Nat := unpackHintV5 0xd719c5a3c482b917b685b405b185ad09a0999e059a879a808e198e00819981807519728571825f25590c590059005012225c2200220022002200004400000000 0x6f68e977b1af0479bda3137bd9b1dec683bd9bda304ded1d2ef68c106bb46ad963f7b368c451455cb9e3c51aa8c1151a355582ad5e2c58d555 16 65535 7 127
def hc_63_5 : Nat → Nat := unpackHintV5 0xe8d3f950ee282f8109ced1b3209cb8132707bc0dee40c88b0a111183015f6167b0297d6f5f4017d0058c691d461f2845626150083d170e01433050b81425090306407050001c0000 0xe7539d70473d44073ad6ed86d36800bf6bd967be9f002ec136028003c020005046305ab5600b971c0201e3c03872aa02063180c6b463658e1e337b2fb5eee0f63005ac000000002e6c630001ac600017b8000053300000040d1a00154000000000040020000040031800550000830dec6ad3b2cded189bdecd8ef6341dee 18 262143 8 255
def hc_63_6 : Nat → Nat := unpackHintV5 0xb37656640ab09c4f1708499b08809fc94ba1586ac96a92c94e83a76274ec0091cbd091aa0b073e4327c800e7919cf0037c226e414dc801b7022cca244554798f0d91a0c2f014c3803a600007 0x73800000006c380002001000000c6000319c000418540b1e039e59ceb473870f488f7ac7873d0c63469ce1c3d550054cd4700a01e3c0e01c8dd050c63381cf55530e478c002804078080000b5ad5a00000318d1a0b5005c00f0220001a340172e0000000008d8000200000000c60012c7000083047b55a7960f368b5ccf2c1e2c98b5ad6f1a351ad5c3c96b5a4f81af63c6ad6b5cc2682f7c40d46366ab16b3803c0390000d1ab0003c11f7b4d81ce06e6b316000001b800039000d1bb37502bdab4116b05873d2ec 19 524287 8 255
def hc_63_7 : Nat → Nat := unpackHintV5 0xb3393515526c36cd30598e19139e5f0373825e65ca8977452c02a560246a42890450d05218023fa367e014ea1218e46270ac4a8388e0709e7e1241824800420708400108001c44c36028006c 0xe739c00000d80001c00400200e000c6000338ce000080c600000aa000000000aaaa0000000739ce78f000000718c068ddec780001ce7380000001c00018c6719c0000e739c000000006300019c670000aa000000000818c002a80001540000000154001540004000000e739c0e0010000000006c00e0c60318002000338ce00b366ceb097bdbbdac366c497b00a10000400005cb8000631a34002a80000000063000aa00588f67a5a802ceb38000100041c0001a346b19f61d703003c1b005ac00000000e00318000d6300 19 524287 8 255
def hc_63_8 : Nat → Nat := unpackHintV5 0xf580bea80bc60f6ddafd0ab18e532f0ac540a19ea973cc0a55a448c1f8f6231c42a37814541b77f2aed429c812b8b056de38ca5199202ae83c528a8786ccdb1599a1c2b084296cc2a2880054 0xf2dbeb60f004007cd5f3e0136a0a803c78aa31a8c6a30468d1462000aa00000000aa000aa00aa00aa000800000aaaa00aa002000000aa000aa00000aa0026c0000004000020000055000550001104001172e40d80000aaa2082d556ab1e3d6aaa9d56bb7bdbbdede16d6d8f001411155595415404d803c78aaaaaa82aa8a6c7bd8b225a3da9408d18002e5c1b4401eaa09b5a802c00000068d005500000000550005500000500001360000000000100002a8000d1a0800080c603c5ed70fd9c47ede6c0786c43620053c01000102601ce0000100006c0000e00318000300118ce000000739e3c00001c68d0005500000000550005500 19 524287 8 255
def hc_63_9 : Nat → Nat := unpackHintV5 0xc7ad576d8ab8b551d548b785158161496bd1586f6acdc02db1072f36f5ba2cb74016a04ad4005a800b18396082a40813117059090a58c905461c4462f494518d0891a10e041f42817278002e 0x1e3c000000000031c71c0000000078f00000c6000011c7001e3c000000000031800471c0000aa00000000aa000aa000200000078f01c002d8000000000000c603180020011c7006e8163c151ceb473870f488f1e0c63469ce0154000000003180055006c07c8e07a800000f1e004040400d1a3c65001cfb8790f61c3d55004f79c0e054318ce073d50de30e1eaaa00b74cd4780000820a22806319c0e7aaa98720c37300363d079b7a13001eb97000000d1b02f72f63f72c2d8f46f97b78cb78ede6c6882c5ad6b447ac68d18ceb3ae5ef6f0 19 524287 8 255
def hc_63_10 : Nat → Nat := unpackHintV5 0xb6c7ab0d5fa32dba0b279ef1c9975897d1a9631a961029124f84bc77f3587926172b67675b66185d616025ce4852da14db5248d4e42a6334ddd2f95420aef1c842174540c9ab075540116400c050000c 0x643882b8f6ce759de2c3ace71a346300000172e781b0783c068d060a26c0553a739c0f399e99e04002730981c1546228c6a31a8d1a232dcc20fb96c759b5b1e70475d1ce88f1e1ce346ed62df26e56b59043c447ad6f5ac68d18ea3a9c38b9adb5a54f1e558b0e796b95463518d468d946a3468002a800000002a8002a8028a1c0f04aa739cf54a75555555556a954e739ea9553aaaaaaaaa75b6ab54aa74456554e739ea95454554eaaaaaaaaaaa28aadb39ce1c3bc78755551101eb162aabd6b555554545555556d9e3ca2a2a9cf2d72aaaaaaaaaaaac1c3aed94f2c792d54eaac0e074179cf54738d1aaaab54aa739cf54aa9d555554e9d39e956dc7aaa8f114aa9ce73d555142a8ce8d3cb2d33431a8d1b42ce6cea7d8a140b39cea1c39ce74e9e751e3c70b61400001c0e7080e0318ce0738c674633b1c703000029980000068d000550000000055000550000aa0b600008004000000000000c6001540080c60000000aa000000000aaaa000000078f01d3a000003180d1bbdcb 20 1048575 8 255
def hc_63_11 : Nat → Nat := unpackHintV5 0x11e151dddeb5962612a097ea905aa1b3582bea841d6057ac000af 0x55000000005500055002609b0000ea7020e0000000000000aa0080c60000234680220c703aed8e7578b0eb3aaaa000002e5c1b4041e0aa826c14066aaa7381d595410005040e0aa82aaaaaa8a2a80000000002aaa800000002a800000002a8002a80000000002a80002a8002a8002a800000002a8002a80000aa800000002a8002a800200009b038004aa000000000000008c001550005500 19 524287 8 255
def nh_63 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_63_11 (Nat.sub p 352)) (hc_63_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_63_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_63_8 (Nat.sub p 256)) (hc_63_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_63_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_63_5 (Nat.sub p 160)) (hc_63_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_63_2 (Nat.sub p 64)) (hc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_63_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_63 : Nat → Nat × Nat := unpackForestF 0xb484800b4fb3235b313500b4bb025cb0250b015cb0150b005000b47aea35ae93500b43aab53aab4baab49aa94baa947ab341aa94500a4fa8928a8925a892400a4ba6b51a7359a695d00a47a4a5ea4925a482800a43a3a5e00a3fa225ea202800a3b9dc589dc529f83b9f8339dc509d94c9d9409d84000a379ca4695b5e95a5e959289a35e9a252959259624e98b5c9614b9735c9701896143960139592400a338e3538e34b8e3498e25f8e2538e24b8e24790b5190a428e2458e23f8eb548ea548e2330094f8c13c8c1368c1340094b87b518ab4987a5d87a3f884608836c8826c87a330094786a548335f85a34833538315e842528313683018009438125f812578115e0093f7f95e7f8180093b7b4587b4527d03b7d0337b4507b24c7b2407b0400093779a54799546fb5f77c6077a6c7796c6fb57769466fa5e6f95e6f93c743527415e6f9367024b728287024371149711417014e700236f934009336ea466db5e6da5e0092f6c9466b25e6b15e6b1360092b6a3485ac5b693485ac535ab5e67a4c5ab5b668285ab5363c5963c516382a64240638265ab525ab4e5ab4361c525ab4260a325aa5e5fa3e5aa525da325d95e5d9525a95e5ba5e5ba525b93e5a9525a833009275824b59028582435802355a345694956941561245595e009233e34f540343e34b51d6051a5c51a505185c3e3474fa384fa344f8343e3433e24f4e0243e24b4bd604bb5c4bb504b85c3e24749a4c49a44498243e243488343e23f478243e23b464604604c3e2374434444a34440243e2333e04e4134242124412424112d3e0363ea423f9343e9423e93a3e0260084b27b4f3c83427b4b3a5603a25c3a2503a05c27b4738238382343803427b4327a4f3682427a4b345603435c343503405c27a473224c322443202427a433103427a3f3002427a3b2ec602e84c27a372d83c2cb442c82427a332784e2a3422a24a2a12127836282422814a2813227826008431f34b1f343258451f14f2485d1f147239451f04f2295d1f0471fa5e211341fa521f95e1f85e1f0170083e1e01c0083b1cc501c84c1b2371b0361b026008330b34e0b3430b342189450b24f17a450b14f16b4810c5210b5e14c501482410b5210b4110b4012a3010a5e11a301095e1083d0b1270e93d0f3400e9250b0270ba3a0d3500ba360c3400b9360b017008320724f09824072430704e07a4207942070260082b06026008230234f04834023430204e02b4202a42020360081b01036008130001f 9 11
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 362 (dagTraceF m_63 s_63 8 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 362 bds_63 (dagTraceF m_63 s_63 8 f_63) (cur_63 0) (nh_63 0) s_63 8 = true := by decide +kernel
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
theorem nb_63_11 : treeBlockF 352 362 ch_63 = true := by decide +kernel
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
theorem nj_63_11 : ∀ i, 0 ≤ i → i < 362 → ch_63 i = true := block_join nj_63_10 (fun _ h1 h2 => treeBlockF_at nb_63_11 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 362 → ch_63 i = true := nj_63_11
theorem lb_63 : LowerBin m_63 s_63 g_63 9 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_4 (kn_cons lb_49 (kn_cons lb_37 (kn_cons lb_11 (kn_cons lb_50 (kn_cons lb_47 (kn_cons lb_26 (kn_cons lb_12 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffff0000ffff
def s_64 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_64 : Nat := 0x155700001f7f
def ep_64 : Nat := 0xa28000000000000000000000042000000600000040200000e0800001002000010200000155400001040
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_31, s_31, 5, g_31), (m_34, s_34, 5, g_34), (m_6, s_6, 4, g_6), (m_18, s_18, 6, g_18), (m_33, s_33, 5, g_33), (m_5, s_5, 4, g_5), (m_30, s_30, 4, g_30), (m_28, s_28, 4, g_28), (m_52, s_52, 6, g_52), (m_13, s_13, 5, g_13)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a04d02489240900c8023831c08e04312103080820c101f06f807c03e01d86b0f5802c01504a805402a0140490448023040c4001 0x1015c0f9540f14c0e9340db480c94c0bb500b3400a140071300993c099440a2540914c0893407a5e07246069561b45f1ac5b18c571645315b5a143421315f1295b109570e1530d14f0c14b0a94708143061310496c0314c0345602b560545b04457039560214e01242b3b4fb334bae347a9b43a8a4fa724ba5a47a2a439b23f9923b97a37952339394f9214b89947851438413f8193b80937711336f12f6092b5a127551235484f4b84a48847388463483f338371c02f058270181f008170001f 13 8191 6 63 11 2047 20 1048575
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x90e408c6308c20347d103c8f03c0f03c0c3300c0300c0210802008014c500c8300c0300c00300000 0x20a5480511f9347ad41e25676939d156cb17f245bc115edc53b495ab24ea857e995b9e55e51539053e294b8651df143724a5bb5854d01a360665b1916060d217a445c5216944551794a562c5153b581e4c1246c471811360 10 1023 4 15 11 2047 18 262143
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0d0d0b4b0b0a9a8939089888881806460606060444032303022190a08010000 0xbed12f244ba522e144b2542c456aed5a3949aa951e928a51b28c60a09b1e1289c572695498512593492911d9288ed72313484502225c82502124c 8 255 3 7 11 2047 18 262143
def cc_64_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0b0284a0280989bb6c1a1681a05ccf83c0f03c0d2340d02c8741c06118051140501404101000 0x7e8c9f52d7c0c9d81a7a941e54487d4a1645848f60d52754aa085e80149fc457b111cc2a78099d844754c9d03e730ca3e438e4f635378c4d6292f8810ddc237206dbb6c6c4e1b2566b559c3566f56db5576a4e5a14166951664c639b1624c625b18560 10 1023 4 15 10 1023 18 262143
def cc_64_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x84210841e3781d17415854150541504c903400d3340d0304c024c9018c5114032084110401000400 0x27a429d53a71429a53aa24ba791e963fa38ce7d339b4ae65239811a516c935525b51955464933870c64029800861423840c62c29730860d32890fa00327e112185c79091f4447c1120424 10 1023 4 15 10 1023 18 262143
def cc_64_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x91482412082402010075ba17cb85c28d40994c26106802b1249048240cc6029140a04204 0x2e4a85f948bd6a178d02eca85c140b949b70916dc9ee0342be49f7491ead1edb142b5079645b2c0aa5714cb068b5d15ab5ab4d05ab38b76315ebcab5614eab25d3216a602251141a6273384c69094d083ca269b3c8ea709d50136 9 511 3 7 11 2047 19 524287
def cc_64_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb07602c0542a81486714e09c1382704a294110e2042184108200b656c0d81b03606c0d8162ac04c614401000 0x1c293b81266fa44dc2d98e533392866a40c5299aa8eb511b6b351d36a1a4577409abb044ce69b9ad1730ab4f05a750ad8f15b19ab62a459d0b4e815af49b4e05a730adbb16f6e2bed357d969fb0d1f5d2d68a56cf49d9690b28abe4956c829f8853b0ca3e11429b0b4e415af1a2dea36 11 2047 5 31 11 2047 19 524287
def cc_64_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8417c47257206c36825c65c05a15a05814e54e04c14824804424404213e23e03c13c03c03a12a82a0281014000000000 0x21844fe5b3d554e94d21454ce8eae636f455a885a8415b363ab88dbed4df24b7bd25f98f7c52fee49d042f1409f90177f151f444f5917d23dcc4aa4c457b113cb4cf1952f534ef933b43ced513ba54ec131e444e7153aa5ae995a805a7815ba03ee60c9002d110979354ffd6ff757fcd37eb45f89132e3ab68dbdd5af655fcd56f04ff093aeb4df95369f16a485777158f83f100df8c17 12 4095 5 31 10 1023 18 262143
def cc_64_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0b80c9b20c8320c0b00c0300b4e3a849f27c1d2741d06c9b04e130394e0344d0304751842408002 0x1a89447c4c904771e8dda695474372885e2309e35b6465388bcd9169522a9448f5c90ea31cd42372ec623f8a466d14a8da1f93c2f1084e4e0bc40139342f0f84e4c0b43a12c382f8684f1253222a24413c87a6d0c4d0941f870378582904d3a131ab3d2a2405e1a09e0ea32f5368369b054da08971143f0c06ef95020526be1302185e1509dd4a240134 10 1023 4 15 10 1023 19 524287
def cc_64_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xec7d83b0760ec1d8362ec0963282504a088700a00346642c81902c340c80100184300600538620c008800800 0xa1b5da11519f9508ca565fa369c9565305a45856a245a9f4569eb579e3569da579315b8c157831497e1419d13b9c1399b937611316c92b5f1275285a450569a9299a128999245da365e93696a4d989417d1316c12b5d1279804c8b1458aa56961565205a9725696a4e9295b8a157959295185a94a45940442a02f130279334f92b436ba3a7b9423784f2983f128372902f12027912356b12a6a938 11 2047 5 31 11 2047 20 1048575
def cc_64_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xd42f696a508ca308c2127c9d274158541324c1303d0f03c0781c0701c0701c025080200802008002 0x4fe3db0a5f5f49cc2178c827af02f659767d1ed915cb12a35d541b695ac5233005e3109c100f97c2d1784b590beb0139742f1704e5c07c5a0bd6e38ad46b578d2ac9c55534aa0685b0bc5813a3854a908950939fea1d3d29540b54dd46771fd31517ea66da4ad4e2523446460894a932932252128a3a49460928296d0125 10 1023 4 15 10 1023 19 524287
def cc_64_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9090743f382a281a111002 0x2d322da0443285e3609e8926bdd316ea56b348cc8178d4270503e6207c660bd0b4db1a6d41d3281265803c 8 255 3 7 10 1023 19 524287
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_64_11 (Nat.sub p 352)) (cc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_64_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_64_8 (Nat.sub p 256)) (cc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_64_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_64_5 (Nat.sub p 160)) (cc_64_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_64_2 (Nat.sub p 64)) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_64_0 : Nat → Nat := unpackHintV5 0x9b4153284253124a0069043d1f01a2f0f45e008b00d110521909432008640109832060d40a028080cfc051cd2b314865d850ba809631225a6c4a80c94808fd2c13ac01d4a00c2e8001800000 0x23a538e353088c7232d70638e38d4c0b8d310b638d38c78c13231c132d7234d3093972cb4c00070000000200b0000000100000070000000023008d72d70f2363530b0b8c0b5cb5c010d0c30c00c80030011357978000134d1d1c070000030c00010d0d4d4c000800002c000001c01c000000123000030c1420c38001543000030c30c000000c0802c00000555500004030000000001231c71c71c71c7 19 524287 8 255
def hc_64_1 : Nat → Nat := unpackHintV5 0xb68bada00b6802da00b680288527ca59f00274081b41c6b819a806688198c16608296e145a01956124b8a0d25c34008c0101c938700215070381c0c8182c0609818141203818000e 0x5cb4d04c8c1d34c24e5cb2d30001c0000000200000b0000001001c000070230000001e8c22c7238c3c5e38e38e30b23238b5e8e32d78e32d7081c8c0172cb5c014d4c1c00001c823535c25e0005d4d4c70000106347238c304e38e38c48e38d4e3 18 262143 8 255
def hc_64_2 : Nat → Nat := unpackHintV5 0xf90af606f306e51caf6caf00af00af008a4a89027c1a662c63065f085f00511c4e064b064806430a351c3500271c27002700152415000b140b00040e01060002 0xa8e38e3201c8c0b5cb5c0014d4c1c8007001c01d79780001753531c000508c7238d344c323078d8c48d078e38e3a8e3088c7108d1c8cb8c2c8c704078d8e31c 16 65535 7 127
def hc_64_3 : Nat → Nat := unpackHintV5 0xb18056280ac20352e56a44194701a890549a789280d2183a430047e0883cc0e91e99e343182462c04bd88178032ee0252cb071b40b330088de10c041b0681e1803c0006c0c0a830031200006 0x14b1c7833db6cf8f0d2c3430e31e326c70cfa0cf0e92c3430c20e0c394032cb2e326c0c00030c308d0020c38b2c4071c73c23cf80200f030830e0cf0c0c087873cf0005353072001c01c08d344c3234b5c48d8d74135d30938751c000700000b3cb3c800070000000000f3d72cb5c0100001c007230000000000f3cb2c23cf91c740007000003c08b2cb2c070000000003cf3cf1000b2cb2c00070000007230000a3807238d72d70f01e38cb8e30b0b078e3 19 524287 8 255
def hc_64_4 : Nat → Nat := unpackHintV5 0xdbc1db78036f006726cce4018b912e63152aa2964f10e9e21c01414247a484b93b9720028460450b869a088b481160016cc02d8002b30050060a0000d86816050220a0341006800080500010 0x2e3030c318d20c38b2d40070c71c71c06380c0b003001c70200aa000000000aa0c30c3008f3ea3cf830e0cf0c30c71c71c71c71c71c70c31cf3e1c780000f5d4d4c701c2307000030c34c10c3572cb4c00030042310001e38c31e32d7530c13878c1c1c070b0023cf8000000000400830e0cf0c000007072230070070000003007072c08cf3c2e1c78000000f50802a80080000aa0c30c30000022cf2cf8f3e808808c3d0d0e0c380c000f6cf6c008000003c0db0db000cf0c00301c0f3c023cf8000232c2c3d40c010230c30c050c38b2c00103c30db1232c07a1c0e4b 19 524287 8 255
def hc_64_5 : Nat → Nat := unpackHintV5 0xe4865c70238b0371006dd44db802b6e026d408cf0b9841a28e7a4f4289e4053309a5c0a44a6e87c190f009f72738c625c1588a2e0e52f152782a400379d06f0009a44120142400045030008a 0xb5d2d4e36307078e34b4b101c1d234630c364b5430d4c30d500c3500c30c3000c00000000555500000c30c35435654b543030c3015435555001418c0c3030c1c1c45051c7000418e35cb5c3c63538c2c8b238e302d72d70c0010d0c30c06300030234d5e5e00004d3535300000354c234830e5cb2d3100c0000c300004343535300063200000b000000000000000022a803c2c0000000002a800c4030c30c0088c00000000088c03e0f0b000c0d001c1c700b3cb3ea2233cf43430c31c700071cf3e3cf80b232c2cb3d4071c71c71c0b2383c3c01001c71231e8fa4b0d0c3830e500cb0c71c71c31c71c7 19 524287 8 255
def hc_64_6 : Nat → Nat := unpackHintV5 0xaf9854f8fa9e0150a329bc592b8c23e19416667fc30ff801ff003de207b00ce80e1cf013584669818d0829970a2c66854c408e9b10c11212064200481030d52d188222947c19398062c0000c 0x30c30c003000800c0002c001555418c00100c000000000008c3538d72d73cf4d8d4c38cb2d32e3538d0da6d234d8d72d2d4e3538d2d4cb07838d38b2d5434c0e30c82030c232cb3e8b3d430e343541a2cb500c3430d0d3428b2d50c3048c6318e32c30e932cb4cb54d44e34c2c0b00538e4c3530cb5cb5d1036d1030d41c1c30d348d34cb4d8c75e5e4d35d1134d1071c1c1d138d72d3936e5d34d34c1c1c30c30043435353063500e4db0e4cb2d35400703070700040701c701c70c35e0c3944c5110c307078c7 19 524287 8 255
def hc_64_7 : Nat → Nat := unpackHintV5 0xeb400e3042d6864d5808c6878c102caa0b89948692c348e0268b814734c27340070c146c4246c4006901a684066840062430624005fc145f0065f0005ec025246450c0c4f00e289341b8680e06c00070 0xb5e33d4c30d36d38a2cb3cf575d574105e35c2cb063a3cf2d73cf4b2d4f3cb02cb3cf2cb0a50c37df0c35560c30c355430c30c30d5f8d34c30c30c30d5471d31c7a5cfa4b0d0d30c34c30c4db033c30c1c1e434b3c3930d2c8e33e30c38cb8d4c3a60d63e0e36c6c0cf90d3c32e0e0e34b0d0c307070c30df638d74b4cb531f634c78d2d72d4c4d31d7a34c726db90575d34c2c2d34c07071e31c7070c33cb0c30c35cb2d74f0d0cf52cb4b54d4c3930e544d30b2cb0c70d71cb1c71d351d3071c1c70c30c3830e00000555500c00000c30c30000555500000c00000000c30c3000c0055550000c0000000 20 1048575 9 511
def hc_64_8 : Nat → Nat := unpackHintV5 0xce00a66d01b119297b46cbd8015e901aea05574c02b920a5c3032d9045500e49f0484a82823d0b90c09485a03426039eb140ea05c64c822e62012da2c9600645e291e3260d38f0399821543c0204500e01000038 0x5cb478e0c3a0c3975d5594f5555830c30e5c71c71d540c30b5cb5c30d511430c1c1c71d5cb5d578e33d48e38d78cb5e3128d50d4b555830e51520c38f3d55566353d55551511e0c30c3873c71c755a9aa3cf3cf6643434343aaa3c73c71c70d436aaa2cb2cb69a430d0cb4343aaa2c72c71c70d43aa000066434300080000000413cb2cfaa3cf3cfaa0cf03034343a07071c78d4e3aa6a3cf3cf69a430d0cf4343aaa3c73c71c70d43aa000066434300080000000aaaa3cf3cf5a663430d0cf4343563ea8baa2aa883aaa8f1cf1c71c350e2871e8a830e0c313170c355d744550c307071c70c30c30c36543550c30c35cb2d75451550d2d8d55555430c30c30d71cb1d11d1471d54ba2cb3cf52cf2c172cf3c23cf850f3cb2cb2cf3cb2c4c4d34cf3c1c1c71c30d72d0d2d54d830e51312c30c1c1c30cb2c30c33cf0cb2cb2cb433d3c34b6352cb53530e2cb2cf0e54b0b2cb2c2cb0c73cf3c32c72c71c74d472c1c72c1c70c3830e0b2c2cb50d52d4450c30707543560c30c30c352c30c30d4542cb2cb50d555552d550c30c30c3454472c72c71c755078cf5cb0c34d04c 21 2097151 9 511
def hc_64_9 : Nat → Nat := unpackHintV5 0xdbc266ca0a3480e99d038cc61166200b188c588022b368555b2028a919374708d4734361a1f9110ce97060a352d01a967804aa04e4945e21a180f80a8608dc2c61f15109058284190980b8080072a80001c00000 0x2cf2e80b2cb2cb503cf0b5e5cf8cb5cf883cf2c2c3db2cb535307073cf2d78f2e9b8e32c8d75d32c54d74d3938502cb134c71c1c1cb138d7572cf2cf3e5db3e00f00b232cb02cb2cf3d72cb5d755c01c1c0701c071c071c001c1c0f3cf3cb2cb2c023cf92cb4000f00000b2cb2c00000f3cf3cb2cb2c000f0000000030c30c0030015554000300000000b2cb2c00f02c8c00803c02c00f3cf3cb2cb2c00001003c000000000003cf2cb4e3cf9044c2cb3cf0707003c2cb2cb000000003cf3cf002cb2cb002e2cf2cb2e2cb3cb2cb00f0f3cf0b2cb2c02c8cf3cf3cb4b2cb4b2cb2cb2c01cf0f1c2c1c701cb1c701c0700070708f8f3cf00002c8d4d4cf000f00f2e3cf80232c2c2d753533c0004135d30939754c0000002cf2cf00000b232000003cf5cb2d7000040000000000000222cf2cf5a3cf4494f50707a080aa000000005500550066a953d2d6a95143cf3cf6635555553d56aa91471d453c73c71c7558e33d34b5c34c34e38d344c320c3a0c38f3d98d690cf430d0d0c35430c32c30c30c0db0c30caa0c30c3873c71c70d430c0c30c0c7830e830e2cb2cb555555830c30e2c72c71c7555707830e830e55cf3d75c192d3d552d55430d71cf1c1c1e33d 21 2097151 9 511
def hc_64_10 : Nat → Nat := unpackHintV5 0xf620374934348ae197c64c2a4a61201b048256b4b8ab254519202738c91651c84e323b03b9bb0e8cf0745b06428c261211286c5222fe3214b1a08c8c83b458172340543280e8dc06806024080120000900000024 0x8e8b2ea3cf8b2cb2cb8f3e0c38b2cb4d3873cf3e2c72c71c74c71cb2cfaa8b2e8b8cb2c2cb2c8f3e2cb2cb2c32d2cb0d2cb830e0c32c30cb0c32c1c72c1c7873cf3e2c72c71c70c31ea80002a830c30c00200000002a08f03ea8f2cb3e830d0d0c30c30e81c1c71e32d78eaaaa8f2cb3ea830c30c30c30c30eaa8f1cb1c71c30c30eaaa8f2cb3ea830c30c30c30eaa8f1cb1c71c30c30eaa955556a8f2cb3d56aa8f1cb1d5471ea820000000002a830c30c0002aa8b8ea8faa8f2cb3ea8a8aa0c30c30c39a0e9a0c30c3aaa3c72c78a1c7a2871c30c30c202a800000002a80030c30c000aaa8f8ba223a0a6cf0f2aa60e6830c30c0c3028882871c8a07070003033cf8f3e008cb000b03d753533c0000c30d308d10c3572cb4c00400c0008f3e22300003c1b000b0020c3833c3000c00400000000000003cf823d75cb2cf8e2c3e83d753533cf1c707070c30d3530d8d0572cb4c68380d30c30c7070700f2db6cf2db8f3eaa8088c3cf3c0d6db0d6e0c3833c3030c30071c071c07081c1c000c1ea80002a830c30c00200000002a802002a830c30c00200000002a80002a830c30c00200000002a802001555400200000002a8000002000002a830c30c0002a80088c0080f002c002a830c30c000030402000000001c00008f8d78b2e082cb3c8cf14f5cf3c2350e3a2cb433cf 21 2097151 9 511
def hc_64_11 : Nat → Nat := unpackHintV5 0x9dc6c914646ed144196a33074200981d81404cc6028120280000014 0x20a8b0b2a8b2d0d0c30c30e81c1c202a800000002a80030c30c02aa2e3aaa2eaaa282cb2cbaa9839a0c30c30c30c30c3aaa8a1c7a28b1cb1c71c30c30e8b8cb2e8b2cbaa3cf8f2cb3cf3db3c3cf3c830e0c32c30cf0d3cf0d3c30e1cf3cf8f1cb1cf071cf071c71c30c73c3c882cb3cf2cb535307073cf1c75555830e55830e2cb2cb55830c30e2c72c71c72d307a2e0c383432c3432c34c34d0c35683913032c30d30c31c1c1c32e34b4c7 20 1048575 9 511
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_64_11 (Nat.sub p 352)) (hc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_64_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_64_8 (Nat.sub p 256)) (hc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_64_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_64_5 (Nat.sub p 160)) (hc_64_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_64 : Nat → Nat × Nat := unpackForestF 0xb4245b404400b4f00b4baea5dae95cb1936ae951af12fb003caf127af017ae95000b47aa238aa235ac02fac027aa234aa138aa134aa03400b43a904400a4fa7a4ea792900a4ba6351a615100a47a324ca3244a3128a3124a302400a439bc5a9fb5d9f951a012da01259f9509bc569bb579bb569ba579b93b9c9569b9399b93700a3f99929999289992400a3b981419804c00a3795a5695a4e961569592900a3394245940440094f92b4f92b430094b8a35c912358a3518ea3b8f84c8ea378e8378a3508a25d8cb6c8c9388a23f8aa6c8aa548a9288a233009478594c859448593c859368682f8682785934858140094384a350093f839468234d821368212e0093b8124d009378013471b5b7f16c71b5771b4d7d94d71b457ca3d71a447195a719577a2457a23d719567934c78a547193f77a4c76254769447604c719377325a732567303e7385473032719367235471817009336fa4e6fa4c6fa440092f6145b6e16c61457613576134f613476125a693516a23a6a236693506915d61256681356124e6634d66345661566124261157611566114f62c5662b5662a456114e61147611420092b5ab425f9485aa4f5db505db405d9505aa475ba4d5ba455b93d5a9425a83c0092755c5b5916c55c57583455595656c5656b565594e5592e009230084f4c24b4c247531394c23f521294c2335034d5083c501364c1334e2424e14e4e1424c12b4d14e4c1234c0460084a49351491514996c49954491330084748029392433913d3913739135458293912f4483e390433c3524305c3c2453c23d3c1523c05e408243c0523c0453e2323e12d3e0323c0443ca503c9443c026390233b044399323983e398323901b00846353563515b3736c3515735a5635956351390083f3414100837332541cc5f1cc5b30a6c3096c309601cc572e3442e2442e1482e1441cc531ca562c9502bc562bb561ca4e2aa541c95f1c95b2846c284602826c1c9572595c2595425944259341c95324a441c94f2335c231341c94b2225c1c9472124c1fa541f9441f9341c9431eb501d2561d24e1d1561c9290082f1bb580645f0645b193601916c191600645716b4816a441694816944064530635a14c5e14a560634213b580615f0615b1146c1146011360061570e95c0e9540e94c0e934061530db480614f0c94c0614b0b3500b3400614708a54099440894c089340614306a5e06a460695606131008270245b0496c024570215602c5602b560214e0081f01242008170001f 9 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 4 15 bds_64 362 (dagTraceF m_64 s_64 8 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 4 15 362 bds_64 (dagTraceF m_64 s_64 8 f_64) (cur_64 0) (nh_64 0) s_64 8 = true := by decide +kernel
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
theorem nb_64_11 : treeBlockF 352 362 ch_64 = true := by decide +kernel
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
theorem nj_64_11 : ∀ i, 0 ≤ i → i < 362 → ch_64 i = true := block_join nj_64_10 (fun _ h1 h2 => treeBlockF_at nb_64_11 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 362 → ch_64 i = true := nj_64_11
theorem lb_64 : LowerBin m_64 s_64 g_64 9 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_31 (kn_cons lb_34 (kn_cons lb_6 (kn_cons lb_18 (kn_cons lb_33 (kn_cons lb_5 (kn_cons lb_30 (kn_cons lb_28 (kn_cons lb_52 (kn_cons lb_13 (kn_nil)))))))))))) rc_64 nc_64 (by decide +kernel)

def g_65 : Nat := 0x115155713371f7f
def ep_65 : Nat := 0x12220a280000144200000c4800140042002400600104040202040e0801101002133210200115155410041040
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_58, s_58, 8, g_58), (m_57, s_57, 8, g_57), (m_62, s_62, 9, g_62), (m_61, s_61, 9, g_61), (m_59, s_59, 8, g_59), (m_64, s_64, 9, g_64), (m_63, s_63, 9, g_63), (m_45, s_45, 5, g_45), (m_51, s_51, 5, g_51), (m_56, s_56, 8, g_56), (m_8, s_8, 4, g_8), (m_60, s_60, 7, g_60), (m_36, s_36, 5, g_36), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27)]
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9209209208288208018007e17e07c17c07a15b05a05815805425405404e34e04a24a04624604604604603e4326038001 0x10d6e105620fb6f0f36e0eb670e3620b25d0a2550d4700c4600b4600a4502156f2056b1e5671cd631b46e1a46b19c6316c621545e13c5b11c530dc520ca6f0ba670aa5f09a5708a640326c07a5406b7c0627c02a5c01a5c052540445901c510356a02d660246e01c620856f0756b05d6704d6303a6e0125ef645ff3c5bee457e2453db35fd8b5bd6357d0353c7b4fc534bc2b47bbb43a4a5f9da5b95257862536424f5d24b51a473a2432c23f2223b0923700a330003f 12 4095 5 31 11 2047 20 1048575
def cc_65_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x8020074dd0741856018054d5048d114411044110440982409018c6018042100400c4120400100000 0xfe38fd1c3d4f98c70823077161c8a1d254d6b77116774ab4d6a9ab16ad724ac59569c6b0e0d79c6a4d26d6132de0eae06d646ea22f569169af5435c95a24d5ea4ae51355 10 1023 4 15 11 2047 17 131071
def cc_65_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42d0acab0ac28376dd0705c06c5b06c1836018054d504c9304c1304c0f4384b311c400882000800 0x2f454badb2dc6c56db2d35ce55bf856bdb59f5563d0dbb2b5ec49befa67b897eca578a8d6ba64aa9529b7ca49f23246a0d52425c9e9526c59911465c6f951ba4c67911892c708d59dac625114ab56fa95ae8d679d58e626e8e97a2a46871a10c50651c20c58 10 1023 4 15 11 2047 18 262143
def cc_65_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xad6b0ac2b0a0e80a0280a02355f170585605455054123481203ccf0294a028055140500c8300c003 0x838d305186062cbe4517f686fb1b9f2313da6e79ad6f1188a2293bb6a766a5415ae72b1cd46f978d72719e4231c645f898a708db9f9373d25e7548ce6d91c5aa37b7c6e4f88c8d5b22a3335c6b6a8d31659a28b1a6d604ca6e9559e37334625d4bab4954ad22b2464636f8c31f0ddbe3036c 10 1023 4 15 11 2047 19 524287
def cc_65_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe9e8ccc8c1c0c0aba8a8a88c88887a7871706260603d383130290c0808080801 0x27d2e4f4559d6a9049f1f12e4da6499688ee95261224b570928fb2adf2513e4947e914891e9923abf46b548b8fd14d11fd3f3b254284890c9521922c435b876af0a959ed2740364 8 255 3 7 11 2047 19 524287
def cc_65_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xbcaf0bc2e1a1a2688211842107c9f0785e0781e0781a4681735c1704d1304c13040c5b1405001400 0x60344bf4897918b1a37e246bc18cf7d18ef5375da46b66d362d86a936d32657c49b4e916e2b45b670b56d9675c2c7385836caf6b95c8d2b23715a455b47b555c1f2b054c687b4b94f5c29ab052c70b9ac56edbed1b5d9367ad6c756d76a137d22677a4bab28fc4d1bd1455a16a9069f2052a3ca46 10 1023 4 15 11 2047 19 524287
def cc_65_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xd41a8312620c03802d1da0b4150ea0540a81502624c098111220421840f0c4d0800c21802084008000800000 0x6fd626f46b6eb422f23d6db5c6d4542eb6c6ca346bd686b47c3e4606a45a69c566936d68b6567d703e4706746c3da7c6623465b533da6e6524685d6b8556384c6f8246e80c6b804677e4637c4627ab6f78b6b76b6774b637435f72b5371b4f1534d70b4b703476e3456c3436aa6f6826e66a6764a622e23f0aa3763a6462a4461d706127c 11 2047 5 31 11 2047 20 1048575
def cc_65_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x84c21d8e8743a17cb85c2a950a85424d2090481ecf0783c18cb258288d0601b088240200 0x3fe367dd7cfeae9af1b3f5223ec6efb8db0317bea2efca46a748bef1a3da327a35cf36a9e48d3c23e77c70ee4f9d8db3adae75354e4489ced939abf6ec54cb4e5b28d05a3671358e4489b6d138a2e6d340 9 511 3 7 11 2047 19 524287
def cc_65_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xf83b3ec3b0ec374d8742c4f10c4310c42b6ac2b0ac2746f17450d134411044110224711c03400c00 0x8fb44872548f2448e6708db6c8d26c8925c6625e65b6e8c24440c593e4513da4e8ad6e8a5623ec6e3e46289b5d893551ac628845287b628735a9456f935639246f914639045f8ec5b8cc578bc5364b5e8b26e88a5e86a468457c3e45c6f3558124483d7c3e4507ea4481c787dc706927c3e56e7dd6d8446983c61733436b26d672658305a828567fc6481d7c67c6c3e45c812443ec7c7f46068a6c 10 1023 4 15 11 2047 20 1048575
def cc_65_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0300bc696a42908621078de0745d0741b26c1a1681a06817332cc024c9018c601445008c2000800 0x9ec52a3c5fa2c5ba14579fc539f25e9e24699b59973519d34b9cb4767a5d52a553e24d53a459bc591ba5530a3d9ac7c99d709937c985709757096b7c962349c4619b36d9a34f98b4b97b4795b438b26d66a4f522472fa3f0ba3794b643ea648aa5c93b548a26c3e25c92b6491b4487a541aa4489a6c90a54 10 1023 4 15 11 2047 20 1048575
def cc_65_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xc41882e1dc0b43682a1d40a8140a80500a0128e504a094110e20440804368600a11402044008008410020002 0xaf461aeb523223dadb6cad46431b7caca34abc6cab464aa36ca9b64a9234a8568a7d60a725ca636ca5b64bb46fbac63b9c5fb8c5bb7459b6c57b4c537c451b436fb3b63b2b5f1b35db135bafb57ae355ac353aab4fa8b4ba6b47a53436aa4f6824e54247422423123f0ca37a4254a3244a2670a1a6ca0b44a0244 11 2047 5 31 11 2047 20 1048575
def cc_65_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e11c20b4107e4fc1c3adb5469cd38234442754e81d02ec4d098121240390688b216020c4007108610020004 0xc0469bfc61bf459a625dbea5545a43bdc6e15a45a636ebcb6214352a0a6a962666ca5e45252c1d6bc0d63be36ebd35ea526f9fa6b95a678ba6372a5f44a53bc2353e56cb8468ba254b7d683e460b52445557c3e56cb9468ba254b6454b956c7d560b2369b0b656a25cb856eb7d623e45e7d45d6ba5d54a5540d7cb5c50b035569a4cb646c7d568b5d646b47cb5244b3254aec64aca340d57cb1b68b3254adb54b2569b1c6c44252b0c59b0455ad35043a42 11 2047 4 15 11 2047 20 1048575
def cc_65_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x8018008008008008008007277017006a36816806806044104003c23c03442862802042001840a70a0043040002000000 0xcdd7cce469cdc61aba5dcd25547243cc85acc056bdc7cbdc6ebf45ecaa4515a54abc6ec8c627225e46a52cfd6bcf563cec6fcbc6ecb467ca462aaa6fa3a6b9a267902637425f462531524dc9a4bc9247c8245aa25dc7255aa36ec6362a926e8fa62c6b6ea8a6fa2a6b98a678ea63c5a35a22698e261a7a4dc4a45c3d6ea7d62a726e8da62c4562bd35da6a6fa126b97a678ca63c325dc2454c037cbf354c1454bfb7c 12 4095 5 31 11 2047 20 1048575
def cc_65_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xb00a84a61a41a40a21a209a47b07a07627606e46266205a45a05244474403e33e03a234334034034026726018702b001 0xe056edfd627ba4ddf245bf57c1ba64dd4617bc59dc451b326e92a62e1c6fe1463e0c5bdec59de457ca451b426f922631b25ddda5bdca57dba557aa4f6324b5ba474d2437a24ddaa457a35ed9b527925e4ca52da35e78a5f6225b5a2574ba53d923561a594b25177a4dd8245d746977c617724e4aa42d7c61d3b6dd6a6d76a4f60a4b5924749a43d5c64bdb64d335cd4c54d2b6cbf4591ba5549243d356ed2d62bdc6e7625d57a5575a4dd22451ab6275b5ed1352aca6e91a626025a57256d556fd4563d3b6ed1b5eb3a6f9126374a5f5f25b56a5748253d0a35ce57c 12 4095 5 31 11 2047 20 1048575
def cc_65_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9e49e08e88838618418218207857807427407407216856045e15a2562468460422420420401346058021001000000000 0xf1a5ff0a5bf0257efa53f2b6df226def26ceea6036a3f28a3b1e23705a33cdc7cdfc6ced358eab44ed45cea340d4b62c13524f253eba4d3623deab4ce9234e9344ea454bfb7cd2b6ce9a38e8a3483c7cb7c6ce72587ca54e5244e735c53a547ca4ce4a40b526e93a627ea5e4ea527ca4e3e24d2823a1d236e524ce3a34e3a44e4b544127c8a26c3e25ce424ce3244e136fd4363cf35fc0b53edb4fca34decb4bec347eb345e8343baa6f932638525f4e253e7a4f7c24de6a4be6247e5a45e2a433523f2723b1ca3704a33e0468dfd68 12 4095 5 31 11 2047 20 1048575
def cc_65_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x2e0ace7472da2681644907b1c061090110400100000 0xbdd62d5b62f7a5d3e56e3ed62ba26e94a62f5d6ee1b6fd5363f7355bb26f94263f6a553923f2b23b21237082333e24d53a45bf452c235251253f524d3e45e40c528125e50a52f5c5ecfb5fc1b53f4b4585a5f50253f42453823f2a23b2023707233f32653723e29a3a1ea3606a32f1268f136c 10 1023 4 15 11 2047 20 1048575
def cur_65 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_65_15 (Nat.sub p 480)) (cc_65_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (cc_65_13 (Nat.sub p 416)) (cc_65_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 448)) (Bool.rec (Bool.rec (cc_65_11 (Nat.sub p 352)) (cc_65_10 (Nat.sub p 320)) (Nat.blt p 352)) (Bool.rec (cc_65_9 (Nat.sub p 288)) (cc_65_8 (Nat.sub p 256)) (Nat.blt p 288)) (Nat.blt p 320)) (Nat.blt p 384)) (Bool.rec (Bool.rec (Bool.rec (cc_65_7 (Nat.sub p 224)) (cc_65_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_65_5 (Nat.sub p 160)) (cc_65_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_65_3 (Nat.sub p 96)) (cc_65_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_65_1 (Nat.sub p 32)) (cc_65_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 256)
def hc_65_0 : Nat → Nat := unpackHintV5 0xcb11dec5a95abe29e0b781aab12198a58ae69f119e939ade8d698c81e2e27b699e6fe2e26a616064c1685c4a1e56d95c4e8a1449594c43a16e3b2a1e3551762d420427b9622231621d194618413611f9920c895c07016202c1100000b0000000 0x175d71d75c75d71c75d71c75d35c5c5d305d305c1c5d5d5d355d355d1d17c2cf2cf2cb3cf2cb3cf2c71cf0f2c4f2da0e83a0c3a0c3838303843983836db6c71d31db8e36db6e79d3131f7db7d76db6db6e79df7c5f1b4e7536d5f7c5f4b3cb3cb3cb3e0e0ea0e0c75c75d7171707175d75d75c1755d5d05d5d5d1d17c057575c14b3cb3cb1c73c3cb0b2cf5cf3cb5cb2cf3d3cb60e0e0e0c0e2835c30e5e830d0e60e0c79c79e323238c1e3276db9e38e3058d09d9d9d1d18c059c52cf2cf2c71cf0f2c2cb3cf2cb3cf4f2d83838383038a0c3a0c343983834d35d34d34d3134d34f31313134d5005d75d7145354d54505735352cf2cf2cf2cf0f2c2cf2cf5583838383038835e5c355838355f6db7d31d39d31d34d34d36d36d34d35d34d34e34d304d34db004d34c74c74e74c4c4d31304d34e304c4c555cd4d54d535500141ccb3cb3cb2cf3cb2cf3cb3cb3cb2cf3cb2cf3c3cb14f560e0e830e830e0e0e830e830c0e15660e0d34d34d39d34c4d31313134df5d75d71453573734cd4cccd573732cf2cf2cf2cf0f2c2cf2cf735cd83838383038837e7c35583835531d34d31d39db6db6d34d38c0134d36d34c134d36d36d34d36d34d34c74c74e74d34e304d31304c4c4c4c554d535573554d001414b2cf3cb2cf3cb3cb3cb3cb3cb2cf3cb2cf3c3cb154b6830e830e0e0e0e0e830e830c0e1560e0d37d34d34d313134c4d34d3cc7df7df4d35400514d551d1415cd4d4b3cb3cb3cb3c3cb0b3cb3d560e0e0e0c0e20e0d560e0c77c77d37d34d36d34d54d34db4d34df4d31c74c71c74e74d34d38d31c071c71c013131307134c4c134d38c1553555734754740050732cf2cf2c71cf2cb3cf2cb3cf2cb3cf2cb3cf0f2c552d83838383a0c3a0c3a0c3a0c30385583831c71c71df4c4c1d3071c7df7df1c79c51737351d335333355cdccb3cb3c71c71c3cb0b3cb3d735ce0e0e0e0c0e20e0dcd7360e0c71c76c71c77c71c71d54d34db4d34d71c74e3001c71c71c701c71c71c71c71c74d313071d38c071c1c070715554d4751d55cc005052cf2cf1cb1c71c71cf1c71c72cb3cf2cb3cf0f2c53d58383a0c3a0c38383a0c3a0c303855983838db8db8c78c78c8c8c8c55540050732cf2cf2cf2cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983834d3000076c71c7001c700000000055555555002cf2cf2cb3cf2cb3cf1c71c700558383a0c3a0c38383005583831df1c76c7cc71c71c71c70000000055555555000731701b0070700070001c01c0010b3cb3c71c73c72c71c71c71c015403c2c20e0e831c30e1e830e0e0c015400c820e0c7075c0071c134c000000000015555555400b3cb3cb1c73cb2cf3cb2cf3c01560e0e0e0e830e830c01560e0c76c7cc71db6c71c76df6c0000000155555554001cc5c06c09c0070701b1b0017000010b3cb3cb1c73cb2cf3cb2cf3c015403c2c20e0e0e0e830e830c015400c820e0d35475471c1c00000004c13013007007000b3cb3cb3cb3c71c71c0003c2c20e0e0e0e0e0c0000c820e0d34c00071c00071c1c000000011d1d55555550002cb3cf2cb3cf2cf2cf1c71c70055a0c3a0c383838383005583831c76c71c71c71c71db1f30000000047555555554001cc1c000707001701b007001c1c001072c71c71c73cb3cb3c71c71c015403c2c2830e830e0e0e0e0c015400c820e0c76db1db071c00134c0000000000155555554001cc2cf2cf2c71cf2cb3cf2cb3cf005583838383a0c3a0c3005583831c76db1db1f31c71db6db0000000055555555000731701b01f0070170007c000042cf2cf2c71cf2cb3cf2cb3cf005500f0b083838383a0c3a0c300550032083831d7075d7001c704d34c000000015555555400b3cb3cb1c73cb2cf3cb2cf3c01560e0e0e0e830e830c01560e0c05d75d74c75d71d3000000000555555555002cf2cf2cb3cf2cb3cf2cf2cf00558383a0c3a0c38383005583836d77f31b6d35c71c74d700000000001555555400b3cb3cb3cb3cb3cb3c01560e0e0e0e0e0c01560e0c71db1c77db5d3135c00000011d5555555001c71c72cf2cf2cf2cf0055838383838383005583834d34c5d75f31d75d70001d71c0000000015555555400b3cb3cb2cf3cb2cf3cb1c73c01560e0e835c30e5e830e0e0c01560e0c75d71d7135d34d74c000000015555555400b3cb3cb1c73cb2cf3cb2cf3c01560e0e0e0e830e830c01560e0c79c77df4db7db4c0000000000555555555002cf2cf2c71cf2cb3cf2cb3cf005583838383a0c3a0c3005583830000555500073006c000700042cf2cf2cf2cf005500f0b08383838300550032083832cf2cf2cf2cf2cf2cf2cf2cf83838383838383838383 24 16777215 10 1023
def hc_65_1 : Nat → Nat := unpackHintV5 0xe79a00df720ad3baeecc69d4c481fab7eb26b021f2a9b99aa339a09b81ee90c2b08582d07f41907799ea7001e66869e661b1ae5ab9be52a2064c399a45b9a03fc17e3859da2d82b627897e2538941ef9901422b612b85a0c918a0519de000146 0x71c71c71db1f36c6c1c1c6d36db6db6d71c71c71c71c7051d06d6d1d1d0470014711d4b3cb3c71c71c3cb0b2cf3cb2cf3d3cb60e0e0e0c0e2830e830d0e60e0d3534c7471c71c71c71c71c071c04d34db4d34d71c71c71c71c71c4c134c13130707152cf2cf2cf2cf1c71c72cb3cf2cb3cf0f2c838383838383a0c3a0c303883831c76c71c71c71c71db1f31c74e31c71c71c71c71c76d76db6db6d71c71c71c71c71d301c706c6c1c1c5471d351c74756d6d1d1d00141cc72c71c71c73cb3cb3c71c71cb2cf3cb2cf3c3cb13cb6830e830e0e0e0e0e830e830c0e10e60e0c76c77df1b1f071f1db6db4c71df6c71c71db6c15f41f5b5f4745f015f14b3cb3cb1c73c3cb0b2cf3cb2cf3d3cb60e0e0e0c0e2830e830d0e60e0c76c77c7534d3474d34d34d34d74f34d31d31d39d3cd34c134d304c4c4c1c4d304c4ccd52cf2cf2c71cf2cf2cf2cb3cb2cf0f2c838383838383a0e8303883831c76db1db1f31c71db6db7d76db7db6db7d77df7c71df1c71df9df7d74e37df7df7d38df5df7c6c7c1c7d31f07df4e3055f5b5f475f4d7d5f7d3500141ccb3cb3cb1c73cb2cf3cb2cf3cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830e830e830c0e10e60e0c75d71d75d75d71c71d75d34d34c4c4d3074c4d304d304d4d4d3474d4d354d3514c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c3038439838305545d75d74c74d34c74e744c504d304c4c5355535545530b3cb3cb2cf3cb2cf3cb3cb3c3cb1560e0e830e830e0e0c0e1560e0d78d75d75d31d75c74e34c4c4e38d3131353538d3534530b3cb3cb2cf3cb2cf3cb3cb3c3cb13cb60e0e830e830e0e0c0e10e60e0d75d75d75d34c4d31313134d35d75c75c75d7054d04d3534d4d4d14c054c52cf2cf2cf2cf0f2c2cb3cf2cb3cf4f2d83838383038a0d70c397a0c343983836db6db6df4db4e34db4db6db4df7d37df4d3134c4c4c5534d36df6c76c76db6df6c1534134d4d353534005073054c52cf2cf2cf2cf2cb3cf2cb3cf0f2c2cb3cf2cb3cf4f2d83838383a0c3a0c3038a0c3a0c343983837db9db7df4d74e36db4db4e34df7d74d77d34c4d31313154d34df9df1df1df7db6db6c1534134d4d353534005073054c52cf2cf2cf2cf2cb3cf2cb3cf0f2c2cb3cf2cb3cf4f2d83838383a0c3a0c3038a0df0c39fa0c343983835d75d707174c5d3171c71c75d75d715c5d1d5d3574d16c15d2c71cf2cf2cf0f2c2cf2cf4f2d83838383038835e5c343983835d75d707174c5d75d3cc5d71c71c75f35d74c71d71d71d715c5d1d5d3575d74f345f0574b1c73cb3cb3c3cb0b3cb3d3cb60e0e0e0c0e20d7970d0e60e0c75d71d75d75d71c71d74d75d75c5c5c1c5d305d305d5d5d1d5d355d3517c2cf2cf2cb1c72cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983835d75d75d75d7177c5c5c5d75d75d75d75d75c1577c175d5df575744301577d4b3cb3cb3cb3c3cb0b2cf3cb2cf3d3cb430e0c30c30c0c32a90c3430c30d75d75d75d75c5df17172aaa8a175d75d75d75d75d7055df0a0c35d7577d5d5d1899055df52cf2cf2cf2cf0f2caa2cb3cf2cb3cf4f2d5d75d75e31b8c7c5c5e38d75c75c75c15f4175b5f5745f015f14b3cb3cb3cb3c3cb0b2cf3cb2cf3d3cb60e0e0e0c0e2830c3a830d0e60e0d34d31d75c75d71c75d71c75d74d3134c4d304d304c1c4d3534d4d354d354d1d14c2cf2cf2cb3cf2cb3cf2c71cf0f2c4f2d8383a0d70c397a0c3838303843983831df1df4d34db4d34d705544c4c41c501c705553555345530b3cb3cb1c73cb2cf3cb2cf3c3cb1560e0e0e0e830e830c0e1560e0c79c77df4db7db4e38e34c4c4c1c4e38d3535347538c530b3cb3cb1c73cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c71db1df4d34c76c77c76c76c71c7144d31db7c71c71c7141c71c76db1db7c71c74d34c711111cf2c72cf2cf838383831c71c71df4c4c1d3071c7d79db9db7d71c74c14741353474d1c7447014714b3cb3c71c71c3cb0b2cf3cb2cf3d3cb60e0e0e0c0e2830e830d0e60e0c71c71c77d35df4e37d71c74e31c71c71c74c4c1d3071c5477c71c76c71c71c71e31c14741353474d1c74005073051c52cf2cf1c71c72cb3cf2cb3cf0f2c1c71cf1cb1c74f2d83838383a0c3a0c3038a0c3a0c343983836db6df7d34d34d34df6df1c76c76c51b7df6db6db6d34c5071c76df5db7df6db6d34d34c4444b3cb3cb3cb3e0e0e0e0c71db1f34db6c71c71c7140041d4b3cb3e0e0df9df7df4d34d34d39df9c71df1df145df5db6e76d74d3141c71db6db7e75df5d34d34c04444b3cb3cb3cb3e7c30dfa0e0e0c77e71df7d38df4e37d38d38c71c71d38d313134c1d3157df9db9db7df4d34c71c71c15341353534d1d34005073054c52cf2cf2c71cf2cb3cf2cb3cf0f2c2cb3cf2cb3cf4f2d83838383a0c3a0c3038a0c3a0c343983834d34c77df1c77d3cc71cb2c77c77c6c1c7074c7db6db6df1c711c7d6d1c7474d11c11d2cf2cf1c71c70f2c2cf2cf4f2d8383831e1c3038838343983831c71df1b1f4c7df7d3cc7df6db6db9f37df4db6df6e36df17c7d6d7d35f7df4f345f05f4b3cb3cb3cb3c3cb0b3cb3d3cb60e0e0e0c0e20e0d0e60e0df7df9df7df7c71e31df4d34c4c7df6e79db5df5db6db7df17c4d4d7df17d2cf2cf2cf2cfa83838383 24 16777215 10 1023
def hc_65_2 : Nat → Nat := unpackHintV5 0xcfd95aca695cc18a38bc614ab70956ae8222aa3912a419889ae24e94c1888bda3a8609747fa19a76aa3e7159546b298c62323e5be9925591965171084ae9a246d90440c1863a998a35e12e3009762b612a23e1e017b30c1031e00452f8000114 0x4d34d31df1df10001309c01cd5cc33337301cdcd04b3cb3cb3cb3cb1c73c01735ce0e0e0e0e0e0c01560e0d34d34df7df7c14000000cc4c0014d551d15cd4d400b3cb3cb2cf2cb3cb3cb3c01560e0e0e0e0e0c01560e0c77c77d37d34d36d34d5000000013007c06c09c007070132300070700014d555cd1d51d0730004b3cb3cb1c73cb2cf3cb2cf3c0003c2c14f560e0e0e0e830e830c0000c81560e0c71c71d34d34c400000704c55734737300cccc12cf2cf1c71c72cf2cf03c055838383838383005583831c71c77df7df1c79c0000001551d7351cdcc33330b3cb3c72c71c71cb3cb3c01560e0e0e0e0e0c01560e0c71c76c71c77c71c71d5000700000005c06c01c0007070007001c1c00554751d55cc1cc0012cf2cf1cb1c71c71cf1c71c70000f0b0558383a0c3a0c3838300003205583830000006c0007001541cc000b3cb3cb3cb3c0003c2c13cb60e0e0e0c0000c810e60e0df5d5551c71d5471d5f1b071c1f4c070715541515450b3cb3cb2cf3cb2cf3c71c71c3cb1560e0e830e830e0e0c0e1560e0c77c71db1f31c71c71c71df1b071c074c07071555555541cd415d56d51d1d551d554754755f402cf2cf1c71cf1cb1c71c71c70f2c5554f4b58383a0c70c387a0c38383038555436583831d1d7551c755d75555c5c5c1c5d305d3055555054142cf2cf2c71cf2cb3cf2cb3cf0f2c5583838383a0c3a0c30385583831db1f31c76db1c71db7db6c6c7c1c6d306d3055555555073505755b56754755b5b55575559d00b3cb3cb1c73cb2cf3cb2cf3c3cb15553d2d60e0e0e0e830e830c0e15550d960e0d35475471d1d301c1313070714d5755b5475475534b3cb3cb3cb3c71c71c3cb153d2d60e0e0e0e0e0c0e150d960e0db6d55471d55471d1df4c071c1b1b070711d1d14055550502cb3cf2cb3cf2cf2cf1c71c70f2c55a0c3a0c3838383830385583831c76c71c71c71c71db1f31d301c706c6c1c1c475555555541cd411d554747555755b547547550072c71c71c73cb3cb3c71c71c3cb15553d2d6830e830e0e0e0e0c0e15550d960e0c76c7475535531313071304c15d559d554d534b3cb3cb1c73cb3cb3c3cb154b60e0e0e0e0e0c0e15660e0c76c7471d555b6d555f1b1f071f4c1f4c155554150550b3cb3cb1c73cb2cf3cb2cf3c3cb1560e0e0e0e830e830c0e1560e0c71db6c76c7cc71c76db6df1b1f071f4c1f4c155555557d5073505755b5675475575557d555f402cf2cf2c71cf2cb3cf2cb3cf0f2c5554f4b583838383a0c3a0c3038555436583831d7475d7551c755d75d7171707174c174c155555555450b3cb3cb1c73cb2cf3cb2cf3c3cb1560e0e0e0e830e830c0e1560e0d55d75d75c75d71d75e31b8c5e307e307c5c555545055142cf2cf2cb3cf2cb3cf2cf2cf0f2c558383a0c3a0c383830385583837df9df51d6e79db5df5db6db54c4c7df7c7c555542cf2cf2cf2cf9f0c37e8383835d75d5d71d75d5471d5717174c174c170715555555450b3cb3cb2cf3cb2cf3cb1c73c3cb1560e0e835c30e5e830e0e0c0e1560e0db6c755b9db7d76db6db6e79d53131f7df1f1b47555550b3cb3cb3cb3e0e0e0e0c75c7575d75d75d7171707174c174c155555415d0142cf2cf2c71cf2cb3cf2cb3cf0f2c5583838383a0c3a0c30385583831e71e79db6e756323238c1e3238c238c155555514050b3cb3cb1c73cb2cf3cb2cf3c3cb1560e0e0e0e830e830c0e1560e0c76c71c71db1f31d34c71c71c71c77d76db5c71c71c01075355404332c71cf2cf2cf838383837e77d38df6d36df4e38c74c78c00004555500040ccb3cb3cb3cb3cb2cf3cb2cf3c01560e0e0e0e830e830c01560e0e3232323155541cd4155b5551d5402cf2cf2cf2cf0f2c5554f4b583838383038555436583831c71c71c77c6c1c1c7d76db6d37d71c71c71c71c7051d07d6d1d1d11c051c52cf2cf1c71c70f2c2cb3cf2cb3cf4f2d83838383038a0c3a0c343983831df1c76c7cc71c71c71c77d76db6db7d71c71c71c77c71d38c71c71c71c71c71c71c71df7c6c1c701d301c1c55f5b471d474d474740050732cf2cf1c71cf1cb1c71c71c72cb3cf2cb3cf0f2c4f2d8383a0c70c387a0c38383a0c3a0c303843983831d75c75d75c5c5c1c5d31c75c75d75d71c71c75d7055d05d5d5d1d16c055c52cf2cf2c71cf0f2c2cb3cf2cb3cf4f2d83838383038a0c3a0c343983831db1f31c76db1c71db7db6d76db6db6db6d79df9c71c71e79db6d36db5e76d74e36db6db6c6c7c1c6d306d3055b5b5f475b4d5b4d40050732cf2cf2c71cf2cb3cf2cb3cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c3a0c3a0c303843983831c76c7cdb6db6c71c71d536db4c71c71c71c71400473010752cf2cf2cf2cf83838383 24 16777215 10 1023
def hc_65_3 : Nat → Nat := unpackHintV5 0xccd1acc5a9cabf419ab749feb071b6aaf95ea401be9f014099696692d9a48e193087f9887ec24e78a1886fba3a69519a6349825a424254f1544ec18c45ca3e3f819239618832d9a22cc18626819021195a1bc95412ea380dc14a08894e000222 0x5475c75c71d71c75d76db5d78df1f8d71f1c7555555555552cf2cf2cb3cf2cb3cf2c71cf2cf2cf55a0e83a0c3a0c3838383835583834d34d1c71c71d5471d535d35d34d7134d7071c71d55555555554b3cb3cb2cf3cb2cf3c71c71cb3cb3d560e0e835c30e5e830e0e0e0e0d560e0c71c7535d31c74d34d34c71c71d34d3134d3155554d552cf2cf1c71c72cb3cf2cb3cf2cf2cf5583838383a0c3a0c383835583835471c71c71c74c71c7cc74d34d34d74f31c71d34c71c71c75534d34d34d34c71c71d34d34cb3cb3cb3cb3c71c71cb3cb3cb3cb3e0e0e0e0e0e0e0e0e0e0e0e0c71c71df4db7db4d54df4df1c71c74e34c4e34c5555cd1d51d552cf2cf1c71c72cb3cf2cb3cf2cf2cf5583838383a0c3a0c383835583831c7cc76c71c76d76db5c701db4d35df5d74d36db6db6c71db4d3136c15554454b3cb3cb3cb3cf3e0e0e0e0e875c75d34c5d35d3cc4c1c4d34d75c07175c17555055551405452cf2cf2c71cf0f2c2cb3cf2cb3cf5583838383038a0d70c397a0c35583831db1db4d7536d74c01307c007c5554100402cf2cf2c71cf2cf2cf03c0558383838383830085583831f31c71f34df4df1f300cf3001b01c23155cd73040100b3cb3c71c71cb3cb3c0f01560e0e0e0e0e0c021560e0c71df4e37db4db7d38c07234c4e3138c1c5555541514544b3cb3cb1c73cb2cf3cb2cf3c3cf2c3d560e0e0e0e830e830c83a1560e0c71c71d5555477355556d5515454b3cb3cb1c73cb3cb3d5553d2d60e0e0e0e0e0d5550d960e0df5c0001c71c0071c000000001f5b471d5f4d4747400b3cb3cb2cf3cb2cf3c71c71c013cb60e0e830e830e0e0c010e60e0c77c71db1f31c71c71c71c000000005c06c01c1c001c0007007001f5b471d474d474741cc001f2cf2cf1c71cf1cb1c71c71c70000f0b04f2d8383a0c70c387a0c38383000032043983831c1d7001c705d7000000000005d5d5d1d5d355d35002cf2cf2c71cf2cb3cf2cb3cf004f2d83838383a0c3a0c30043983831db1f31c76db1c71db7db000000001701b02700701b1b001700006d6d7d1d6d356d350730009cb3cb3cb1c73cb2cf3cb2cf3c0003c2c13cb60e0e0e0e830e830c0000c810e60e0db6c00071c00071c1c00000001fad351c74756d6d1d1d0002cb3cf2cb3cf2cf2cf1c71c7004f2da0c3a0c3838383830043983834d4d31d1c71c707001333000004c0070701701b007007000b3cb3cb3cb3c71c71c0003c2c20e0e0e0e0e0c0000c820e0c71db1c71c71c71c76c7cc000000001c000707001701b00700700071d351c74756d6d1d1d0730001cb1c71c71cf2cf2cf1c71c70000f0b04f2da0c3a0c383838383000032043983831db1c1c04c01700270013135353475354d4132cf2cf2c71cf2cf2cf002c4f2d83838383838300843983831db1c1c70006db000000000007d6d7d1d7d357d350002cf2cf2c71cf2cb3cf2cb3cf004f2d83838383a0c3a0c30043983831c76db1db1f31c71db6db00000001f005c06c09c01c05c001f00007d6d7d1d7d357d350730007cb3cb3cb1c73cb2cf3cb2cf3c0003c2c13cb60e0e0e0e830e830c0000c810e60e0c75c1d75c0071c175d70000000005d5d5d1d5d355d35002cf2cf2c71cf2cb3cf2cb3cf004f2d83838383a0c3a0c30043983830175d75d71d75c75c00000000175b578d5f57d5d002cf2cf2cb3cf2cb3cf2cf2cf004f2da0e83a0c3a0c383830043983835d75c5d71d75c0071c000000001757574d574d5747400b3cb3cb2cf3cb2cf3cb1c73c013cb60e0e835c30e5e830e0e0c010e60e0c75c7175d75d75c00000005c05d5d5d1d5d355d35002cf2cf2c71cf2cb3cf2cb3cf004f2d83838383a0c3a0c30043983831e71e7be76ef6e7000000000027676747678d675002cf2cf2cb1c72cf2cb3cf2cb3cf004f2d83838383a0c3a0c3004398383104d34d37db6df1305c000033337301cdcd7357304b3cb3cb3cb3cb3cb3c01560e0e0e0e0e0c01735ce0e0c14004d34d35d75d700cc4c000014d15cd4d54d5400b3cb3cb3cb3cb3cb3c015683a0e0e0e0e0c01560e0d57db6df4c74e74c74d3000001300005c01b1b0132300131b00270070015cd4d54d53550730004b3cb3cb2cf3cb2cf3cb3cb3c0003c2c1560e0e830e830e0e0c0000c8143560e0c41b6db6d34d34c01b04c00734737300cccd5412cf2cf2cf2cf2cf2cf005583838383838300c05583834d37d34d34d75d75c00000014d7351cdcd5433330b3cb3cb3cb3cb3cb3c015683a0e0e0e0e0c01560e0d54c74d34c74e76db6db130000000004c00131b001b006c6c09c01c005354d55cd541cc0012cb3cf2cb3cf2cf2cf2cf2cf0000f0b055a0c3a0c3838383830000320558383 24 16777215 10 1023
def hc_65_4 : Nat → Nat := unpackHintV5 0xb2d138abc9c2a16a989ad9a491e23e8cd1448751607fe9da7aa95074e1726ea19064c2786120e85b198253c9d45170964cd12846e97a3d8a5839a0fa33d9722c71da29f89e26b0d225485a1e19cc18a15e1259920be99c0511b60370680000dc 0x1c071c01d36d35c707334d34d51dcd55575b4753554d4d5114d4c52c72cf2cf2cb4f2d8383a4391c7cc7cd1c7551f355cf3536d35c71f31c7cd34d34d5d551d5755534b3cb3c72c71c71cb3cb3cb3cb3d54b60e0e0c3830e0e0e0e0d5660e0c71c76c71c7cc71c71c76d76db5c71c71c79d79df1f5c57555547735556755555d55b5b54755d555b5b55455f454b3cb3c72c71c71cb2cf3cb2cf3cb3cb3d5553d2d60e0e0c3830e830e830e0e0d5550d960e0c155075c75c71d34c71eb9d1b4db14134c130715d5555555450b3cb3cb2cf3cb2cf3cb1c73c3cb1560e0e830e830e0e0c0e1560e0c01d71d71c75e71c74e71b334db04db6d30715d555555551dcc515d56d54d8d55ad55534154c152cf2cf2cb3cf2cb3cf2c71cf0f2c5554f4b58383a0c3a0c38383038555436583831db1db000055354c71c71c00556d5340019d2cf2cf2c71cf002cf2cf53d58383838300838355983831db1db0000556d357d3000000055540005002cf2cf2c71cf002cb3cf2cb3cf558383838300a0c3a0c35583831db1db1b3300001b09c01c005b55554773000050416d56d57d000040001410054b3cb3cb1c73c0003c2c15553d2d60e0e0e0c0000c815550d960e0c71b6d31131316d55559dcd14556d555b5b4554dcc54b3cb3cb3cb3c3cb155560e0e0e0c0e15543560e0c55474c7cdb1c74d31db1db4c44c44c1c67555b54d154c2cf2cf2cf2cf2c71cf0f2c5583838383838303850d5838305451c76db1c74d31db1db4d30504c44c1c55555555142cb3cf2cb3cf2cf2cf2c71cf0f2c55a0c3a0c3838383830385583830076c71d36c71db6e71db1db4db4db01b334c1c5b555556d55551dcc516d55535b555b55b55341154d8c152db2cb3cf2cb3db3cf2cf2cf2c71cf0f2c5554f4b5a0c3a0c3838383830385554365838301d71d30cd3131355547735d5d4d4d54dad54d0052cf2cf4f2d83834391d71d7006c005d35557d3000000057555547730001400b3cb3cb1c73c00b2cf3cb2cf3d560e0e0e0c02830e830d560e0c75c75c006ccc0009c01c0057555547730001105755b55f40000001410054b3cb3cb1c73c0003c2c15553d2d60e0e0e0c000030c2815550d960e0d35471c71c71d3131757555472cf2cf2c783834d31c71c1c4d31c1c05d5d5d5551dcd7575757557401d14c52cf2cf2c74f2d970c35e834391c71c74d77d37d73355cf353131331ccd071551d6745530b3cb3c72c71c71cb3cb3c3cb1560e0e0e0e0e0c0e1560e0c71c71df4db7db4e70131301ccc71c071c767555547735556754517d56d51d53630044550455363054b3cb3c72c71c71cb2cf3cb2cf3c3cb15553d2d60e0e0e0e830e830c0e15550d960e0c071c71c71c0017575755547735d5d5d5d55dad51d0052cf2cf4f2da83834391f31c71f300330cc4d77d37d71f355cf300155b51d000674b3cb3c71c71c00b3cb3d4f560e0e0e0c020e0d5660e0c71c71c79c00001ccc01b0070067555547730000504155b5474000100005040152cf2cf1c71c70000f0b05554f4b58383838300003205554365838351c74c4c5c113131307015d3534450f3c3cb00e0541531c74c74d79c71d34d35d3133354574d4d52cf2cf2cb8383554d34d7cd34d35d39cb2e95555cd51d71d71d34c75d71d75c74d74d74d74e74e74d74d34d31c75cb3cb3cb3cb3cb2cf2cb3cb1c73cb3cb3e0e0e0e0e83a0e0e0e0e0e0e0d51d71d71c75c71d75db6d75d79c71e7556d55552cf2cf2cf2cf2c71cf2cf2cf5583838383838383835583831f31f3471c7cd75d71c75d75d75c71c71d75d75d55cd73555554b3cb3c71c71cb3cb3cb3cb3d560e0e0e0e83a0e0e0d560e0c71c75c71c7cd1c7550471d75d75d71c71c75d75d7555555cd5d554b3cb3c71c71cb3cb3cb3cb3d560e0e0e0e83a0e0e0d560e0c71d1c75d5471d471d34d74d71c71c74d35c4d35c555555555552cf2cf1c71c72cb3cf2cb3cf2cf2cf5583838383a0c3a0c38383558383101c71c71c700552cf2cf8383a51c71c71c70001ccd7171717017001c0555142cf2cf0f2ca8383038 24 16777215 10 1023
def hc_65_5 : Nat → Nat := unpackHintV5 0xe411d8dcd9ced621aecfa1a0ca714cc25a06baf9d8af62e6aaa130a4319c9b12489359ee8762fe81c1687b819075a9766f19a4658a645e01e256a1d84fe1b049b98a3da3063679ca2f91ba2879c61c131a1569aa1180fa0b698601b26e00006c 0x1c71c7001733001701c01c0055477355000050415d55d51d00000005040152cf2cf1c71c70000f0b05554f4b58383838300000c30a0555436583835471c71c71c71c71c71c71d76db5d78df1f8d7071c71d55555551d5554b3cb3cb2cf3cb2cf3c71c71cb3cb3d560e0e830e830e0e0e0e0d560e0c71c71c71d34c4d30707134d31c1c71c70055055551405452cf2cf1c71c70f2c2cb3cf2cb3cf5583838383038a0d70c397a0c35583831c71c74e37db4db7c7071c71c131307071c715555505451512cf2cf1c71c72cb3cf2cb3cf0f2c5583838383a0c3a0c30385583831c71c71c71c75547735555556d51d455152cf2cf1c71c72cf2cf5554f4b5838383838383555436583831c71c71c71c71c71d47471d76db5c71c71d78df1f8d7175b471d1d1d757d5f5f4b3cf2cf3c71c71cb2cf3cb2cf3cb3cb3d3cb683a0e0e0e830e830e0e0d0e60e0c71c71c7071c71c071d47471c704c0707134c071c13534747534d534d4530b3cb3c71c71cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c01c71d71c71d71c71c71d31c71c71c74c78c71c71c71c71c71c71d517334d304d34c74c071c07071353534d534d471d31c75477314c2cf2cf2cb3cf2cb3cf1cb1c71c71cf1c71c70f2c4f2d8383a0c3a0c3a0c3a0c3838303843983831d1c700000001c13001c74474d4d00004c1c71c72cf2cf0003c04f2d838383830000843983831c71c71c74d31c71c70500000000004d4d1c74474d3000002cf2cf1c71c72cb3cf2cb3cf004f2d83838383a0c3a0c30043983831c71db1db1c71db1c71c71d51733000000001301c0007070007007001353471df1c75477300011302cf2cf1cb1c71c71cf1c71c70000f0b04f2d8383a0c3a0c38383000032043983831c71c71c701c1c71c751d1c74c0701c1c4d301c704d4d1c751d1dcd34d534d4530b3cb3c71c71cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c01c71c71d31db1c71c71d31c71c76c71c76c71c71c71c71c71c71d54d34d34c05ccc74c071c0707134d534d5353471d31c75477314c2d32cb3cf2cb3d33cf2cf2cf1cb1c71c71cf1c71c70f2c4f2da0c3a0c38383a0c3a0c3838303843983831d1c7000017330001ccc000707001c74474d4d000004f3071c71cb3cb3c000f013cb60e0e0e0c00002843983831c71c71c71c71c74d30500000000004d4d1d14d3000002cf2cf1c71c72cb3cf2cb3cf004f2d83838383a0c3a0c30043983831c71c71d71c71d31c75c0000001353471df4d7515dcc00b3cb3c72c71c71cb3cb3c013cb60e0e0e0e0e0c010e60e0c71c71c71d71f31c71c75400000013534c71c0001c71c7071d3cc00b3cb3c72c71c71c71c71c00b3cb3e0e0e0e0e0e0c020e0e0e0c71c75c76c71c75c71c71c754005ccc0000004c070001c1c001c00707001353471df1c7547730000504c0b3cb3c72c71c71c73c71c71c0003c2c13cb60e0e830e830e0e0c000030c2810e60e0d34d31c71c71c71c1c704d3134c1c701c701c1c4d4d4d344d301d1d14c2cf2cf2cb3cf2cb3cf1c71c70f2c4f2d8383a0d70c397a0c3838303843983831c71c77d36df6d38c14747131307071c7071c74d4d1d1d4e304d0538c2cf2cf1c71c72cb3cf2cb3cf0f3cb0f4f2d83838383a0c3a0c303843983831c71d31c71f3471d5111d54d3134c1c71c74d34d35351d55573535552cf3cb3cf1c71c72cf2cf2cf2cf55a0e838383838383835583831c7471d751d1c75d34d34c71c71d34d34d737351d7355cdcd54b3cb3c71c71cb3cb3cb3cb3d560e0e0e0e0e0e0e0d560e0d51c71d71db1c71d71c71c71c74c76c71c71c74c71c71c71c71d31c71c71c71d54d34d34d34c4d34c1d31c1c71c1c71c75735355351d475573552cf2cf2cb3cf2cb3cf1cb1c71c71cf1c71c72cf2cf558383a0c3a0c3a0c3a0c3838383835583831c71d1c75551c75554d34d31c71c74d34c4d34c535547555355534b3cb3c71c71cb2cf3cb2cf3cb3cb3d54b60e0e0e0e830e830e0e0d5660e0c71c71c7534df1d54d3134c1c71c74d34d3535cd5cdcd573735cdcd2cf3cb3cf1c71c72cf2cf2cf2cf735cda0e8383838383838355983831c76c71d1d51c79d34d34c71c1c7134d34dcd5cd1d7355cdcd73734b3cb3c72c71c71cb3cb3cb3cb3d54b60e0e0c3830e0e0e0e0dcd7360e0d51c71c71d31db1c71c71d31c71c76c76c71c76c71c71c71c71c71d31c71c71d54d34c4d34c4d34d31d31c1c71c1c71c75354d55cd1d475573554d2cb3cf2cb3cf2cf2cf1cb1c71c71cf1c71c72cf2cf552da0c3a0c38383a0c3a0c38383838355983831c71db1c71c71c71d51c7071c7071c71d471c71d51dcd4b3cb3c72c71c71c73c71c71cb3cb3d3cb60e0e830e830e0e0e0e0d0e60e0c1c70701d74c71d34d354773555d5d1d4dad54d4d514c52cf2cf4f2d83834391f3471f354751f355cf3535d35c71c71d34d34d55751d57554b3cb3c71c71cb3cb3cb3cb3d560e0e0e0e0e0e0e0d560e0c71c7cc71c76c71c71c76d76db5c71c71db6d7176c57555547735555755555d55b5b54756d6d555d55455152cf2cf1c71c72cb3cf2cb3cf2cf2cf5554f4b583838383a0c3a0c38383555436583835c171c071c74c4442cf2cf8383a 24 16777215 10 1023
def hc_65_6 : Nat → Nat := unpackHintV5 0xd04942cac162c3a9c6bee132b94168b2d19caa4224a3d19c9d31a8904b3a8921ca80da127981d6713a1269a1e662c1b85c69965053064f683a4d089845c1d24021683ab15c3471902b9a3625f9681ee1c61a61201401980a826005913c000164 0x5db6d71c7cc76c4471df5d75535d36db6c76df7c71d313070713535f7cb3cb3cb1cb3cb3e0e0e0e0d37d37c71c71c1cccccc002301c4d4d01c1cc773004c2cf2cf2cf2cf1c71c7004f2d8383838383830043983834e37db4db7c71df051c8d4c4c4e38d38c1c4d4d4c741c704d1d14e30b3cb3cb2cf3cb2cf3cb1c73c3cb13cb60e0e830e830e0e0c0e10e60e0d34d34c77c77c4c13cd4dcc13073cf31f3732cf2cf2cf2cf2c71cf4f2d83838383838343983834d34d31df1df10001309c4f3537301c1cf3cc7cdcc132cf2cf2cf2cf2c71cf0004f2d8383838383830043983831df1df4d34d37d3540000001304d34d34d715cc7534c001d0002cf2cf2c71cf2cf3cb3cf002cf2cf83838383a0e8300838383831df1df4df4d34df4d35400000004c1f01b02704c8c04d3535f47731c751c71c00132cf2cf2c71cf2cb3cf2cb3cf00003cf02cb04f2d83838383a0c3a0c3000032043983834d74f3534d34d47534d5114d34d34d34d34d34d35355475573535552cf2cf2cf2cf2cf2cf2cf2cf5583838383838383835583834d354454d35f31d34d351d4d34d34d34d34c71d35355735355355552cf2cf2cf2cf2c71cf2cf2cf558383835e5c3838383835583835475c75c71d34e71d31c74d34d74d34d36d36d34c71c71d34d36d34c71d34d35534d34d34d3134d3131c74d34d3134d315cd4d554d57347554754d54d4b3cb3cb2cf3cb2cf3cb1c73cb2cf3cb2cf3cb3cb3d53d2d60e0e830e830e0e0e830e830e0e0d50d960e0d54d34d34d31c74d34d35d71d1c71f34d47534d34d34d34d34d34d34d34d32cf2cf2cf2cf2cf2cf2cf2cf2cf2cf8383838383838383838383831d1c71c74d51c74d34d34d31c71d3cc71c7cc71c71d34d34d3cd3cd3cd3cd34d34c71c71cb3cb3cbccfccbccfccb3cb3cb3cb3e0e0e0e0ecc3cecc3ce0e0e0e0e0e0d354d1c74d31d34c75c7474d34d34d35d3cd54d34d34d34d34c71d34d34d32cf2cf2cf2cf2c71cf2cf2cf2cf2cf8383835e5c383838383838383834db4c7476c74d31d34d35d31f34d34d34f35534d34d34d34d31c74d3cd3cd3cd3ccb3cb3cb3cb3cb1c73cbccfccbccfccb3cb3e0e0e0e0e0e0ecc3cecc3ce0e0e0e0d51d71d71c75c71f34d74db6dbcd31c74db4db1c74d54db4d74d34d34c71e74d34d32cf2cf2cf2cf2c71cf2cf2cf2cf2cf8383838383838383838383834d34d34db4f3475534d5114d34d34d3134c4d34d35355475573535552cf2cf2cb3cb2cf2cf2cf2cf2cf558383830e0c3838383835583834d37d4d31d39d47534d34d34d34d31c74d4d7355cdcd7373554b3cb3cb3cb3cb1c73cb3cb3d560e0e0df9f0e0e0e0e0d560e0d51d31c74d31c74d39c76c76d34c71d34d36c71c71d34d34db4d34d36d36d34d54d34c4d34c4d34d34c71d34d34c4d34c5354d55cd5cd1d51d552cb3cf2cb3cf2cf2cf2c71cf2cb3cf2cb3cf2cf2cf55a0c3a0c383838383a0c3a0c383835583835d7501ccc7d314575d407331f5c5c1c4c404d477d05103cb00e1471d36d71c75c75d55575d36d35d55734db4d74df4df4c71df4df4d37d32cf2cf2cf2cf2c71cf2cb3cb2cf2cf2cf838383838383a0e83838383831d71d75db6db6d75576db5df1c77df7df5551d5552cf2cf2c71cf2cf2cf2cf2cf55838383838383838355583831c76db5471c151dcc71d471c752cf2cf2c71cf2cb3cf2cb3cf2cf2cf4f2d83838383a0c3a0c38383439838305541c71c71c71c71c71c744c504d301c1c55555555142cf2cf2cb3cf2cb3cf1c71c70f2c558383a0c3a0c383830385583830071c71c71c71c71c71c5ccd35c135db1c1c55555547735514575575536355575551d0553054b3cb3cb2cf3cb2cf3c71c71c3cb15553d2d60e0e830e830e0e0c0e15550d960e0c71c71c000155b4d40071c00001551c54001400b3cb3c71c71c00b2cf3cb2cf3d560e0e0e0c02830e830d560e0c71c71c5ccc00006c07007001551dcd540004416d56d51d00000005040152cf2cf1c71c70000f0b05554f4b5838383830000320555436583831c1c74c44c1c5555514556d534553152cf2cf2cf2cf0f2c5555838383830385550d5838305451c71c71c71c71c71c74d30504c41c1c5555554755142cb3cf2cb3cf2cf2cf1c71c70f2c55a0c3a0c3838383830385583830071c71c71c71c76c71c71c74d75d35c05ccc70715555551dcd54516d55535b555b55b5474154c152db2cb3cf2cb3db3cf2cf2cf1c71c70f2c5554f4b5a0c3a0c383838383038555436583831c71c700004d51c7071c70057554740019d2cf2cf1c71c7002cf2cf552d838383830083835583831c71c700005d3555001c700000555150005002cf2cf1c71c7002cb3cf2cb3cf558383838300a0c3a0c3558383 24 16777215 10 1023
def hc_65_7 : Nat → Nat := unpackHintV5 0xf061b8e82210dd0ac6d679a4d01998c8e9ccc251a6baf1d8b371e0a7c2eca1918c9b519094e99a8be2428481d87da1b87609e669c31263b9825d29a45689a84d4252415afa3f78783b6904325a442b49c420fa941b3970125a38074ac40001d2 0x1d1db4db4d39d34d34d34c71d34d34d34d347574dcf3cc7cdcd34d34d4d2cf2cf2c71cf2cf2cf2cf2cf4f2d838383838383838343983831d71d74d74f34d34d34d51c7534c74d5cc7534d3441d4d34d34d34c71d34d34d34d34d34d32cf2cf2c71cf2cb3cb2cf2cf2cf2cf2cf83838383a0e838383838383831d71d74d74d34d36d35537d34e74d34d36d34d34d31c74d34d34d34d34d34d3134d3134d4d5d1dcc71d471c74d34d3534b3cb3cb1c73cb2cf3cb2cf3cb2cf3cb2cf3cb3cb3d3cb60e0e0e0e830e830e830e830e0e0d0e60e0c75c7535d135d3cd34d34d31c74d34d34c7535347534d3cd3534b3cb3cb1c73cb3cb3cb3cb3d3cb60d7970e0e0e0e0e0e0d0e60e0d75c7535d3cc71d134d34d34d34d34d34d3535353534d3cd3534b3cb3cb3cb3cb3cb3cb3cb3d3cb60e0e0e0e0e0e0e0d0e60e0c75c75c7534d3474d35d3cd35d3cd5134d34d31c74d34d34d34d34d34cb3cb3cb1c73cb3cb3cb2cf2cb3cb3cb3e0e0e0e0e0e0e83a0e0e0e0e0c75c75d75d36d35d31c79d38d3138d313535347534d4d2cf2cf2c71cf2cb3cf2cb3cf2cf2cf4f2d83838383a0c3a0c3838343983831d71d74c4d34db04e74d3131307134c134c134d4d5d347534d314c2cf2cf2c71cf2cb3d33cf2d32cb3cf0f2c4f2d83838383a0c3a0c303843983834d304db4c1c751c74d1d71d74d304d304c4c4c1c4c751c754d353574d1d14c2cb3cf2cb3cf2cf2cf2c71cf0f2c4f2da0c3a0c38383838303843983830075c75c71d39c71d34d35d34d36d34d34d38d34d34d34d34d38d51b334d304d34d307134c134c134d4d5d34d534d51dcc71d471c714c2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf0f2c4f2d8383a0c3a0c38383a0c3a0c303843983831db1db4d74d34db4d34e74c00000001353447534d3002cf2cf2c71cf2cb3cf2cb3cf004f2d83838383a0c3a0c30043983836d76db4d34d31db1db0500000000004d4d001c7011d002cf2cf2cb3cf2cb3cf2c71cf004f2d8383a0c3a0c383830043983831db1db4d34d36d35400000013534d41c74f31c74d300071c000b3cb3cb1c73cb3cf2cf3c00b3cb3e0e0e0e0e83a0c020e0e0e0c76c76db6d36db6d36d51b33000000001307c01c04c001f00004db535b47731c751c71c000141302cf2cf2c71cf2cb3cf2cb3cf0000f0b04f2d83838383a0c3a0c3000032043983834d304c4d71db1db1c74d1c754c4c4d304d304c1c4d4d1c754c754d47514c2cf2cf2cb3cf2cb3cf2c71cf0f2c4f2d8383a0c3a0c3838303843983831db1db4d704c4d34e74d3131307134c134c13535351d534d314c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983831534d1c74d31d31f34c76c76c71d34d34c71d34d34d36d35531313131307134c4d30b3cb3cb3cb3cb1c73cb3cb3c3cb20e0e0e0e0e0e0c3830c0e20e0c01c74d31c74e71db1db4d34d34d36d34d36d34d34db4d34db4d35534d34d301b334c1c4d304d304d34d534d4d534d4d6d1dcc71d471c714c2d32cb3cf2cb3d33cf2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2da0c3a0c383838383a0c3a0c303843983835d74db4d75d71d305000000000135d4d5c71c715dcd35d400b3cb3cb2cf2cb3cb3cb3c013cb60e0e0e0e0e0c010e60e0c75c75d35d34d36d34d39d3000000004d3535711c71d4d34c00b3cb3cb1c73cb2cf3cb2cf3c013cb60e0e0e0e830e830c010e60e0d34d34db6d75c75c75c14000000000135d4d5c0071c0471c7400b3cb3cb2cf3cb2cf3cb1c73c013cb60e0e830e830e0e0c010e60e0c75c75d75d36db6d35d5001b330000001309c007070130007c000135d4d5d1dcc71d471c700011302cf2cf2c71cf2cb3cf2cb3cf0000f0b04f2d83838383a0c3a0c300000c30a043983831c77c71c74df4d34db4d35537d34d36d34c000554d04d34e34c4c07331c704d31304d34e301c71d34d4d7d1dcc71d471c74d35354d34d4530b3cb3c71c71cb2cf3cb2cf3cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830e830e830c0e10e60e0d30071c71c71c001d3534b3cb3e0e0d34c71c74740007335c5c5c5c05c0070134c74754530b3cb3c3cb25c30d7a0c0e071c71df4db7db4e75400001ccc0009c01f01b00704c8c00440004e75351dcc71d471c70000504c0b3cb3c71c71cb2cf3cb2cf3c0003c2c13cb60e0e0e0e830e830c0000c810e60e0c77c77d34d34d54d34d34d715cc7534c441d4d34c4c4c1c4d3134d34f313070b3cb3cb1c73cb3cb3cb3cb3c3cb20e0e0e0e0e0e0e0c0e20e0c77c77d37d34d37d34d54df4d34db4d34e74c01313130704c4d34e304d34d34d4d7d1dcc71d471c74d34c530b3cb3cb1c73cb2cf3cb2cf3cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830e830e830c0e10e60e0c77c77d34d34d39d3000013134d4d7c47cf31c7734d34c00b3cb3cb1c73cb3cb3c013cb60e0e0e0e0e0c010e60e0c77c77d37d34d37d34d50013001300004c04c0401c04c8c04d3535f47731c751c71c0130041c0b3cb3cb1c73cb2cf3cb2cf3c0003c2c13cb60e0e0e0e830e830c0000c810e60e0d34d36d34d37c77c77c1471d3537d34d37d34c0154c4c4d34d34c1c9d34d38c04c4d3535f4c751c7047731c751c71c4d4d30b3cb3cb2cf3cb2cf3cb1c73cb2cf3cb2cf3c3cb13cb60e0e830e830e0e0e830e830c0e10e60e0c75c75d34d35d701c5d74d3134c4c1c4d304d304d5354d1d4d344d3014c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c30384398383 24 16777215 10 1023
def hc_65_8 : Nat → Nat := unpackHintV5 0xed5964e5c1e6e0495eda7176d3e1a4c9a290c3b17cbc61d4b589b6aec1b2a801b0a229769c21829539ba8e91aa88f96684093c7d71a678813c6b83405ecb2e5233264a99e642f9e83aa2163349d62bc9e02489d01cd9ec1162de051b12000146 0x71c71c0000174c0015471d400015154001400b3cb3c71c71c00b2cf3cb2cf3d560e0e0e0c02830e830d560e0c71c71c001ccc005c05c01c01555dcd1d5400014105751d51d4000100005040152cf2cf1c71c70000f0b05554f4b583838383000032055550c35a583831c1c71c44c4c4755555773451551dcd5547474554dcc5471c71cb3cb3c3cb1554f560e0e0e0c0e1555560e0c74d74f35d74d31c71c71554c4c4c41c45357d551d154c2cf2cf2cf2cf1c71c70f2c53d583838383838303855583831c71c71c74d31c71c705454c4c4d30501c455555555142cf2cf2cb3cf2cb3cf1c71c70f2c55838397a0c3a0d70c383830385583831c71d71db1c71d71c71c71c04c4c1c77c71c01ccd555dcd1d55554755145351d5547475547551d1d41154d8c152cf2cf1cb1c71c71cf1c71c70f2c5554f4b5838387a0c3a0c70c3838303855550c35a583831d71d700000733174c001f4d554000155b1550005002cf2cf2c71cf002cb3cf2cb3cf558383838300a0c3a0c35583831d71d7000007331701b01f00555b735540004419d67547500000005040152cf2cf2c71cf0000f0b05554f4b583838383000032055550c35a583835575d75d31d75c74d36d35d38d3138d3135d39d5cd6d56d55554b3cb3cb2cf3cb2cf3cb3cb3cb3cb3d560e0e830e830e0e0e0e0d560e0c75c7471f3cc71d7cc71d75d75d71c71c77c75d75d7735cd55555552cf2cf1c71c72c72cf2cf2cf2cf558383831e1c3838383835583835d75c71c71f3471c75c7550575d75d75d75d75d75df5d5555573575552cf2cf2cf2cf2cb3cb2cf2cf2cf5583838383838383835583835d71d35d74db4d705505313117334d701c71d555555450b3cb3cb3cb3cb2cf2cb3c3cb1560e0e0e0e0e0c0e1560e0c71c71c75c71c74c71d74c4c1c77d35c117335555555142cf2cf1cb1c71c72cf2cf0f2c558383870e0c783830385583831d71d75d71c71d75576db5e71c79e78d7178e7155555555554b3cb3cb2c71cb3cb2cf3cb2cf3cb3cb3d560e0e0e0e830e830e0e0d560e0c75c75d313134c1c71d3cc5d706c5d74d34c07555055551405452cf2cf2c71cf0f2c2cb3cf2cb3cf5583838383038a0c3a0c35583835d7cd75f34f300cf3135d35c4c001c1f1cd7315440100b3cb3cb3cb3cb3cb3c00b1560e0e0e0e0e0c001560e0c71c71d30071d1c71c5c001c231515440100b3cb3c71c71cb3cb3c00b1560e0e0e0e0e0c01560e0df6db7d38c131f4e38c74c78d38c4c4c4e315555505451512cf2cf2cf2cf2cb3cf2cb3cf0b3cb2c5583838383a0c3a0c30385583836db6db555b735555555475455152cf2cf2cf2cf2cf2cf5554f4b583838383838355550c35a583831c71f31c71db5d79db6db6db6d75d51c71c71db5d35d557575b4db6d76db5c77c71c71df9df1f7c6d35c5d36c5d75b5747731c751c71db4d5d575d357d7d2cf2cf1cb1c71c72cb3cf2cb3cf2cb3cf2cb3cf2cf2cf4f2d83838383a0c3a0c3a0c3a0c3838343983831c71db1c71f35d77db6db6df6d75d51c71c71db6d36db557d6d5d35d76db5c71c71df7df1f7df174df1f4d7175d6d5d1dcc71d471c75d35f57df4d5f5f4b3cb3c71c71cb2cf3cb2cf3cb2cf3cb2cf3cb3cb3d3cb60e0e0e0e830e830e830e830e0e0d0e60e0d34d31d79c75df1c75d1c754db4db6d35d36db6db5536d35d34df134d7131c77d37d37d37d37d35d3534d5c71c71d531d5d51dcc71d471c74d4d2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf2cf2cf4f2d8383a0df0c39fa0c38383a0c3a0c3838343983831f31f31c71dcd75d71c75d75d75c7cc71f31d75d75c74747731dcd74d5d35f5f4b3cb3c7cc71f31cb3cb3cb3cb3d3cb60d7970e0e0e0e0e0e0d0e60e0c71c75c71c7cd1c75d31d0471d75d75d71c71c75d75d71d1d1d1d5d3575d74f35f5f4b3cb3c71c71cb3cb3cb3cb3d3cb60d7970e0e0e0e0e0e0d0e60e0d75d71d75c75d71c75d71c755d75d75d75df5df5d75c71d75d7577d1c755df50d1d7d7d2cf2cf2cb3cf2cb3cf2c71cf2cf2cf4f2d0c383aa0c30c30c30c3430d0c30c3aa5d75e830c75d71d75ea871d75c71d575d75ea975d77d77d75d71c75d75d5df66471d577d6475f5f4b3cb3ea8b2cf3cb2cf3cb1c73cb3cb3d3cb571d71d71c75d1c755db6d75e37c7e35c7c71d75b471d5f1d5f475f5f4b3cb3cb2cf3cb2cf3cb1c73cb3cb3d3cb60e0e830c3a830e0e0e0e0d0e60e0c75c7537d34e74d34d34d31c74d34d34c7cd4dcd373cf31f3734d34d3534b3cb3cb1c73cb3d32d33cb3cb3d3cb60df9f0e0e0e0e0e0e0d0e60e0c75c75d34d34d35d3cd3553531d535731d4d34d107534d34d34d31c74d34d34d34d34cb3cb3cb1c73cb3cb3cb3cb3cb3cb3e0e0e0e0e0e0e0e0e0e0e0e0c76c76d36d34db4db4d35536d34e74d34d34d34d34c71d34d34d34d34d34d34c4d34c4d3535b47731c751c71d34d34d4d2cf2cf2c71cf2cb3cf2cb3cf2cb3d33cf2d32cb3cf2cf2cf4f2d83838383a0c3a0c3a0c3a0c3838343983834d34c71d471db476db1db7db6df6db4db4db4db4d54d36c4d36c4db4db4c71df4df4df4df4df4db1c751c75b54db4d4d35b47731c751c71d3534b2cf3cb2cf3cb3cb3cb1c73cb2cf3cb2cf3cb3cb3d3cb6830e830e0e0e0e0e830e830e0e0d0e60e0c76c77d34d34d31c74d3cd4dcd373cf31f3734d4d2cf2cf2c71cf2cf2cf4f2d8383838383834398383 24 16777215 10 1023
def hc_65_9 : Nat → Nat := unpackHintV5 0xe459ceddf19ad741acd2114ccd991ec7f16abfea02b8b1ceb151d8a9f1d89e5ae699893493199c89fa488241ee765afa70e95c6aa9906409a85ad24e5429aa4e018a439a9a3c99c03212a22c397622b2621ce97214f1fe0e61a4051254000144 0x1db6c76db1c76db6db6c755b6db6df1c79df8df1f8df16d55555555554b3cb3cb1c73cb2cf3cb2cf3cb3cb3d560e0e0e0e830e830e0e0d560e0c76db1db6d313134c1d31b1b6db6c134d3055055551405452cf2cf2c71cf0f2c2cb3cf2cb3cf5583838383038a0c3a0c35583836db6db4c6db4db04e38c74c78d31b4db131315555505451512cf2cf2cf2cf2cb3cf2cb3cf0f3cb0f5583838383a0c3a0c30385583836db6db6db6db5b735555555b55475455152cf2cf2cf2cf2cf2cf5554f4b5838383838383555436583836db1d6db4d39c02727001c6c6c01c04c4c1b6d34d3534530b2cb3cb3c3cb030e0e0c80e1b6c76d31d30076d36c75b6d34c04c9c9d34d34d327274db4d34d4d4d4d2cb2cf2cf2cf2cf0c34e83930c38383a1db6c76db1c756d6c76db6db6db6e71c79e78c8e71b6d6d6e7476759d67674b3cb3cb2c71cb3cb2cf3cb2cf3cb3cb3d3cb60e0e0c3830e830e830e0e0d0e60e0c76c76db1b6db6c134d34c4c4d3074c4d304d304d4d4d1d4d344d3014c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c30384398383056d4c6db6db4c78e31d38d31b4db136db4c4c4d4d4e304d13534538c2cf2cf2cb3cf2cb3cf2cf2cf0f2c4f2d8383a0c3a0c38383030e0343983834d354d4d71db1db1c74c1c704c4c1c704c704c0704d4d4d354d354d1d14c2cf2cf2cb3cf2cb3cf2c71cf0f2c4f2d8383a0c3a0c3838303843983835471d34c71d39c76c76d34d34d34db4d34db4d34e34db4d34db4d30134c134c131301ccc71c071c74d34d34d56dcd347534d534d4530b2cf3cb2cf3cb3cb3cb1c73cb2cf3cb2cf3c3cb13cb6830e830e0e0e0e0e830e830c0e10e60e0c7471c0000001b04c0135d15d3474000130b3cb3cb3cb3c0000b13cb60e0e0e0c0003010e60e0c140071c71c71c71c71c71c0000000135d15d34c000747400b3cb3cb2cf3cb2cf3c71c71c013cb60e0e830e830e0e0c010e60e0d51c71c71c71c71db1c71c71c0000001ccc006c00131b001b01b007004d75d35d55dcc747400044c0b2cf3cb2cf3cb3cb3c71c71c0003c2c13cb6830e830e0e0e0e0c0000c810e60e0c71c71c71d47471c71c07071d3130701c134c134c134d4757731d1d4d351c7514c2cf2cf1c71c72cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983835471c71c74c76c71c71c74c71c71db1c71db1c71c71c71c71c71c70134c134c1313071d31c7007334d34d34d55dcc74d471d47474530b2cf3cb2cf3cb3cb3c72c71c71c73c71c71c3cb13cb6830e830e0e0e1e830e831c30e0e0c0e10e60e0c75b6c00009ccc006c001b1b004db45b4d4d000004f30b3cb3cb3cb3c0000b13cb60e0e0e0c0003010e60e0c140076c76c71db6c71d34c0000000134534c001347400b3cb3cb2cf3cb2cf3cb1c73c013cb60e0e830e830e0e0c010e60e0d51d34d31d34e7cc76c76c000000134c0004d34d3135d3cd3474c00b3cf2cf3cb3cb3cb1c73c00b3cb3e83a0e0e0e0e0c020e0e0e0d51db1c74db1c76db9c76c76c000000001ccc6c00131b001b01b013004db9d36d56dcd3474000141302cb3cf2cb3cf2cf2cf2c71cf0000f0b04f2da0c3a0c3838383830000320439838355b1db6db1db6db6db6db1b6db1b6db6db6db6d56dcd54b2cf3cb2cf3cb3cb3cb3cb3cb3cb3d3cb6830e830e0e0e0e0e0e0d0e60e0d3cd573cd47cc71f354754d74d74d34d31c71c75357d551d552cf2cf2cf2cf1c71c72cf2cf55838383838383838355583831d71c75c7cc71c71c71c75d75d71c71c1df1c1c71c755577355547551d55555d474755475551d547475455f454b3cb3c71c73c72c71c71c71cb3cb3d5553d2d60e0e831c30e1e830e0e0e0e0d555430d6960e0c7cd71f347cd573cd4d7554d7cd35f34c71d74d34d35355d557d554d2cfccb3f32c71cf2cf2cf2cf2cf552da0e83838383838383555a60e0c71d75c75c7cc71c75d75d75db5d75d71c75d75d7177d71555dcd5d555555d5555755d547475575551d1d55157d152cf3cb3cf2c71cf2cb3cf2cb3cf2cf2cf5554f4b5a0e838383a0c3a0c3838355550c35a583833355cf3575d75d74d74d75d334ccd13131314d5f5545530b3cb3cb3cb3cb3cb3c3cb15683a0e0e0e0e0c0e15560e0c05d75d74c75d75c74d717334d704d76d3131555dcd5555d55755145354d8c0111555d51d41154d8c152cf2cf2cb3cf2cb3cf2cf2cf0f2c5554f4b5a0e83a0c3a0c3838303855550c35a583835d7cd75f3330cc004f355cf3135d74d75c014d551d0005f4b3cb3cb3cb3c00b3cb3d54b60e0e0e0c020e0d5560e0d75d75d75c005ccc005c17007001555dcd5d5400014105755d51d4000100005040152cf2cf2cf2cf0000f0b05554f4b58383838300000c30a055550c35a583831d71d74d34d36db5d705544c4c41c71c501c70555f555555142cf2cf2c71cf2cb3cf2cb3cf0f2c5583838383a0c3a0c30385583831d71d75d74db6db4d70131301ccc71c071c7555b735f555555145359d5474755363555f554154c152cf2cf2c71cf2cb3cf2cb3cf0f2c5554f4b583838383a0c3a0c303855550c35a583831c71c700004d75d35c54750053554740017d2cf2cf1c71c7002cf2cf552d838383830083835558383 24 16777215 10 1023
def hc_65_10 : Nat → Nat := unpackHintV5 0xdbd1d2d63966cf09ccca4132c4a168be4198b5c220ae71d4a6f1e09b42ec95118c8ed1908879967f72427811d87131b86999e65d630e56d1a45031a847423c41d15c3b919032ba362d19682601c62181201b219811b25c0cb1400731600001cc 0x75c75d75c1b175d34d34c4c4d3074c4d304d304d4d4d4754d344d3014c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983830733333174d35d75d75c7c13000130734dcd35340130b3cb3cb3cb3cb3cb3c013cb60e0e0e0e0e0c0010e60e0c1531f631d38d31e37db6df4e38d38c4c4c4c4db44db04d4d4d4d14e30b2cf3cb2cf3cb3cb3cb3cb3c3cb13cb6830e830e0e0e0e0c0e10e60e0c4c134d34d75d75c13073cf34f3734f353732cf2cf2cf2cf2cf2cf4f2d8383838383834398383104d34d35d75d71305c0004c1cf3cd3cdcd3cd4dcc132cf2cf2cf2cf2cf2cf004f2d83838383838300043983835575d75d34d34d74c00001300015cd3534c004d04d34d34d7002cf2cf2cb3cb2cf2cf2cf002cf2cf83838383838300838383835575d75d34d35d35d34c000004c001704c8c5c01c0057734d354d34d34d4d5c00132cf2cf2cb3cf2cb3cf2cf2cf0000f0b04f2d8383a0c3a0c3838300000c30a043983834d74c75c75c71d3071c1313071c131c13071353534d34d3475714c2cf2cf2cb3cf2cb3cf2c71cf0f2c4f2d8383a0d30c393a0c3838303843983834d354db4d1c701c74c1d71d74c701c704c4c4c1c4d354d354d4d4d3476714c2cb3cf2cb3cf2cf2cf2c71cf0f2c4f2da0c3a0c38383838303843983835475c75c71d39c71d34d35d34d36d34d34d34d34e34d34d34d38c04c4c4d304d3007331c701c71d6dcd34d534d34d347674d354d3514c2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf0f2c4f2d8383a0c3a0c38383a0c3a0c303843983834d74c71c71c71c71c71c71c0000000053534d31d1d002cf2cf2cb3cf2cb3cf1c71c7004f2d8383a0c3a0c3838300439838305001c71c71c71c71c71c700000000004d3014d1d1d002cb3cf2cb3cf2cf2cf1c71c7004f2da0c3a0c3838383830043983835471c71c71c71c71c00000004d74f34d34d300134c07471d400b3cb3cb2cf2cb3c71c71c00b3cb3e0e0e0e0e0e0c020e0e0e0d51c71c71c71c71c71c7000000073300170170130005c00070057734d754d76c71d1d1c000141302cf2cf2cb3cf2cb3cf1c71c70000f0b04f2d8383a0c3a0c38383000032043983831c71c71d1c71c751c701c1c74c4c1c1c4d304d301d5351d1d4d351c7514c2cf2cf1c71c72cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983831c71c74d74c71c07071d3130707134c134c0754d4747534d314c2cf2cf1c71c72cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303843983835534d34d35d3cc71c74d31c71c71c71c71c71c71c71c51c75313134c4d3131307070b3cb3cb3cf2cf3cb3cb3c71c71c3cb20e0e0e0e0e0e0e0c0e20e0d51c71d71c71d71c71c71d31c71c71c74c71c71c71c71c71c71c701313134c134c071d31c70073357734d354d34c71d351c74751c7474714c2cf2cf2cb3cf2cb3cf1cb1c71c71cf1c71c70f2c4f2d8383a0c3a0c387a0c3a0c70c3838303843983834d74c75c75c71d35c71d34c00000000574d3534d34d34757002cf2cf2cb3cf2cb3cf2c71cf004f2d8383a0c3a0c3838300439838305001c74d31c79e31d71d700000000004d3016d36d4e74767002cb3cf2cb3cf2cf2cf2c71cf004f2da0c3a0c3838383830043983835475c75c71d79c71d39c000000001ccc5c06c04c00270004c016dcd36d536db4e7476700011302cf2cf2cb3cf2cb3cf2c71cf0000f0b04f2d8383a0c3a0c383830000320439838355b6c71db6c16dcdb6d5b6db552cf2cf2cb3cf2cb3cf2cf2cf2cf2cf4f2d8383a0c3a0c38383838343983831db1db6d76db4d34d305544c4c41c501c7055555555142cf2cf2c71cf2cb3cf2cb3cf0f2c5583838383a0c3a0c30385583831db1db6db4db6db4db0131301ccc71c071c75b7355555555145357d51d54d8d557d550553054b3cb3cb1c73cb2cf3cb2cf3c3cb15553d2d60e0e0e0e830e830c0e15550d960e0c71c71c000001b4c15471d400015c5554001400b3cb3c71c71c00b2cf3cb2cf3d560e0e0e0c02830e830d560e0c71c71c001ccc006c06c01c015dcd55540004416d47547500000005040152cf2cf1c71c70000f0b05554f4b5838383830000320555436583831c1c71c44c4c5555514551d534553151c71c72cf2cf0f2c5553d583838383038555583831c74d31c71c71c71c705454c4c4d30501c45755555555142cf2cf2cb3cf2cb3cf1c71c70f2c558383a0c3a0c383830385583831c71db1db1c71db1c71c71c04c4c1c77c71c01ccd5dcd55555554514d475551d1d551d51d4154c152cf2cf1cb1c71c71cf1c71c70f2c5554f4b5838387a0c3a0c70c38383038555436583831db1db00004d7136d74d5005357d540017d2cf2cf2c71cf002cf2cf53d58383838300838355983831db1db0000006d307d3555000045550005002cf2cf2c71cf002cb3cf2cb3cf558383838300a0c3a0c35583831db1db000007331b01b01f005b735555000050416d67547500000005040152cf2cf2c71cf0000f0b05554f4b583838383000032055543658383 24 16777215 10 1023
def hc_65_11 : Nat → Nat := unpackHintV5 0x7f84db3e2c659e4334ceaf1ca7210da373e729ad3330d1e12e6265a32e04cb960c3d8a4fada4ef4e22474c1914d3b482f9dc3dc0ef1bd4c30d4728c6359b82d8d081400b188895dc3ada5c19e4e20a5ea504a32301f59700b551604465901593280002b2 0x1c7071d7001c701c74c00000000135d35c71c71d34d7534d7400b3cb3c71c71cb2cf3cb2cf3c00b3cb3e0e0e0e0e830e830c020e0e0e0c140075c75c71d34c71d39c0000000134d15d34d34d1d002cf2cf2cb3cf2cb3cf2c71cf004f2d8383a0c3a0c383830043983830075c75c71d71c75e30000000005db6d75df5f5d7c71c00b3cb3cb2cf3cb2cf3cb1c73c00b3cb3e83a0e830e830e0e0c020e0e0e0d34d3071c71c7001c700000000004d74d74d35d4d35d1c71c7002cf2cf2cb3cf2cb3cf1c71c7002cf2cf8383a0d70c397a0c3838300838383831c71c77d36df6d38c00003307007137d37c71c71d38d3534d002cf2cf1c71c72cb3cf2cb3cf002cf2cf83838383a0c3a0c300838383831d71d700004d34d75d47575c000134d5d35d3cc4d74757000574000b3cb3cb1c73c00b2cf3cb2cf3d3cb60e0e0e0c02835c30e5e830d0e60e0c79c77c000137db4db7d38d476700004d4d4d1d00000b3cb3cb1c73c00b2cf3cb2cf3d3cf2d3e0e0e0e0c02830e830d83a60e0c71c00001ccc01b000071c000402cf2cf2c71cf0000f0b02cf2cf838383830000320838383835475c71d31d54747471c71c75c7cc71c71c71c75c71c71c71c71c71d75d75d75d7177d7071c7074c7071c71d5dcd75d575db1c74751c74d471d1d1df5f4b3cb3cb2cf3cb2cf3c71c73c72c71c71c71cb3cb3d3cb683a0e830e830e831c30e1e830e0e0e0e0d0e60e0d51c75d71d71f31c75d75c75c71d75c71c71c71c7555d1d5d35d75d75d75d75d75c5df5c5c71d75d35c5d35c57735d755d76d75d1d5d74d5d575d357d7d2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf2cf2cf4f2d8383a0c3a0c38383a0c3a0c3838343983835475734d4d31d113471c71c71c71c74c71c7cc71c74754d34d34d34d34d34d31c71c72cf2cf2cf2cf2cf2cf1c71c72cf2cf8383838383838383838383835475c71d31c71c71c74c71c71c71c71c71d34d34d34d34d34d34c71c7074c7071c71d5dcd34d534d31c74c71d1d1d3534b3cb3cb2cf3cb2cf3c71c73c72c71c71c71cb3cb3d3cb60e0e830e830e831c30e1e830e0e0e0e0d0e60e0c75c71c71d1c75d34d34c71c71d34d34c773cf34f3731c74d3cd1dcd3534b3cb3c71c71cb3cb3cb3cb3d3cb60e0e0c7870e0e0e0e0d0e60e0d51d75c75d71d31c71d34d75d5d71c751c71c74d34d35d35d35d34d35d31c75d34d7134d715dcd35d535db4d74d1d3574d74db54d35754d4d2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf2cf2cf4f2d8383a0c3a0c38383a0c3a0c3838343983831d71c71c7cf31c7731c75d75d75c71c71d75d75c7735dcc71d1d357475f5f4b3cb3c71c71cb3cb3cb3cb3d3cb6cc3b30e0c7870e0e0e0e0d0e60e0d75d71c71c7cd1c71d71d74c7415d75d75d75d75d75d75d5d5d5d5d3575d74f35f5f4b3cb3cb3cb3cb3cb3cb3cb3d3cb60e0e0e0e0e0e0e0d0e60e0c75c75d7571c71d575db6d79c71e79e35c5e39c5d6d9d1d6db55db59d9d2cf2cf2c71cf2cb3cf2cb3cf2cf2cf4f2d83838383a0c3a0c3838343983831d751c71d1c75d51c71c71c71c75c71c71c71c74c71d31c1c71c4d74d74d74ef4d35c71c71c71d36d471d1d55dcd35d535db1c74d1c7474d4d1cb1c71c71cf2cf2cf2cb3cf2cb3cf1c71c72cf2cf4f2da0c3a0c38383a0c3a0c38383838343983831c71d74d34d34d34d34f347731dcf3cd3cdcd3534b3cb3cb3cb3cb3cb3d3cb60e0e0e0e0e0d0e60e0c7471c71d34d74c71c71d34d34d34d34c71d1d1c773cf34f3734d34d353471c71cb3cb3cb3cb3cb3cb3d3cb60e0e0e0e0e0e0e0d0e60e0d51d71d71d34d7cc74d34c75734d4d31d113534d34d1d35d34d34d34d34d34d31c74d34d34cb3cb3cb2cf2cb3cb1c73cb3cb3cb3cb3e0e0e83a0e0e0e0e0e0e0e0e0d51d71d71c74d35c74c74d74c71c71d35d34d34d34d34d34d34d34c71d34d34c4d34c57734d354d34d34d1d5d34d34d4d2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf2cf2cf4f2d8383a0c3a0c38383a0c3a0c38383439838354000554d04d34e35d75d74c74d74c74d34c74d74c74d317334d304d31304d34e304d34d31315dcd34d534d34d35354d34d534d4d5c530b3cb3cb2cf3cb2cf3cb2cf3cb2cf3cb3cb3c3cb13cb60e0e830e830e830e830e0e0c0e10e60e0d55d75d74c75d75c74d70017330001700004c1323001100170070015dcd35d535db4d753570000504c0b3cb3cb2cf3cb2cf3cb3cb3c0003c2c13cb60e0e830e830e0e0c000030c2810e60e0d515cd3534c444d4d35d75d74d34d34d34d34d74c4c4d3134d34f3131313130b3cb3cb3cb3cb3cb3cb3cb3c3cb20e0e0e0e0e0e0e0c0e20e0d54d74c0175d75d34d35d35d34d31d35d31d34d31304c4d34e304d34d31315dcd34d534d34d34d34d4d5c530b3cb3cb2cf3cb2cf3cb2cf3cb2cf3cb3cb3c3cb13cb60e0e830e830e830e830e0e0c0e10e60e0d75d5c7534d300131311313130707131301313001534d35344c530b3cb3c3cb20e0c0e135d35d75d74d34d3001300057cf34d3734d34d34d4d5c00b3cb3cb3cb3cb3cb3c013cb60e0e0e0e0e0c010e60e0d55d75d74d34d3bd34c4c004c00000101301323130070016dcd34d534d34d35340130044c0b3cb3cb2cf3cb2cf3cb3cb3c0003c2c13cb60e0e830e830e0e0c0000c810e60e0c53531c74c74d79d75d35d74d34c71c7015c7534d34d35d35c134d31353134d353534cb3cb3cb3cb3e0e0e0e0c74d30071c71d39d747453471c71c71c74c79c75c74d3071c134d35c74d3471d4d4c5d31d3cc71d34cb1c73cb3cb3e0e0e0e0c1534d340154c74d34c74e75d75d74d34d34d34d34d34c4c5d34d38c04c4c4c4d354d305b734d354d34d34d4d13534c2cb3cf2cb3cf2cf2cf2cb3cf2cb3cf2cf2cf0f2c4f2da0c3a0c38383a0c3a0c383830384398383 25 33554431 10 1023
def hc_65_12 : Nat → Nat := unpackHintV5 0xf1632ee51b12dd81e6d5e1e8ce39eac5e216be89d6b6d9ecaafaf8a311fa9c31b893822c888abe8101e279e9c673b98c6d519a6669ba5fb1ae5919a653e94c4be20243da023c51e234d9de2d81d62779821db27216f9ae0cba9006719200019c 0x71c76c71c7cd75df6db6db7db5d70071c71c76db4db6c01f1b174d78d71b01ccc71c071c75d31f07df4e305db6d71c71c77df7d7df7d5d37d7d35d1f7c2cf2cf1c71c72cb3cf2cb3cf2cb3cf2cb3cf0f2c2cf2cf83838383a0c3a0c3a0c3a0c3038838383834d34c75e71d77c71d7071c136d38db6d35d38db6db6c04d3134c1c704c7007331c701c71d36d35d34df534d7531c77d37d37d37d37c4d30b3cb3cb2cf3cb2cf3cb1c73cb2cf3cb2cf3c3cb0b3cb3e0e0e837c30e7e830e0e0e830e830c0e20e0e0e0c7cc7cc71c7335d75c71d71c1c1ccc7335d3174c5d75d71f31c7cc75d75d71f7c2cf2cf1f31c7cc72cf2cf0f2c2cf2cf835e5c383838383038838383831c71d71c71f3071d74c7001c75c7070707174c5d75d3cc5d75d71c71c75d75d71f7c2cf2cf1c71c72cf2cf0f2c2cf2cf835e5c383838383038838383834d354d4d71d71d71c74d31c74e74c4c4d304d304c1c4d353574d34d3471c74530b3cb3cb2cf3cb2cf3cb1c73c3cb13cb60e0e830e830e0e0c0e10e60e0d75d71d75c75d71c75d71c705d7177c1c705df00c1c5d75d75d75df5df5d75c71d71f7c2cf2cf2cb3cf2cb3cf2c71cf0f2c2cf2cf0c383aa0c30c3030c0c30c30c30c3aa5d75e830c75d71d75ea871d75c71c175c5df22071c177c207175d75ea975d77d77d75d71c75c7df0b3cb3ea8b2cf3cb2cf3cb1c73c3cb0b3cb3d78e31d71d71c75c1c705e31b8c1c707c707c1c5db6d75df5f5d7c71c7df0b3cb3cb2cf3cb2cf3cb1c73c3cb0b3cb3e0e0e830c3a830e0e0c0e20e0e0e0d34d31c701c76c1db6c76df6db7db6d36d36d36d38c04c701c704d3134c07331c701c71d34db534db536d36d31c77d37d37d37d37c4d30b2cf3cb2cf3cb3cb3cb1c73cb2cf3cb2cf3c3cb0b3cb3e830e830e0e0e0e0e830e830c0e20e0e0e0c75c75d34d53535d34d47539d3131307134c134c134d4d5d34d1d9d34d314d34c2cf2cf2c71cf2cb3cf2cb3cf0f2c4b3cb2d83838383a0c3a0c303860e983831d71d75e35e34c4c4c1c4e38d36d35d31c79d38d3534d134c2cf2cf2c71cf2cb3cf2cb3cf0f2c2cf2cf83838383a0c3a0c3038838383831df1df4df4d34df4d30131301ccc71c071c75553555363555154c53553545470534151c152cf2cf2c71cf2cb3cf2cb3cf0f2c5554f4b583838383a0c3a0c3038555436583831df1df4d34db4d34df051c74c4df4d34df4d3015531301ccc71c131c071c071c74d4d4d347674d34d34d38d54d8c534d30b3cb3cb1c73cb2cf3cb2cf3cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830e830e830c0e10e60e0c75c75d34d35d751d5d74c1304c1c4d304d304d3534d4d747574d354d3514c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2da0e838383a0c3a0c303843983831e71df4df6d36df051d9c4c4c4c1c4c701c704d4d4d1d4e38c634e30b3cb3cb1c73cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c71e36db8c08c8c07331c701c71c71e36348e30b3cb3cb1c73cb2cf3cb2cf3c3cb0b3cb3e0e0e0e0e830e830c0e20e0e0e0c140071c71c71c71c71c71c0000000134d15d34d31d1d0002cf2cf2cb3cf2cb3cf1c71c7004f2d8383a0c3a0c383830043983830071c71c71c71c71c71c71c00000000176db5d77d7d7471c71c00b3cb3cb2cf3cb2cf3c71c71c00b3cb3e0e0e830e830e0e0c020e0e0e0c71c71c71c000134d31d1c71c7500004d3534c1d1d0005002cf2cf1c71c7002cb3cf2cb3cf4f2d8383838300a0d70c397a0c343983831c71c700004df6d36df1d1c71c7500004d4d1d1c71d00000b3cb3c71c71c00b2cf3cb2cf3d2cf2cb60e0e0e0c02830e830d0e60e0c71c71c001ccc0001b007001c71c7000100b3cb3c71c71c0003c2c0b3cb3e0e0e0e0c0000c820e0e0e0c71c71c71d51d1c71c71c71c71c71c74c4c1c1c4d304d304d351d5dcc747534d314c2cf2cf1c71c72cb3cf2cb3cf0f2c4b3cb2d83838383a0c3a0c303843983831c71c71c71c71c71c07071d78c6e30707178c1f8c176db5c71c71d77d7d747df0b3cf2cf3c71c71cb2cf3cb2cf3c3cb0b3cb3e0e0e0e0e830e830c0e20e0e0e0d34d31c71c71c71d1c754c4c4d304d301c1c4d3534d1c751c751d1d14c2cf2cf2cb3cf2cb3cf1c71c70f2c4f2d8383a0d70c397a0c3838303843983837d36df6d31c71c7051c1d4c4c4e304e301c1c4d4d1c71c7471c74634e30b3cb3cb2cf3cb2cf3c71c71c3cb13cf2d3e0e0e830e830e0e0c0e10e60e0c71c76c71c71c71c702323071c71c01ccc71d1c71d1c71c7238c2cf2cf1cb1c71c71cf1c71c70f2c2cf2cf838387a0c3a0c70c38383038838383831f3071f301c1f300cf3001701c17135d35c71c71d34d34c00b3cb3c71c71cb3cb3c00b3cb3e0e0e0e0e0e0c020e0e0e0c71c7cc71c76c71c71c76c00001ccc0005c017006c6c01c1b1b001700005db6d71c71c76db5d5e76d00012702cf2cf1c71c72cb3cf2cb3cf0000f0b02cf2cf83838383a0c3a0c30000320838383831c7cc7cc1c01f300cf305c001c17136d35c71f31c7cd34d34c0130b3cb3c71c71cb3cb3c00b0b3cb3e0e0e0c3830e0e0c0220e0e0e0c71c76c71c7cc71c71c76c00001ccc0009c017006c6c01c1723001b1b000176db5c71c71c79d79df5f9d7400047c0b3cb3c71c71cb2cf3cb2cf3c0003c2c0b3cb3e0e0e0c3830e830e830c0000c820e0e0e0c7cc7cc1c71f35d75c71d700330cc0005d75d71c71c75d75d7002cf2cf1c71c72cf2cf002cf2cf83838383a0e8300838383831c71d71c71f3071c0001c75c00000331705d75d71c71c75d75d7002cf2cf1c71c72cf2cf002cf2cf83838383a0e830083838383 24 16777215 10 1023
def hc_65_13 : Nat → Nat := unpackHintV5 0xe929eae181ead5a2f8ccf22cc79956bcbab8b511eaadf9c6a7c98ca1619a9a79ba94119a8d69aa88394c8051fa784a027111ce6999de6231da5c198651d2924b01b440929c39d9ae3311b22c51b025f9961f29b41851b61201940d193a000346 0x1d71d74d34c71c74d74d351d4d74c4c4c1c4d304d304d5d34d4d347574d34c530b3cb3cb1c73cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c75c75d7171c71c178e35c6c8e3078c6db05db05db6d79c71e79d7579d238c2cf2cf2c71cf2cb3cf2cb3cf0f2c2cf2cf83838383a0c3a0c3038838383831d701c71c1c75c01c71c71c71c75c71c71c71c74c78c74c071c05ccd35c135db1d3071c1d31d1c71d4d74d74d74eb4eb4d71c71c7134c1cb1c71c71cf2cf2cf2cb3cf2cb3cf1c71c70f2c2cf2cfa0c3a0c38383a0c3a0c38383038838383830175d75d34d3ad3ad34c6ccd34c134d34c4c5355536355555154c455305354d51d4154c152cf2cf2cb3cf2cb3cf2cf2cf0f2c5554f4b58383a0c3a0c383830385554365838301d35e74c7ad35d571c71d54ebad34d34d35ccd3134c1313135d353534d3534b3cb3cb2cb3cb3e0e0e0e0c1534d300555d75d74c74d34c74d34d39d3ad34c6ccd34c134c134c134d34c4c4d353574d34d34d38d54d8d3534534d30b3cb3cb2cf3cb2cf3cb2cf3cb2cf3cb3cb3c3cb13cb60e0e830e830e830e830e0e0c0e10e60e0c75c75d75d5b575d34d34c4c4c0704d304d304d753574d3474d4d354d3514c2cf2cf2cb1c72cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c30384398383054d7c7db6df9c74d31e74c4c4db04db04c4c4d4d4e38d3534634e30b3cb3cb2cf3cb2cf3cb3cb3c3cb13cb60e0e830e830e0e0c0e10e60e0c06db8c71e31b336db06db6e3231b6e36348e30b3cb3cb2cf3cb2cf3cb3cb3c3cb0b3cb3e0e0e830e830e0e0c0e20e0e0e0c76c76c71d36d34d31c140000000001353534d19d34d30002cf2cf2c71cf2cb3cf2cb3cf004f2d83838383a0c3a0c30043983831db6c76db1c76db6db6c700000000001b6db6df1c79df7d7df400b3cb3cb1c73cb2cf3cb2cf3c00b3cb3e0e0e0e0e830e830c020e0e0e0c76db1db6c0001b5b6db6d534d300004d4d4d3474c0005002cf2cf2c71cf002cb3cf2cb3cf4f2d8383838300a0c3a0c343983836db6db00004d6db4db54e71d31e700004d6d36d4d4d00000b3cb3cb3cb3c00b2cf3cb2cf3d3cf2d3e0e0e0e0c02830e830d83a60e0db6db6c6ccc00006c001c006db6db000100b3cb3cb3cb3c0003c2c0b3cb3e0e0e0e0c0000c820e0e0e0c76c76c71d36d34d31d34d51d4db4db4c4c4c1c4d304d304d4d4d351d9dcd34d314c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c303860e983831db6c76db1c706c6c76db6db1b238c1e3238c238c1b6db6e71c79e79d9e748e30b3cb3cb1c73cb2cf3cb2cf3c3cb0b3cb3e0e0e0c3830e830e830c0e20e0e0e0c76c76db5b6db6d534d34c4c4c1c4d304d304d4d4d3474d4d354d3514c2cf2cf2c71cf2cb3cf2cb3cf0f2c4f2d83838383a0c3a0c30384398383056c4d4c79e71d36db6db4e304e304c4c4c4c4db6d35b4db53534634e30b2cf3cb2cf3cb3cb3cb3cb3c3cb13cb6830e830e0e0e0e0c0e10c390e0e0c06c76db6c76db6db6db6db6c06cce3231b6d6db6d6db6db238c2db2cb3cf2cb3db3cf2cf2cf2cf2cf0f2c2cf2cfa0c3a0c383838383038838383834f300cf301f31c7cc0704c1f0007135d35d34d34c71c71c00b3cb3cb3cb3c71c71c00b3cb3e0e0e0e0e0e0c0020e0e0e0c75c71d71f31c71c71c71c005ccc0001c0001701c1c001c0007001c1c005d75d71c71d1df1d1c71c700011f02cf2cf1c71cf1cb1c71c71c70000f0b02cf2cf8383a0c70c387a0c3838300000c30a0838383831f35c7cc1f300cf313004c17001f135f34d7cd31c75d34d34c0130b3f32cfccb1c73cb3cb3c00b0b3cb3e0e0e0e0e0e0c0028838383831c75d71d71f31c71d75d70017330000017005c17001c1c05c8c001c1c0005d76d75d75c71d75d75d5df5d00011f02cf3cb3cf2c71cf2cb3cf2cb3cf0000f0b02cf2cf83838383a0c3a0c300000c30a0838383830175d75d31d75c74e30331b01b00136d35d38d3534d4d74c00b3cb3cb2cf3cb2cf3cb3cb3c00b3cb3e0e0e830e830e0e0c020e0e0e0c75c7071f3cc71d7cc71d7330cc000005d75d71c71c77c75d75d7002cf2cf1c71c72c72cf2cf002cf2cf8383831e1c3838300838383835d75c71c71f3071c75c7000000000331705d75d75d75d75d75d77d7002cf2cf2cf2cf2cb3cb2cf002cf2cf83838383838300838383831d71d74d34c71c74d70500000000004d4d4d34574d34c00b3cb3cb1c73cb2cf3cb2cf3c013cb60e0e0e0e830e830c010e60e0c75c75d75c71c75e30000000000176db5e71c79e75d5e7400b3cb3cb2c71cb3cb2cf3cb2cf3c00b3cb3e0e0e0e0e830e830c020e0e0e0c75c75c000175d5b575d34d300004d753574d3471c74f300011d0002cf2cf2c71cf002cb3cf2cb3cf4f2d8383838300a0c3a0c343983837db6df00004e354d7d39c74c79c00013535353400002cf2cf2cf2cf002cb3cf2cb3cf4b3cb2d8383838300a0c3a0c343983836db001b33000001c006db000100b3cb3cb3cb3c0003c2c0b3cb3e0e0e0e0c000030c2820e0e0e0c71c7cc71c76d75e76db6db6db5d70071c71c76d74d78c017171b4db6d71b01ccc71c071c76d31705d74e305db6d71df1c71c77e77d7e77d6d35d5d36d1f7c2cf2cf1cb1c71c72cb3cf2cb3cf2cb3cf2cb3cf0f2c2cf2cf83838383a0c3a0c3a0c3a0c303883838383 24 16777215 10 1023
def hc_65_14 : Nat → Nat := unpackHintV5 0xf94128f560f8ed5204e282b4dc119cd24274c5f314bea9d2b69a04b19142ab11a0a5616ca0a1309969ce901a548562ae7ef19c753a6e69030e6139f25c314255b1a050016c4b41304409ce3ad24e34a18c278b461ad32e0edafe0771da0001dc 0x6db6db1c71c71c71c76db6db1c71c72cf2cf2cf2cf1c71c72cf2cf838383838383838383831c71c76db6db1c71c75555552cf2cf1c71c72cf2cf558383838383835583831c76c71c71c71c71db1f31c7071c71b6db6c71c71c71c7471c71d6db6db1c71c71cb1c71c71cf2cf2cf1c71c72cf2cf2cf2cfa0c3a0c3838383838383838383831c75d71d71f31c71d75d75d75d75d7005c5c5c1c17175d38c175df5d75d75c71d75d35df5d35d75d75d5df5d1f7c2cf2cf2c71cf2cb3cf2cb3cf2cb3cf2cb3cf0f2c2cf2cf83838383a0c3a0c3a0c3a0c3038838383831f35f31f3cf3175d75d75c00005c5d75d75c71d75d75d77d7002cf2cf2c71cf2cb3cb2cf002cf2cf83838383a0e8300838383831c75db1db1f31c71d76db17001f001700001c06c06c01c07c8c05db6d77c71df5df7df7df5df007c011f02cf2cf2c71cf2cb3cf2cb3cf002c00f0b02cf2cf83838383a0c3a0c300800320838383831c75db1db1f31c706db5c76db01c77db1c71d76db005d71b177df07275d75d75d38c05c5db6d77c71df7df7d7df7d5d37df7d35df1f7df7c2cf2cf2c71cf2cb3cf2cb3cf2cb3cf2cb3cf0b3cb2c2cf2cf83838383a0c3a0c3a0c3a0c320e8838383831db1df4d704c4d34e701c4d34c4c4c1c4d304d304d4d4d1d4d34c534d30b3cb3cb1c73cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c76c77c71c131f1d36c07236d38c4c4e307138e34db4df4c71d34d4e34d134e30b3cb3cb1c73cb2cf3cb2cf3c2cf2cb0b3cb3e0e0e0e0e830e830c83a20e0e0e0c7cd7cc7cf3cc5c05c05d75d75c71d77df7df2cf2cf2c71cf2cf2cf2cf2cf838383838383838383831f35f31f3cf307017005c1707c5d75d75c71d77df7df0004c2cf2cf2c71cf2cf2cf0002cb0b3cb3e0e0e0e0e0e0c0028838383831c75d71d71f31c71d75d70000000055555555002cf2cf2c71cf2cb3cf2cb3cf005583838383a0c3a0c3005583831d7cc7cc1c04c04d34d34c71d34d34d32cf2cf2c71cf2cf2cf2cf2cf838383838383838383831c75d71d71f31c71d75d70000000170175d75d71c75d74d77d74d75c00b3cb3cb1c73cb2cf3cb2cf3c00b3cb3e0e0e0e0e830e830c020e0e0e0c71d75c75c7cc71c75d75c00000005c1705c17230175d75d71c75d75d77d77d75c000107c0b3cb3cb1c73cb2cf3cb2cf3c0000f3c0b2c0b3cb3e0e0e0e0e830e830c000030c2820e0e0e0c71d75c75c7cc71c75d75d75d75d75d5575d75d71c75d74d77d74d75d75d7177d71757574755d5d74d575df7d7d2cf2cf2c71cf2cb3cf2cb3cf2cb3cf2cb3cf2cf2cf4f2d83838383a0c3a0c3a0c3a0c3838343983831f35f31f3cf3575d75d75d75d75d71c75d75d75df5d55555d552cf2cf2c71cf2cb3cb2cf2cf2cf5583838383a0e8383835583831c75db1db1f31c71d76db5db6d77c71df5df7df7df5df57555f5557555555f51d56d56d51d57d455f454b3cb3cb1c73cb2cf3cb2cf3cb3cb3d54b553d2d60e0e0e0e830e830e0e0d56550d960e0c71d76c76c7cc71d5b6d71db6d471df6c71c75db6d5576db5df1c77df7df1f7df174df7df4d77d75d6d5df7d1d9d75d75d74d55d7d7df7d2cf2cf2c71cf2cb3cf2cb3cf2cb3cf2cb3cf2cf2cf4b3cb2d83838383a0c3a0c3a0c3a0c3838360e983831db1df1c754d7c74db51d9db4db4df4c71e74e34c4e34c4d4d4d1d4d3534b3cb3cb1c73cb2cf3cb2cf3cb3cb3d2cf2cb60e0e0e0e830e830e0e0d83a60e0c7cd7cc7cf3cd5d55d55d75d75c71d77df7df2cf2cf2c71cf2cf2cf2cf2cf838383838383838383831f35f31f3cf3475575575d75d71c75df7df7d5d5757d555352cf2cf2c71cf2cf2cf2cf2cf5552cb60e0e0e0e0e0e0e0d556983831c75d71d71f31c71d75d70000000055555555002cf2cf2c71cf2cb3cf2cb3cf005583838383a0c3a0c3005583831d7cc7cd1d54d54d34d34c71d34d34d32cf2cf2c71cf2cf2cf2cf2cf838383838383838383831c75d71d71f31c71d75d75d75d75c71d75d35df5d35d75555555575554b3cb3cb1c73cb2cf3cb2cf3cb3cb3d560e0e0e0e830e830e0e0d560e0c71d75c75c7cc71c75d75d75d75d71c75d75d77d77d75d55555555d555755d575155f5152cf2cf2c71cf2cb3cf2cb3cf2cf2cf55553cf52cb583838383a0c3a0c3838355550c35a583831c76db1db1f31c71db6db6db1c706db1c752cf2cf2c71cf2cb3cf2cb3cf2cf2cf2cf2cf83838383a0c3a0c38383838383830075c71d31e3001c1c1c71c71d71f31c71c71c71d71c71c71c71c71c717335d705d76c71c1c071d38c0707175d75d75d7577d7471c7474c7471c71c7df0b3cb3cb2cf3cb2cf3c71c73c72c71c71c71c3cb0b3cb3e83a0e830e830e831c30e1e830e0e0c0e20e0e0e0c01c75d71d71f31c75d75c75c71d75c71c71c71c7005c1c5d35e35d75c5ccd75c175db5c1c5d31705d74e305d75d75d75d5df5d5c71d75d35d5d35d1f7c2cf2cf2cb3cf2cb3cf2c71cf2cb3cf2cb3cf0f2c2cf2cf8383a0c3a0c38383a0c3a0c3038838383830075d71d75c74c78c71d34d78d7175c71c071c71d34d317334d704d76d34c1d3134c134c135d35d35d3ad39d35d31c75d34d7534d744d30b3cb3cb2cf3cb2cf3cb1c73cb2cf3cb2cf3c3cb0b3cb3e0e0e830e830e0e0e830e830c0e20e0e0e0c75c71c71f3cc71ccc71d71ccd7331c7074c5c1c5d75d71c71c75d75d71f7c2cf2cf1c71c72cf2cf0f2c2cf2cfb30ecc3831e1c38383038838383835d75c71c71f3071c75c75d31c017171717174c5d75d3cc5d75d75d75d75d75d71f7c2cf2cf2cf2cf2cf2cf0f2c2cf2cf83838383838303883838383 24 16777215 10 1023
def hc_65_15 : Nat → Nat := unpackHintV5 0x7551dedb03e99727baf08f755d2109cb3bd1a87b9f74f73781da6073a49f6860f61231709ee2631f835c5a82e0f6000170 0x135c13134c71c71c71c7071c1313071c071c07071353534d31c7474714d34c2cf2cf2cb3cf2cb3cf1c71c70f2c4f2d8383a0c3a0c3838303843983834e304c7c71c71c71c7071c138c4c1c71c7071c7136d37d34d4e34d1c71c7134c2cf2cf2cb3cf2cb3cf1c71c70f2c2cf2cf8383a0c3a0c38383038838383834d535f1c71c71c71d1c754db4df4e34c4e34c1c71c74d4d1c71c7471c753534b3cb3cb2cf3cb2cf3c71c71cb3cb3d3cb60e0e830e830e0e0e0e0d0e60e0c71c76c7cc71c71c71c76db1c71c1c7071c71db6c71c7471d1c71c72cf2cf1c71cf1cb1c71c71c72cf2cf2cf2cf8383a0c70c387a0c383838383838383831c71db1c71f31c71c71db5db6d71c71c75e37c7e35c5db6d71c71c75df5f5d7df7df2cf2cf1c71c72cb3cf2cb3cf2cf2cf2cf2cf83838383a0c3a0c38383838383831d71d74c4d34db04e701c4d34c4c4c1c4d304d304d353574d1d4d34c534d30b3cb3cb1c73cb2cf3cb2cf3c3cb13cb60e0e0e0e830e830c0e10e60e0c75c75d3171c71c138c07174c6d36c4e307136db4db4d74c71d34d4e34d134c2cf2cf2c71cf2cb3cf2cb3cf0f2c2cf2cf83838383a0c3a0c3038838383831d71d74d5c71c754d47574db4d74c71e74e34c4e34c4d6d36d4d1d4db6d3534b3cb3cb1c73cb2cf3cb2cf3cb3cb3d3cb60e0e0e0e830e830e0e0d0e60e0c76c7cc71db6c71c76db6db6db1c76db6c6db1b6db6c71db6db5b6d2cf2cf2c71cf2cb3cf2cb3cf2cf2cf2cf2cf83838383a0c3a0c38383838383834db04d34c1c701c71c1c71c71c701c704c4c1c1c4d34d35347474534d30b2cf3cb2cf3cb3cb3c71c71c3cb13cb6830e830e0e0e0e0c0e10e60e0d36c1b6d3071c071c7071c71c71c74c6d36c1c1c71c4e34d4d3536d36c71c71c4d30b2cf3cb2cf3cb3cb3c71c71c3cf2c3cb3cb3e830e830e0e0e0e0c0c380e0e0e0e0d36d5b6d3471d471c7471c71d38d3138d3136d36c71c71c71c74db5b4db5b1c7471c7474d4d2cb3cf2cb3cf2cf2cf1c71c72cf2cf4b3cf2cb4fa0c3a0c383838383838360c3a4383830134d34d34d35d36d34c71c71c71c71c71c71c71c71c4c4d304d34d31307070b3cb3cb2cf3cb2cf3cb3cb3c71c71c3cb20e0e830e830e0e0e0e0c0e20e0d34d34c71c71c71c1c4ccc0000b3cb3cb3cb3c71c71c020e0e0e0e0e0c020e0d34d34c71c71c71c1c4c0000001304c04c01c01c002cf2cf2cf2cf1c71c70000f0b0838383838383000032083830136d3534d35d34d34c71c7471c71c71c71c71c71d34d34d3013334c4c1c1c2cb3cf2cb3cf2cf2cf2cf2cf1c71c70f2ca0c3a0c383838383838303883834d34d31c71c71c70700133300001305c06c01c01c002cf2cf2cf2cf1c71c70000f0b083838383838300003208383 23 8388607 10 1023
def nh_65 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_65_15 (Nat.sub p 480)) (hc_65_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (hc_65_13 (Nat.sub p 416)) (hc_65_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 448)) (Bool.rec (Bool.rec (hc_65_11 (Nat.sub p 352)) (hc_65_10 (Nat.sub p 320)) (Nat.blt p 352)) (Bool.rec (hc_65_9 (Nat.sub p 288)) (hc_65_8 (Nat.sub p 256)) (Nat.blt p 288)) (Nat.blt p 320)) (Nat.blt p 384)) (Bool.rec (Bool.rec (Bool.rec (hc_65_7 (Nat.sub p 224)) (hc_65_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (hc_65_5 (Nat.sub p 160)) (hc_65_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (hc_65_3 (Nat.sub p 96)) (hc_65_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_65_1 (Nat.sub p 32)) (hc_65_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 256)
def f_65 : Nat → Nat × Nat := unpackForestF 0xf7a5df6b55f6a5500c5ff445ef524df4345f424500c5bf3265eeb6deea6defa5ff136cefa5befa57efa53eea6ceea6000c57e2b4fed45ce2b4be2b47eba4de2b45eab4ce8c54e8a38e9344e8a34e2b43e2a4fe735ce2a4be2a47e2a45e524ce3354e324ce3a44e3244e2a4300c53dbc6fdbc63dbc5bdf56edf562df245dbc59dbc57dba5bdd461dba57dc451dba5500b5fdaa45d935ed9b52d923500b5bd8245d6c61d7469d6a6d00b57d5c64d0d6fd4c54d0d63d0b6ed256ed2562d2245d0b5ed1352d0a3500b53c856bc8563c846fcc469cc461cc255cc05acc056c846ec8467caa45c8462c824bc8247c8c62c824500b4fc7255c5b6ec6362c5a3500b4bc4a45c3562c3d6ec325d00b47c2454bc56bc1454bc563bec69bec61bec59bea55bc36ebdc6ebc35ebcb62bc23500b43a546fa5463ba254a545fb956ca545bb7d6eb7d62a5459a5457b646cb5564b5244a5453a536fa5363b3254a535fb1d69b1c6ca535bb0459b0455a5357aec61aeb52a5355adb6cacc64aca34a5353ab46cab464a534fa936ca9364a9234a534ba7568a7560a725ca5347a5b6ca5b64a534300a5fa42549e45fa32449e45ba1e70a1a6c9e457a0344a02449e4539e25e9ec529e24600a5b9cb4b9cb4795c619bc5995b6d9ac7c95b4f995709937c95b4b9857095b47965709637c9623495b4300a5794b6486d6f93b5486d6392b6486c6f91b4486c6390a5486c5f8f3448f24486c5b8d6708d36c8d26c86c578c24486c5386a6e8956e895628935d8935586a5e87452873628735a86a4600a5364d6b64d6364c6f82c6982c618285a8285664c6e8157c8124464c6b64c677fc6c7ed747ea4464c637cc6d7cc5d7ca4664c627b4687b46464b6f7935c793547923464b6b7747c774707727c64b677536c7535c7535464b6364b5f73b647357e64b537224464b4f7145c64b4b64b476ed626ec6b6eb4264b456db5c6cc546ca3464b436b5686b47c64a6f68c5a68c5668b6d68b6564a6e675706746c64a6766234653536524664a6200a4f63a645dc6f62a445dc6b615706127c5dc675fb445fa445dc635da6e5e4625da4600a4b525625c5685236f5ae705ab6c5236b59d7052367576705736c5735c57234523635646e5235d54d7054c685226f52d7052d6052c705226700a4750c5550b543ad6b4fa5c4ec554eb543ad634da643ac6f4c3444c2443ac6b4a5704a37c4a27c3ac6748c7e48a443ac6347a6446d7e46b543ac5f4547e453443ac5342b5b42b574324542a563ab6e3fc693fc613fc59403643fb433aa6e3dc6e3dc623da6e3aa5e3b56b3b4623b36a3b3523aa4600a4339b642cd6f38b542cd6b3737c3727c2cd6735c5435b542cd6334c592cb6e3346e334622cb5e31c6431b7c2ca6f3047c3036c2ca672ec542eb6c2ca5f2d46c2d35c2ca5700a3f2ba6422d6f2aa5422d6b2937c2927c22d6727b5427a5422d6326c5922a6e2446f2446e244672446222a5e2356722a4600a3b21c6809d6f20c5809d6b1ec711ec701ea7c09d671d4581d25409d631bc591ba5509c6e1ab5c09c6b09c6317569175611735e1703a1703609c6215c6e15a4509c5e1457a1435c09c5b1257a12b441257209c53113550e56e0e5620e36f0e36e0e3670e36209c520d47009a6f0c46009a670b46009a5f0a45009a5700a3708a640156f07a540156b0637c0627c015670525401563044590126e01d6a01d6601c6e01c620125e00a330003f 9 11
def ch_65 : Nat → Bool := dagCheckNodeV5 fullMask g_65 ep_65 4 15 bds_65 496 (dagTraceF fullMask rootStock 11 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 fullMask g_65 ep_65 4 15 496 bds_65 (dagTraceF fullMask rootStock 11 f_65) (cur_65 0) (nh_65 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 32 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_1 : treeBlockF 32 64 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_2 : treeBlockF 64 96 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_3 : treeBlockF 96 128 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_4 : treeBlockF 128 160 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_5 : treeBlockF 160 192 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_6 : treeBlockF 192 224 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_7 : treeBlockF 224 256 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_8 : treeBlockF 256 288 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_9 : treeBlockF 288 320 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_10 : treeBlockF 320 352 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_11 : treeBlockF 352 384 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_12 : treeBlockF 384 416 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_13 : treeBlockF 416 448 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_14 : treeBlockF 448 480 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_15 : treeBlockF 480 496 ch_65 = true := by decide +kernel
theorem nj_65_1 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_65_1 h1 h2)
theorem nj_65_2 : ∀ i, 0 ≤ i → i < 96 → ch_65 i = true := block_join nj_65_1 (fun _ h1 h2 => treeBlockF_at nb_65_2 h1 h2)
theorem nj_65_3 : ∀ i, 0 ≤ i → i < 128 → ch_65 i = true := block_join nj_65_2 (fun _ h1 h2 => treeBlockF_at nb_65_3 h1 h2)
theorem nj_65_4 : ∀ i, 0 ≤ i → i < 160 → ch_65 i = true := block_join nj_65_3 (fun _ h1 h2 => treeBlockF_at nb_65_4 h1 h2)
theorem nj_65_5 : ∀ i, 0 ≤ i → i < 192 → ch_65 i = true := block_join nj_65_4 (fun _ h1 h2 => treeBlockF_at nb_65_5 h1 h2)
theorem nj_65_6 : ∀ i, 0 ≤ i → i < 224 → ch_65 i = true := block_join nj_65_5 (fun _ h1 h2 => treeBlockF_at nb_65_6 h1 h2)
theorem nj_65_7 : ∀ i, 0 ≤ i → i < 256 → ch_65 i = true := block_join nj_65_6 (fun _ h1 h2 => treeBlockF_at nb_65_7 h1 h2)
theorem nj_65_8 : ∀ i, 0 ≤ i → i < 288 → ch_65 i = true := block_join nj_65_7 (fun _ h1 h2 => treeBlockF_at nb_65_8 h1 h2)
theorem nj_65_9 : ∀ i, 0 ≤ i → i < 320 → ch_65 i = true := block_join nj_65_8 (fun _ h1 h2 => treeBlockF_at nb_65_9 h1 h2)
theorem nj_65_10 : ∀ i, 0 ≤ i → i < 352 → ch_65 i = true := block_join nj_65_9 (fun _ h1 h2 => treeBlockF_at nb_65_10 h1 h2)
theorem nj_65_11 : ∀ i, 0 ≤ i → i < 384 → ch_65 i = true := block_join nj_65_10 (fun _ h1 h2 => treeBlockF_at nb_65_11 h1 h2)
theorem nj_65_12 : ∀ i, 0 ≤ i → i < 416 → ch_65 i = true := block_join nj_65_11 (fun _ h1 h2 => treeBlockF_at nb_65_12 h1 h2)
theorem nj_65_13 : ∀ i, 0 ≤ i → i < 448 → ch_65 i = true := block_join nj_65_12 (fun _ h1 h2 => treeBlockF_at nb_65_13 h1 h2)
theorem nj_65_14 : ∀ i, 0 ≤ i → i < 480 → ch_65 i = true := block_join nj_65_13 (fun _ h1 h2 => treeBlockF_at nb_65_14 h1 h2)
theorem nj_65_15 : ∀ i, 0 ≤ i → i < 496 → ch_65 i = true := block_join nj_65_14 (fun _ h1 h2 => treeBlockF_at nb_65_15 h1 h2)
theorem nc_65 : ∀ i, 0 ≤ i → i < 496 → ch_65 i = true := nj_65_15
theorem lb_65 : LowerBin fullMask rootStock g_65 12 :=
  lowerDagV5 (kn_cons lb_58 (kn_cons lb_57 (kn_cons lb_62 (kn_cons lb_61 (kn_cons lb_59 (kn_cons lb_64 (kn_cons lb_63 (kn_cons lb_45 (kn_cons lb_51 (kn_cons lb_56 (kn_cons lb_8 (kn_cons lb_60 (kn_cons lb_36 (kn_cons lb_24 (kn_cons lb_27 (kn_nil)))))))))))))))) rc_65 nc_65 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.and, [7, 14]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [13, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276808360 * 2 ^ 32 + 3972587648)) (13 - 1) := by
  rw [show canon fullMask (4276808360 * 2 ^ 32 + 3972587648) = g_65 by decide]
  exact lb_65

end PEqualNP.Outside.L_meta_48404

theorem PEqualNP.Outside.L_meta_48404 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48404.table2_from_lowerBin (4276808360 * 2 ^ 32 + 3972587648) 13 PEqualNP.Outside.L_meta_48404.root_lb PEqualNP.Outside.L_meta_48404.wg 18 rfl PEqualNP.Outside.L_meta_48404.wfits PEqualNP.Outside.L_meta_48404.weval
