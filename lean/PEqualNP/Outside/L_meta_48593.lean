import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48593

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

def m_0 : Nat := 0xff000000000000
def s_0 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_0 : Nat := 0x17000000000000
def ep_0 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_1 : Nat := 0xf0f000000000000
def s_1 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_1 : Nat := 0x107000000000000
def ep_1 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_2 : Nat := 0xf000f0000000000
def s_2 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_2 : Nat := 0x100070000000000
def ep_2 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_3 : Nat := 0x3030303000000000
def s_3 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_3 : Nat := 0x10103000000000
def ep_3 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_4 : Nat := 0xff0000000000
def s_4 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_4 : Nat := 0x170000000000
def ep_4 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_6 : Nat := 0xf000f000000000
def s_6 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_6 : Nat := 0x10007000000000
def ep_6 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_7 : Nat := 0x3300330000000000
def s_7 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_7 : Nat := 0x100130000000000
def ep_7 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_8 : Nat := 0x2222222200000000
def s_8 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_8 : Nat := 0x2022200000000
def ep_8 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x4444444400000000
def s_9 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_9 : Nat := 0x4044400000000
def ep_9 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_10 : Nat := 0x5050505000000000
def s_10 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_10 : Nat := 0x10105000000000
def ep_10 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_11 : Nat := 0xcc00cc
def s_11 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_11 : Nat := 0x4004c
def ep_11 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
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

def m_12 : Nat := 0x5500000055000000
def s_12 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_12 : Nat := 0x100000015000000
def ep_12 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_13 : Nat := 0xf0f000000000
def s_13 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_13 : Nat := 0x107000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_14 : Nat := 0xc000c000c000c00
def s_14 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_14 : Nat := 0x40004000c00
def ep_14 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_15 : Nat := 0xf0f0
def s_15 : List Nat := [0x5050, 0x3030, 0xf0]
def g_15 : Nat := 0x1070
def ep_15 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_16 : Nat := 0x3030000030300000
def s_16 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_16 : Nat := 0x10000010300000
def ep_16 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
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

def m_19 : Nat := 0x33cc33cc
def s_19 : List Nat := [0x11441144, 0xcc00cc, 0x30c030c, 0x33cc]
def g_19 : Nat := 0x1104134c
def ep_19 : Nat := 0x2480000000000000000000000000004020800000000000000000000000011041040
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def nh_19 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x3300cc003300cc
def s_20 : List Nat := [0x11004400110044, 0xcc000000cc, 0x3000c0003000c, 0x3300cc]
def g_20 : Nat := 0x1300440033004c
def ep_20 : Nat := 0x20000800000000000000000000000000000000000200000000000800000000000000000010004400000040
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_20 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 10 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 10 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 10 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 10 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00000000ff
def s_21 : List Nat := [0x550000000055, 0x330000000033, 0xf000000000f, 0xff]
def g_21 : Nat := 0x17000000007f
def ep_21 : Nat := 0x6000000000800001200000000200000140000000040
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8428408027657607607226e26e06e06a26626416406216206016005e15645415405215205015004e1464460270032001 0x106901fd002a92024240a4681d53038a20203405028194901a0a0613006068154d00a0a05120020480d4d0221203c2406840125002098038400606805490121a01c34028200a4c0109001830020482a938532509a4611c84228f8431d07a360dc641a5282ea30593a09a6c0b118061b0082e0103d7c8fee91ddb6379fc67394fe629dc91377b266eb4bdb895b0527442467f0fcda1b9782f2004e2b07c020b8000f 12 4095 5 31 10 1023 19 524287
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9866094650942508ca308c221791e0781e0709c0701b15d09e24090240901c870148050000000000 0xe130c120d9243414d934e244dd3cd5344814b9341414b924c234bd4cb5442814fe4afa46f63af236ed4ee94ae546d142cd3ec93ac536b13208260816a24c9e40653444346244953c913440444814 10 1023 4 15 10 1023 16 65535
def cc_21_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc1d80300600c0170ae05829cb382704a28c51823042270ae01c0342604b85702c1580a855028140880008000 0x36695af46d5276992b448d8e42c49ee14d5125b8129be92ac486086d0426b6a65a502a4692034a7a2584a2ba491c4492125449220494e30861a4c49038292e34a0a64f51030482814989a050525a401014891a48052302911209320478c22a810d34bba75cd2ace8d5b42ab255291a8a7ac9393c9ace4c66a5b29258423410fa085c0c16 11 2047 5 31 10 1023 17 131071
def cc_21_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc1782d1505a0140261482901202213a5740e81b13226404c090101200400800c21803005082404000400000 0x798d23049e344fa947c49228692424f29244093c4610c24e29a0f0538489d53ce89a0e0909029c5241a0a704c06029fa4dd324d9917dc83ea3def1af6535d2929945e6a0f24f77a6bb84edc1f42098582d9e30ca92440932c699f44cc94644924848c120 11 2047 5 31 10 1023 17 131071
def cc_21_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x8408217c37827807807616e46a26a06816806615c55c05a15815615605605604c52162001e11e01e01e01c11c01c000e 0x9e4927e349d5123414994d01414994926e349a53261440a052543c930d25524934925a349413248448e0f2342c908d0152405492392d8d4aa31268b4962924a18f6723abf8daf635ba8d2e54eb7536d94cb152abd46ad516a544a450a8d3ea14f6812e9c4b4b01d9706a44168f0562414678c0e130879361a455d8f61639848d58e318353609452a4f60539804d4d1316e119b836 12 4095 5 31 10 1023 18 262143
def cc_21_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0313c4310972508c9f47c1d2705c06c58360171548f63c0f03c0a5280a0280a0190601442308002 0xab512f93c8b052e13db54eac136ae4d6a934bc4baed2d300766c1a9605a40158a052793495052e234b45126818940527934b30527924b3492d634b4512c814b0492641893052ba34a8532893c9d4b2601892052892d9d4aab126ab496a924a85329d3ca64b294149e4927e34a251238149e4d01414 10 1023 4 15 10 1023 18 262143
def cc_21_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a49a07727607607607417026656416216205e25e05a25245014e14e04a24a0462460460403384361341340077060003 0x27e34a8532d1440a053aa4ae991ba23ee78f70e359c8cb994ee552b9146e050b7d36c34d7792e9c4b4f42d16094c81ddd057644cd38d33034d2d135234cb5133524d7092d520c84d31d24d30927934d10535240d28c34140c64d2d520c78d32124cc0527934ca0527a30c84c31d20cd9032e30c950319349f4b27d2cdbd3b6b4ad8d1b5b42d592b3e46c38fa823dce52b1546c44fa8d3dc44bb0d29bf48af521ba483083d1e0d5842d4a094f01d13056b144c04f23014 12 4095 5 31 10 1023 18 262143
def cc_21_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a08818618418408408407a54f64c14a14814804804424404213c33c01921611411211010e10e00e00a20a0081023001 0x3fa4406a680d4d1f89ebed3a7d26cf94d5f09a46e4d854952291a4122c76448e29d1b536349f4613d8ba78e04ea2a9b44d3587268a44ca1a974292d1a03b05069fe0b3f4157b828a78d1e11829e3863a48ef091df1a3c34466a48ee091eba53d34679c9cf2929e3233b6426f47ca18f5d09d39d396226ca14c5889337d253107a4d0d44416bb02553248e34c180922f93453270c8491c40a3893471c88d44d1c20a27d20 12 4095 5 31 10 1023 19 524287
def cc_21_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe82ecb82b3ac2929525094241889c66c5b06c1b0595605093140ce2380e0344941c8701846014405 0x23e9f4793d8ca5ae34aa2c934512587a4838076120d410167f02af80521922449347e028c8492060a466446a26908062040a45944838310105229224494c53a790b4b20c0c4001464269124f6169d445368826b0f4d1909203414642690c912169a3ec1483a480d0520e9a4264484279064d0240a40c2c80849034d2029a412447e099020f2001a3ec2c 10 1023 4 15 10 1023 19 524287
def cc_21_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xba1b81b61b60b609329018e18c18a18a08248205f25e05a25054e14e04a24a04623e43c13a13a00d70c0063060003000 0x151a23c2305449933d3a37a6cfa4d9ec8adb8f6791ccee3576c633852a6ea4c9d468da83274da6c9aa0c4d3908a2a0f6741ac8d3490a890c4c14c944324453a78d44d0240a4e24e9bc9b2691615213aa3a6746d3651a4ca2cd53e72a75344d962994cd2e8525a3f0b434128e81d9902b2c8d194124af445a488c94d19a924bc2471a60c749258123212495028b4d0257184a540632490c8f2189649b4e86e9b30935e524b6245974832d8f6511ac9d4e8e29b274fa4c9cc8932902631d4c1d295315269289a26115041e9bc351f03a1705646a6445247d02921532209a3e414 12 4095 5 31 10 1023 19 524287
def cc_21_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81f03c16c6d81a8740e61cc1983305c5b05602c05619c928a50481901185e2bc0742e05b0b606c0d8162816 0x2a00c52814ae68958532ae9e2992ca783149052b5a231e3463c69588f6af1d55a36aac6b548d2a09211024a846952d12a29453d24248494c062940a53234a54694dd128aa65113ca5831490528fa21123422469458f6891d50e36a146b418d2c9a6d874ab5e8d69d16cda25964eb249b638fac31ebb52dafa555e4a6ba9456d26aca4b53491489098c2da70554809a8c12d0024 11 2047 5 31 10 1023 19 524287
def cc_21_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xd80d80b52b21b01ae1a64a41a40a408127e17c17c07826e56e04174003a33a03433403401cc1c01631601220c3082004 0xbc69d64d36f7255ea49b9c8d64906e71b5e6359f29b2d515b69edfd39bf26ae04c50e269e8452e87b7d0d6d91a5aa44b146162d114c943352424848a74f2f7a75eb4db968b61d0af3235ca45bc47d618f5ea9eb55357925b774a6ec92ac5213607a550d4d216dd425b1479628f2549a3452494c88d08d168a235134b802972d3ac7a6dce4eb2c9b738fae51cdae32b4c63668c2e2a6b95496c28b6f5067a9eca1357a25acf496dc26964454307a770d4d61694825b64995649286125aa4caaa4942092d11f59e3d7825b604aab89356925aa248670b6a41553426a384b41092c5a256124a2848c7490881258b44aba49440918e9253024b0688cd492a21452c24 12 4095 5 31 10 1023 19 524287
def cc_21_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x1 0x1514c 2 3 1 1 9 511 17 131071
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_21_12 (Nat.sub p 384)) (cc_21_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_21_10 (Nat.sub p 320)) (cc_21_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_21_8 (Nat.sub p 256)) (cc_21_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_21_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_21_5 (Nat.sub p 160)) (cc_21_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_21_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_21_2 (Nat.sub p 64)) (cc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_21_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_21_0 : Nat → Nat := unpackHintV5 0xa00a8009e0a50a8e1a3808c0a08a7c19f007a09c0a7001c006e09b806c09b00681178a5e017805c097005a09680561130a46189a00290002 0x14555111544450055401554011445101145145145 14 16383 6 63
def hc_21_1 : Nat → Nat := unpackHintV5 0xa22a60a8e29f907c09c0c6e09b806e01b806e017905c0940c4e093804e013804e00aa4280870c1c007001a08680180838a0c0800c0000000 0x5551555515555555155555541555414455555155555 14 16383 6 63
def hc_21_2 : Nat → Nat := unpackHintV5 0x9a926028c323008c022828a022027e29e067801d826c2980c600178254293864e01302422908042010024000f823e00e843028a860a8000a 0x15414455555551554445555455511140155401114404515 14 16383 6 63
def hc_21_3 : Nat → Nat := unpackHintV5 0xd233480d00b18ac01b000be0ad0aa832a00a60a70a961a580940a28a84199205a2940a4040f823230c023000c003000c00262870a0c4000c 0x15551554445555455511150014404514555545555555155554555555 14 16383 6 63
def hc_21_4 : Nat → Nat := unpackHintV5 0xde03780d81b582d603580d603580d40b500d403500d403482d00b382ce03380cc0b282c222a988499e8a7029810543128a4028c102430024 0x11515555555555555555411155554555555155554555555005115555 14 16383 6 63
def hc_21_5 : Nat → Nat := unpackHintV5 0x7f21e8a7431b8c626169058115844a61204480120048011463f30dd03418c842e20a88224059816005801600580131830e0c002460238004 0x155555555555555555555555555555455555555555555555555555545555155555 14 16383 5 31
def hc_21_6 : Nat → Nat := unpackHintV5 0x8f0d1c09d59378c6528ca017092d825614a03140028004f049e013812310401880010001f823f007c08f801f0038186040a86120c230412d0144000a 0x4555555555515455555555545555515555555555555555555455455555515455555555555 15 32767 6 63
def hc_21_7 : Nat → Nat := unpackHintV5 0xa0053e0a7c04f809e053a0a64446987a4ce831b86338e6118b2415c22b805700a8194c11d3234185c30a06110c1b1c2a3034805840b0016002030010 0x155555555555555554115555555555555555551555555545515555555555555555555555555515555 15 32767 6 63
def hc_21_8 : Nat → Nat := unpackHintV5 0xd866062c9d5869c84c12508f98706304168cac456027211906d01ec0838308180063020810008004002000840400200100080002 0x555555555555455555555555555555555555555555555555555555454 13 8191 5 31
def hc_21_9 : Nat → Nat := unpackHintV5 0xce1990330475c90b8053eca646498c8b210839f083c867804bec954a2a024f149231240240248008e08fc81c8c3318640861a0a080f141620185000c 0x5555555555555555555154555555555555555555555545555555555154555555545555555551551555455155555555555555555555 15 32767 6 63
def hc_21_10 : Nat → Nat := unpackHintV5 0xca42c98ac1aa049c323108c023008421f086c41518520948052014805201402500140050014004e093024a092804a012024608f882660026 0x1555555555555555555555555555555555515555555555555541155 14 16383 6 63
def hc_21_11 : Nat → Nat := unpackHintV5 0xd521a80aed95a8caf194e429034e8e95212809ed93a8c6f18ca519012f8a5e0488d10041d8a37106428b06130c1a302638403048e070808180820004 0x155555555515455555555555555515555555555555551545551551555555554554551555555555555555555555555555555554555555155 15 32767 6 63
def hc_21_12 : Nat → Nat := unpackHintV5 0xe 0x1555 8 255 4 15
def nh_21 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_21_12 (Nat.sub p 384)) (hc_21_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_21_10 (Nat.sub p 320)) (hc_21_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_21_8 (Nat.sub p 256)) (hc_21_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_21_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_21_5 (Nat.sub p 160)) (hc_21_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_21_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_21_2 (Nat.sub p 64)) (hc_21_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_21_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_21 : Nat → Nat × Nat := unpackForestF 0xbea737d4d6fa1a8063fbae9d75d36eb235d63ebaa5375496ea128063bb747d6e8e6dca6dc014b72836e134031bdb24ca068d6a93281a2d9e3eb3c7b40d1281275024da047d62d12811ed8344a0255404a6809457344a024d5ad128092d523daa475548daa91ad5234a02494fd129e9454234a7a49400aa93a253234a48314a8d2920a50026a3e8940096831ed063aa0c6d418d6831a5002400c673a9367522cea399d46b3a0d4029fcca4e9949b3251a649f4c9369925d32054029dc964d97849259064b1ecb02494c612a05252a04963592a7d254e64a268053791a98f791a42a63de458f27d1e4f5ef223dd4e7ba9af74fa33223dd3d7ba7916511ee9b452447ba6b0f4f61e9b43d3587a68f74d1ee9742e4485a68f74b60d224193c83a69064d1ee0d4024481a69000f2029a400347b82cfe911ee0abe13d7c274f84d9f09abe1347b828014cdd9a53b3467649cec929d9233bb4477c68ee091d9213b02500a5edd929bb233763e6ec7add539baa53754670c88e24d1c20a375426ea6cdd4b9ba0a8052b6169cc2d29b22630b466b848c2d0985253424069848d08c1a20a341406148cc25298d203301463460ca0518ca031d3063a40c64d184a33092e61252c20f40293b013c44c6cbe4f1131aaed2e5da5a898d112a72e23444a9a89531651a2c94459a48b205112a52c12444a8cae8d112a2aa9265524aaa49112a22954c52a78a54b14a0a2254244a7ca2511129ea252e4ec689e4913aa22252d4c4689853132922614444834928d12a922484c49a4892111120b242344482a8a4b51495229264524a8a491120a005234049a80915011ca02354029a80515009ca01350087e6e934f8941f124374826e8f4f2921e2303746a6e534e89e1d134372826e4f4e2921c1303726a6e0f8021b97f4a2fe8c5f938bf2517e4632688644a0cb1a191242fc845f4f4be9a97d292fa4a010bc83a71074a2d2985a50083a315d282ba4841d0883251512429c6041918829e93d4c27a88414c482969313425a404149487201201421c604605086a01112021a6841118821700427164942c918591d0b2361629c2c52858a30d6441aa78364d06a9a0b1421627c2c4e8589b0b63416a982e4905aa20b1320083e02938052509e4c13c8002918489e0913401484028f8051d07f480fe80028d838a60714401464025283292061300128c024e82a9a051200126c0c500221203130078480c1001a10030340108c044c0121a0112003868040c00a08010240106c02078020b8000f 9 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 384 (dagTraceF m_21 s_21 6 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 384 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) (nh_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 64 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_2 : treeBlockF 64 96 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_3 : treeBlockF 96 128 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_4 : treeBlockF 128 160 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_5 : treeBlockF 160 192 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_6 : treeBlockF 192 224 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_7 : treeBlockF 224 256 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_8 : treeBlockF 256 288 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_9 : treeBlockF 288 320 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_10 : treeBlockF 320 352 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_11 : treeBlockF 352 384 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 64 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nj_21_2 : ∀ i, 0 ≤ i → i < 96 → ch_21 i = true := block_join nj_21_1 (fun _ h1 h2 => treeBlockF_at nb_21_2 h1 h2)
theorem nj_21_3 : ∀ i, 0 ≤ i → i < 128 → ch_21 i = true := block_join nj_21_2 (fun _ h1 h2 => treeBlockF_at nb_21_3 h1 h2)
theorem nj_21_4 : ∀ i, 0 ≤ i → i < 160 → ch_21 i = true := block_join nj_21_3 (fun _ h1 h2 => treeBlockF_at nb_21_4 h1 h2)
theorem nj_21_5 : ∀ i, 0 ≤ i → i < 192 → ch_21 i = true := block_join nj_21_4 (fun _ h1 h2 => treeBlockF_at nb_21_5 h1 h2)
theorem nj_21_6 : ∀ i, 0 ≤ i → i < 224 → ch_21 i = true := block_join nj_21_5 (fun _ h1 h2 => treeBlockF_at nb_21_6 h1 h2)
theorem nj_21_7 : ∀ i, 0 ≤ i → i < 256 → ch_21 i = true := block_join nj_21_6 (fun _ h1 h2 => treeBlockF_at nb_21_7 h1 h2)
theorem nj_21_8 : ∀ i, 0 ≤ i → i < 288 → ch_21 i = true := block_join nj_21_7 (fun _ h1 h2 => treeBlockF_at nb_21_8 h1 h2)
theorem nj_21_9 : ∀ i, 0 ≤ i → i < 320 → ch_21 i = true := block_join nj_21_8 (fun _ h1 h2 => treeBlockF_at nb_21_9 h1 h2)
theorem nj_21_10 : ∀ i, 0 ≤ i → i < 352 → ch_21 i = true := block_join nj_21_9 (fun _ h1 h2 => treeBlockF_at nb_21_10 h1 h2)
theorem nj_21_11 : ∀ i, 0 ≤ i → i < 384 → ch_21 i = true := block_join nj_21_10 (fun _ h1 h2 => treeBlockF_at nb_21_11 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 384 → ch_21 i = true := nj_21_11
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xf0ff0f0
def s_22 : List Nat := [0x5055050, 0x3033030, 0xf0f0, 0xf00f0]
def g_22 : Nat := 0x5071070
def ep_22 : Nat := 0x20060000000000000000000000000000210200000000005041040
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xff00ff0000000000
def s_23 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_23 : Nat := 0x100170000000000
def ep_23 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7)]
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
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_4 (kn_cons lb_5 (kn_cons lb_7 (kn_nil))))) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff000000000000
def s_24 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_24 : Nat := 0x117000000000000
def ep_24 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_0, s_0, 4, g_0), (m_18, s_18, 4, g_18), (m_17, s_17, 4, g_17)]
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def hc_24_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_24_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_24 : Nat → Nat := fun p => Bool.rec (hc_24_1 (Nat.sub p 32)) (hc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 43 bds_24 (dagTraceF m_24 s_24 6 f_24) (cur_24 0) (nh_24 0) s_24 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 ch_24 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 43 ch_24 = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 43 → ch_24 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 43 → ch_24 i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_0 (kn_cons lb_18 (kn_cons lb_17 (kn_nil))))) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xff00ff00000000
def s_25 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_25 : Nat := 0x17007700000000
def ep_25 : Nat := 0x60000000000000000000000000000600000000000000120022000000000014004400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf0f0f0f000000000
def s_26 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_26 : Nat := 0x10107000000000
def ep_26 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_13, s_13, 4, g_13), (m_10, s_10, 4, g_10), (m_3, s_3, 4, g_3)]
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
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_13 (kn_cons lb_10 (kn_cons lb_3 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcccccccc00000000
def s_27 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_27 : Nat := 0x4044400000000
def ep_27 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x3333333300000000
def s_28 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_28 : Nat := 0x113133300000000
def ep_28 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_17, s_17, 4, g_17), (m_3, s_3, 4, g_3), (m_8, s_8, 4, g_8)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_17 (kn_cons lb_3 (kn_cons lb_8 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xaa00aa00aa00aa
def s_29 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_29 : Nat := 0x200220022002a
def ep_29 : Nat := 0x20000800000020000000080000000000000000000200000000000800020022002200200000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_29_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_29_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_29_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_29 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_29_2 (Nat.sub p 64)) (hc_29_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 64 (dagTraceF m_29 s_29 5 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 64 bds_29 (dagTraceF m_29 s_29 5 f_29) (cur_29 0) (nh_29 0) s_29 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 64 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 64 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 64 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 6 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x5050505050505050
def s_30 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_30 : Nat := 0x10105010101050
def ep_30 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x66666666
def s_31 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_31 : Nat := 0x4260666
def ep_31 : Nat := 0x2400000000000220060000000000404060000000000000000000000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xbd750f 4 15 2 3 6 63 8 255
def nh_31 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_31 : Nat → Nat × Nat := unpackForestF 0x1f7a8f 1 6
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 3 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 3 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 3 ch_31 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 3 → ch_31 i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_nil) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x115155500000000
def ep_32 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_18, s_18, 4, g_18), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9)]
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
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_18 (kn_cons lb_10 (kn_cons lb_9 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x6666000066660000
def s_33 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_33 : Nat := 0x6000004260000
def ep_33 : Nat := 0x420000000000000000000000006000000220000000600000404000000000000000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
def cur_33 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_33 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_33 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 3 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 3 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33 : treeBlockF 0 3 ch_33 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 3 → ch_33 i = true := fun _ h1 h2 => treeBlockF_at nb_33 h1 h2
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_nil) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xcccc0000cccc
def s_34 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_34 : Nat := 0x44400000c4c
def ep_34 : Nat := 0x808000000000000000000000040000000400000040000000c0800000000000000000000044400000040
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
def cur_34 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_34 : Nat → Nat := fun _ => 0
def f_34 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 1 (dagTraceF m_34 s_34 3 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 1 bds_34 (dagTraceF m_34 s_34 3 f_34) (cur_34 0) (nh_34 0) s_34 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34 : treeBlockF 0 1 ch_34 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 1 → ch_34 i = true := fun _ h1 h2 => treeBlockF_at nb_34 h1 h2
theorem lb_34 : LowerBin m_34 s_34 g_34 4 :=
  lowerDagV5 (kn_nil) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5500550055005500
def s_35 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_35 : Nat := 0x100150015001500
def ep_35 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xff000000ff00
def s_36 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_36 : Nat := 0x170000001f00
def ep_36 : Nat := 0x800000000000000000000000000000000000000060000000e0000001200000010000000140000001000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x3300330033003300
def s_37 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_37 : Nat := 0x100130011001300
def ep_37 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xcc00cc00cc00cc00
def s_38 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_38 : Nat := 0x40004000c00
def ep_38 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf000f000f000f00
def s_39 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_39 : Nat := 0x100070005000f00
def ep_39 : Nat := 0x40008000000060000000a000000000000000000000000000000000001000200000000000100040005000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcc00cc00cc00cc
def s_40 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_40 : Nat := 0x400440004004c
def ep_40 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xffff0000
def s_41 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_41 : Nat := 0x15370000
def ep_41 : Nat := 0x220000000000000404000000000000103200000000000015040000
def bds_41 : List (Nat × List Nat × Nat × Nat) := []
def cur_41 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_41 : Nat → Nat := fun _ => 0
def f_41 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_41 : Nat → Bool := dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 1 (dagTraceF m_41 s_41 3 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 1 bds_41 (dagTraceF m_41 s_41 3 f_41) (cur_41 0) (nh_41 0) s_41 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41 : treeBlockF 0 1 ch_41 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 1 → ch_41 i = true := fun _ h1 h2 => treeBlockF_at nb_41 h1 h2
theorem lb_41 : LowerBin m_41 s_41 g_41 4 :=
  lowerDagV5 (kn_nil) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xffff
def s_42 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_42 : Nat := 0x1f7f
def ep_42 : Nat := 0x600000000000000e0800000000000010200000000000001040
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xff00ff00
def s_43 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_43 : Nat := 0x15001f00
def ep_43 : Nat := 0xa0000000000000000000000000004000e0000000000100010000000000015001000
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

def m_44 : Nat := 0xff00ff
def s_44 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_44 : Nat := 0x37007f
def ep_44 : Nat := 0x480000000000000000000000000004000800000000003200200000000000040040
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xcccccccc
def s_45 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_45 : Nat := 0x4040c4c
def ep_45 : Nat := 0x84800000000000000400000000004040c0800000000000000000000000004040040
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff000000
def s_46 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_46 : Nat := 0x100000015000000
def ep_46 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff0000
def s_47 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_47 : Nat := 0x17000000370000
def ep_47 : Nat := 0x20000000000000000000000000000000000000000600000004000000120000003200000014000000040000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf000f000f000f0
def s_48 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_48 : Nat := 0x10007000300070
def ep_48 : Nat := 0x20000000000060000000400000000000000000000000000000000000100020003000200010004000000040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f00000f0f00000
def s_49 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_49 : Nat := 0x10000010300000
def ep_49 : Nat := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf0f00000f0f0000
def s_50 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_50 : Nat := 0x107000005070000
def ep_50 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5a5a5a5a
def s_51 : List Nat := [0xa0a0a0a, 0x12121212, 0x5a005a, 0x5a5a]
def g_51 : Nat := 0x10121a5a
def ep_51 : Nat := 0xa480000000000020040000000000000000000000000101210000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14b59280f 4 15 2 3 9 511 11 2047
def nh_51 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0x32dc940f 1 9
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 3 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 3 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 3 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 3 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x5a005a005a005a00
def s_52 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_52 : Nat := 0x120010001a00
def ep_52 : Nat := 0x100008000000120000000a000000000000000000000000000000000000001200100010000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_52 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 3 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 3 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 3 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 3 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xc0c0c0c0c0c0c0c
def s_53 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_53 : Nat := 0x4040404040c0c
def ep_53 : Nat := 0x400080800000400000008080004000000000000000000000000000000000000000000000004040404040000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x50a050a050a050a
def s_54 : List Nat := [0xa000a000a000a, 0x102010201020102, 0x50a0000050a, 0x50a050a]
def g_54 : Nat := 0x10205020502050a
def ep_54 : Nat := 0x400000800000400000000080000000000000000000000000000000001020002000200000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_54 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xaaaaaaaaaaaaaaaa
def s_55 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_55 : Nat := 0x2022200220a2a
def ep_55 : Nat := 0x2008080000022000000a0800020020002200200002020000000a0800020222002200200000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 6, g_29)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 6 f_55) (cur_55 0) (nh_55 0) s_55 6 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 6 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 7 :=
  lowerDagV5 (kn_cons lb_29 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xff00ff00ff00ff00
def s_56 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_56 : Nat := 0x100170015001f00
def ep_56 : Nat := 0x140008000000160000000a0000000000000000000100060004000e0001001200100010000100140015001000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 7, g_23), (m_39, s_39, 5, g_39), (m_36, s_36, 5, g_36), (m_38, s_38, 5, g_38), (m_35, s_35, 5, g_35), (m_46, s_46, 5, g_46), (m_37, s_37, 5, g_37), (m_12, s_12, 4, g_12), (m_14, s_14, 4, g_14), (m_43, s_43, 4, g_43), (m_52, s_52, 5, g_52), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4)]
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c26a95c75c05a15a05815805425405404e34e04e04a24434404214204014004004003e1364360341340321320038001 0x200983e110a91f94a3b2646e488cc20971183b22066420ac78119c34f3769666d1cbda183a3e2b27c3a0506daf0c93e154a22e8e456b009350144b824d48452f0b452134a620904380a06254080281717c29a984a5e072a40a0500da95134fa06973cd1e75a1ce24f9a4972891e4121c723f8d477008ddd519b614f602967451c70a18d13f182761e4dc34998312f042560449c04918001f 12 4095 5 31 11 2047 19 524287
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x902318c1f4569504c9123c8f03c0a5280a02446318060144320c0300c03004810004000000000000 0x7cd02012f7e4ade9277848efb5cbcd42ea5cb8946aa50a48fe823b928de0a3376171c94454051714c52051693c50051b5606a571613c681713014620b19134600d120145b141734a58d1944504e1012828 10 1023 4 15 11 2047 18 262143
def cc_56_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x944a2190884421f4f87533190c859ac144a04924104803c9548440200e47038150140000 0x29b4ea2d2a634690d0a6c50b2132325cae092da3fb48eec237ac8cea36ca6982006ca2d81f86c9a941f05c9b142584c965427c609d14262607a1b2504c8c97220248c94222508654243608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_56_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b0284a0280a0280731c0701485001400 0x3795d8a557d818f4053eb4ef852fc943dc13f184b8411d8043f007fb813ff17bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5944d1583395ccc1732134c60d3534fd2d2f2b47c4d0f093e 10 1023 4 15 11 2047 18 262143
def cc_56_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0700bc6f0b86e0b82e0b82e0a5690a4290916407d5b46c1745c1705c152541323d0f03c0b406801 0x4fa519b8bd368fa65ae4c350972b92c542542e49c5f9248e2651c289fc89278f6bce857da8ada9157382a6e657da4ada8157372a6e4575a0aca7155362a29a90220261693c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_56_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x28308040 0x24e53a3925fe310b4be8434 6 63 3 7 10 1023 18 262143
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_56_5 (Nat.sub p 160)) (cc_56_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_56_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_56_2 (Nat.sub p 64)) (cc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_56_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_56_0 : Nat → Nat := unpackHintV5 0xe06036b626b14a357f458b1c6f5541d25ea5d2f4009262a48b042458011c8328d00a4680021e0b0f5cca6de682ca52965000ac83052e1b26f1413382092c383ce6419b260971b44045a150590104c00004000000 0xad31c74d31c74e1c78722e2e2e2cb806db6db1c04c71d34c71d3a1c787ab8b8b8b8b2ea2c32cb2cf2c32cb4b4b2c71c7000000000000b02830c30c30d5d5eaaaa4c0030c30ea87a83974d35c30c30e65e6aaa0eaeaaaaa970000000000003d33cf4c71d3692cb0c32cb4343003cf0cf0d34d34d30cf3c38b8b83aba0c38b8b2d32c72c72cba8b2d2d2cb0c30c000000000000f3e832cb0d357eaaa8002bad87ada7c33eb2e3ebab5cf3c71df4b2da83a99000a87a8f0cf0e8b5d34e6a60cf3c3aaaaaa0eaea800000000000034c30c30d34d34c30c30e2e2e0e25cb8b2d34d34e0175d75cb0034c30c30d34d34c30c30e2e2e830e0eae5cb8b2c34c30c31c30ea0d70d0d0c30cb0c000000000000c0acfa0cf2e4ebadf1cb8b1eacba8f0cf0d37d2d2e99a8021cba1cba830d62c0b134d75355d5ea87a83a8fa8baaaaa975ab5a54000000000000134d34d55562e2e2e2d45534d34d75d75c10b0134d34d554d562e2e2e2d6ad554d51d50d53d554b400000000000404d7550cf3c355a56aea800174d35d51d554f543555556aaa96555ab0000000000004d34d3534d4d35757932e2cb972e2cba55ab2d32c72c72cb2c32cb2cf2c3a95000000000000000000000 21 2097151 9 511
def hc_56_1 : Nat → Nat := unpackHintV5 0xda0034820cd84aaa8c76b41da006b8b186285a87158125184910363f050fc003c030ce2230830c2002d8305a5c13038460611800400609868260006830140603818000e000000000 0x9db1eb8badb9c701b9e76c71c71db9e76c71c71e028aaaaa87a3eaa831c71c7a6a6871c71eaaa87abaaaa200000000000002bacb833d2d2bad3cb5cb2b0cf6b1ad6cadb8c7aeb8b52c33d0aeb1badbaeb0cb0c2b0eb2d34e5833cf0cb2cb2d1d1c02b2eaeb1eb8b6eb6eb6eb2c 18 262143 8 255
def hc_56_2 : Nat → Nat := unpackHintV5 0xc5202b460911c23e068e01a38008885a2200830599874638298806598895e084c8b1161c4005900003a858ea00328809832200606e121b800620c188005c06108680c36018180006 0xc30c31c71c70c30c3a2aaaa00000000551c71c755a255aa000000001c71c7471d0cf3c3a87aa9900000aeb1eb8b2b1cb81c71c71c71c7a887aaaa000000000aaeb3c365aeb2b8f0dad7a3eb1abab5b0f0dac1eb8b236cf0dad91cf0daeb8b0aeb8b89adb03aeb3c35bacf0dae831eb2e0aeb 18 262143 8 255
def hc_56_3 : Nat → Nat := unpackHintV5 0xc245cc0410be80ebe800be800bdc06bd006bc406aa09286d1a82c207f41c7e4087d806788287700c7640671c24584cc58400558164f8304ec064d80a4cc06480264800045c123f43431c6c1010e00080 0x30c30c343575d3d3e2e2c0030d6b0caeb6c30c30c3575750d46db403c00c30c35d576db0c30c30d5d5d430d0dac30c30c70c35433c30c30c35d570e0cb0e0c3000000000030002536bacbab8f4eadaeb1d4dabae2c0ebaeb1e0d3ab22e4c71d3a838fa4c71d39939a87abaaaaaaaa4c000000000002bad1daeb0cf3c75c7adadac7aeb8b51cac33ebacb833c31c3071da433cf0c71c71cb2d2d2c00071c71c71c71e1eae871e2e2e2e2ea1c31c71cf1c31c747471c72c700000000000001c71c71c71c73cf3cfa2aaaa00000000 20 1048575 9 511
def hc_56_4 : Nat → Nat := unpackHintV5 0x7a1519b9d7467837992c5a5b44b95d080532211408604be2211b0a43f73a8f70363c9098ee022327488bf45429c3088391c1ce2006606c1950186480619200061c161870005f0161441c0450600d42002388c0263400004c 0xc30c71cf1c70c30c70eb1d1c71d1c71c71c33cf0c7871c7872c71c71c33cf0d34d34c00000000000030c30c31c3ac33c30c30d71d71d75c30d70c30c3435c3430d31c74c30d30c30c3832c3830d74d74c0000000000001571c75d50d3d51dad555554c71d354b655d35d355530000000000001d745ad433cf0c14e2e2c0071c71c75d1dad471d5d5d51c31c71cf1c31c71c71c74d34d34d531e1cb1e1c70000000000001c71c751551c71c73cf3cf55000000000c30c3545551c71c70c30c35500000000aaaa1c71c7555155000000001c71c75447551c71c72cb2cb55000000001c05d75d71c71c74051554d34d31c71c74d34d35551d4f5550c71c71d555476b5559554b1c71c74d34d355100000000000003aeb7d434f0cf0d5eb0cf5eb472d3931d71d75d471d1dad5d5d55c37cf3d70c71c74c71d35d34d4d4d37e4cb932c000000000001430c30c30d55562e2c00030c30d5475435550dad5550c30c354b655500000000000003cf0cf0d75757436b50c33d73c73c73cf5430c30cf3c35d573e3cb3e3cb0000000000000c71c351550cf3c31c71c755000000003c33c350cf3c3555558b8b00000aeb3c36b2b0cf40cf3c3545550cf3c355000000000aa3c33c3aa555551000000003c33c355512cb2cb0cb2c355000000008db8db3c33c33c05540516e38db0cf3c355547554f0cf0d4f5555550dad65552c33cf0d54004000000000000c350c73c33c32c300c 22 4194303 9 511
def hc_56_5 : Nat → Nat := unpackHintV5 0x83868599503d8e0115620008a 0xc35df3cf0d43471d3cf8b8b000c30c31c3ac71c30c71c75c71cf4f3d3cf0cf3cf0d31c74cf8f2cf8f2c33cf3c34d35d300000000000000c7030c301c0c01c71c70c30c35d75d71c71c70c30c34d34d34d34d30c70eb0c30c30c70c30c31c71c71d70c30c30d0d70d0c31c71c70c30c30e0cb0e0c34d34d300000000300000070c70eb1c73cf430d4f3d1c74d38b8b000 20 1048575 9 511
def nh_56 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_56_5 (Nat.sub p 160)) (hc_56_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_56_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_56_2 (Nat.sub p 64)) (hc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_56_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_56 : Nat → Nat × Nat := unpackForestF 0xa349202d3e841a00b4b9f4a202d1c05a180a4f9b47c0292e55ae4ab50952b92a542542e00a47918bf2291e449380a438f6bc028fc051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37768bcec979dda73b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6b288c2d3d85a5b3560662b8cc17185a3b193463068c2d0d849f0094b3b6b876d40ed2e1da515647eac8ed64262b23757048ac8cced2829b6c534c0768fd45b01da3b4a8c0951413628252604b2a094130ed1ba1360424d88c941092e21a50432a084090ed199e12f3c2567cd00f0939e1233b0b80251ce4a20eb4f1d69669580d0ae1a05c1d68e604d0c416180341d68658d28b628163461d27c3c8fc791d93c50270803c8dc94140f2331e0763c0cc78158f84c1f0883c08c740a009431b6bc024fc649f0093b174722114852b00a25c104a622d48452f082410126e1c050049986254078be0ed4c1d2f04014072a4024bc140a0092b036a40249c04918001f 8 11
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 4 15 bds_56 164 (dagTraceF m_56 s_56 8 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 4 15 164 bds_56 (dagTraceF m_56 s_56 8 f_56) (cur_56 0) (nh_56 0) s_56 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 96 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_3 : treeBlockF 96 128 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_4 : treeBlockF 128 160 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_5 : treeBlockF 160 164 ch_56 = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → ch_56 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 96 → ch_56 i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nj_56_3 : ∀ i, 0 ≤ i → i < 128 → ch_56 i = true := block_join nj_56_2 (fun _ h1 h2 => treeBlockF_at nb_56_3 h1 h2)
theorem nj_56_4 : ∀ i, 0 ≤ i → i < 160 → ch_56 i = true := block_join nj_56_3 (fun _ h1 h2 => treeBlockF_at nb_56_4 h1 h2)
theorem nj_56_5 : ∀ i, 0 ≤ i → i < 164 → ch_56 i = true := block_join nj_56_4 (fun _ h1 h2 => treeBlockF_at nb_56_5 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 164 → ch_56 i = true := nj_56_5
theorem lb_56 : LowerBin m_56 s_56 g_56 9 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_39 (kn_cons lb_36 (kn_cons lb_38 (kn_cons lb_35 (kn_cons lb_46 (kn_cons lb_37 (kn_cons lb_12 (kn_cons lb_14 (kn_cons lb_43 (kn_cons lb_52 (kn_cons lb_2 (kn_cons lb_4 (kn_nil)))))))))))))) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xf0f0f0f0f0f0f0f0
def s_57 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_57 : Nat := 0x10107010301070
def ep_57 : Nat := 0x1020000000001060000000400010006000200060000000000000000000101020103010200010104010001040
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
def g_58 : Nat := 0x4044404040c4c
def ep_58 : Nat := 0x4000808000004400000084800040040000000400004040004040c0800000000000000000004044404040040
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_53, s_53, 5, g_53), (m_27, s_27, 5, g_27), (m_38, s_38, 5, g_38), (m_40, s_40, 5, g_40), (m_45, s_45, 5, g_45), (m_34, s_34, 4, g_34), (m_14, s_14, 4, g_14), (m_11, s_11, 4, g_11)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d2529425088e118421069da0681a05cd615815154150505405014035cd0340c1288a006401 0xb9517941e9394131912f6923cb496132283e5a50bc518a4e5242b14e4142184ea8169b5e925e89525a5071445c507c526b5e625e5252495e415239352034284f1843e343da4ed242c14fa143813f3133103e0832001f 10 1023 4 15 11 2047 16 65535
def nh_58 : Nat → Nat := unpackHintV5 0x12700221acbdd666befcd54298327af80e5e20eba81d4d282930751c0aa241515af21a11434008402905829fc0f3e01879828ea889cb0a2ccca58414b0801570a1a7081b598003680000 0x40d8800399c6718bde800000c013a70039ce7500002e0000004c06351804d66318c6004c00006000ce3d5e0719c61b1e0f00037b459b00781b1ea339c600000b05ef60f5f338ce37aed7a8c6ab164f7b367def7bdec38c6717b1b37abb18c178e6339ce35558b37b5a0ac1601ee039aa9c67182aad6b58ce718000002a802a8ce7180080000081c06751828ce71802c4187162c 19 524287 8 255
def f_58 : Nat → Nat × Nat := unpackForestF 0xe9390b430a4e0a42cb49094fac51a94ea81609438b5e8a5e8952093f3c5271443b5e3a5e5c503a52395e395239350933184f20341843083e0832001f 5 11
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 30 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 30 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 30 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 30 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_53 (kn_cons lb_27 (kn_cons lb_38 (kn_cons lb_40 (kn_cons lb_45 (kn_cons lb_34 (kn_cons lb_14 (kn_cons lb_11 (kn_nil)))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xff00ff00ff00ff
def s_59 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_59 : Nat := 0x1700770037007f
def ep_59 : Nat := 0x20000800000060000000480000000000000000000600000004000800120022003200200014004400040040
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 6, g_29), (m_47, s_47, 5, g_47), (m_25, s_25, 5, g_25), (m_48, s_48, 5, g_48), (m_44, s_44, 5, g_44), (m_40, s_40, 5, g_40), (m_20, s_20, 5, g_20), (m_6, s_6, 4, g_6), (m_11, s_11, 4, g_11)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x214d3495a4d249934a391894678dd537149c01f 6 63 2 3 10 1023 14 16383
def nh_59 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x63058d6318f6bd185ce78f3a19c00146f182d5abb41e73c77d2776c3d8e005bd60350468d540f1ea9000058c600b51a8001e3c38f31d 16 65535 7 127
def f_59 : Nat → Nat × Nat := unpackForestF 0x214d18dda4d14dcb4a2918946149c01f 4 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 9 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 9 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 9 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 9 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_29 (kn_cons lb_47 (kn_cons lb_25 (kn_cons lb_48 (kn_cons lb_44 (kn_cons lb_40 (kn_cons lb_20 (kn_cons lb_6 (kn_cons lb_11 (kn_nil)))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xffffffff
def s_60 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_60 : Nat := 0x15371f7f
def ep_60 : Nat := 0xa4800000000002200600000000004040e0800000000103210200000000015041040
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_44, s_44, 5, g_44), (m_11, s_11, 4, g_11), (m_41, s_41, 4, g_41), (m_43, s_43, 4, g_43), (m_31, s_31, 5, g_31), (m_51, s_51, 5, g_51)]
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x902228821178de0781e0781d1741c15d5705856054550541324c12148111441103c8f03c0d207001 0x65a6bcd15446ce35d4d1b3614162a0a050662f3116978a4ab564d2b224d8f26c695e30ab14118808c305e142b0617820ad134f7da3ba93da48e923740a59c50cb256484b1c21880ec1026001f 10 1023 4 15 11 2047 17 131071
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x18941a3 0x664d8e455a35865d56358150 5 31 2 3 10 1023 16 65535
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_60_1 (Nat.sub p 32)) (cc_60_0 p) (Nat.blt p 32)
def hc_60_0 : Nat → Nat := unpackHintV5 0xd503e2ef71701850db064d8202c101529ca802d28328f0b418c915f48a01f998f9076d1f34c39a600b43e5a0023931150e6bbe3247192008b7c3e8e1f400711400700000 0x270a09bc789d380003c0025cf1e04c4e9c007813271d1932739d39ae022026cd420000b34f2756a8389d383060d3acd96a8389c1839830eb04d0e7aa1000009831800c21c00751834e0c26010e003a8c19d9c3026408318004b14c9a75860084c63aa0001a0815984008004 17 131071 7 127
def hc_60_1 : Nat → Nat := unpackHintV5 0x4987567aac012468049 0x1d54d72e0566a060d74d4b9754c594b2b94183 15 32767 7 127
def nh_60 : Nat → Nat := fun p => Bool.rec (hc_60_1 (Nat.sub p 32)) (hc_60_0 p) (Nat.blt p 32)
def f_60 : Nat → Nat × Nat := unpackForestF 0x8d2282d3e04bb015005a3bcd14149edb5d6c280291d38bc9c5a4e292c54136aca0504d2b028dd126c094b3c9b0250cc2bc61560495941181096404604218a17850ac083b082f041581026001f 6 11
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 3 7 bds_60 36 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 3 7 36 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 36 ch_60 = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 36 → ch_60 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 36 → ch_60 i = true := nj_60_1
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_15 (kn_cons lb_44 (kn_cons lb_11 (kn_cons lb_41 (kn_cons lb_43 (kn_cons lb_31 (kn_cons lb_51 (kn_nil)))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xffff0000ffff0000
def s_61 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_61 : Nat := 0x117000015370000
def ep_61 : Nat := 0x1420000000000000000000000016000000220000010600000404000001120000103200000114000015040000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_24, s_24, 7, g_24), (m_12, s_12, 4, g_12), (m_50, s_50, 5, g_50), (m_47, s_47, 5, g_47), (m_41, s_41, 4, g_41), (m_33, s_33, 5, g_33), (m_17, s_17, 4, g_17), (m_0, s_0, 4, g_0)]
def cc_61_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81aa6e3dc0b81702d0da0b03412804e19c1306604c094328240c80847082103e27c0f81d1343680c841c001 0xa91f94a3b2646e488cc5c9f1183b200663e0ac78119cb4f3769666d1cbda18b24e2b29c3a05065aa0b8141b8a634d78612f8b15214028251483d2f0694e096c00cd402da404c510849c0d148152f05453076a408d08080a51b4fa169736d1e61a1caa4f934972291e4121c7a3f8d477008ddd519b614f602967451c70a18a93f13276224dc40998712f0c2560649c04918001f 11 2047 5 31 11 2047 19 524287
def cc_61_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x98251942145e9525413244910440c5300c02c483200801c45214050140500c830084200802000800 0x7cd02012f7e4ade9277848efb5cbcd46bb50ac972aa50a68fe823b928de0a3376171715c54051c13452051695c50051b5606a571614c681713014620b19134600d120145b141724d5891544504e1012828440f10834 10 1023 4 15 11 2047 18 262143
def cc_61_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8642211087d3e1d4cc6432190ba5c2e146a04924104803c9548440200e47038150140000 0x2a24da49266245909066c50b6132325cb2092ea3fb88eed237b08cea460801b29460a29b1f86c9b141f05c9b142584c969427c609d14263607a1b2504c8c97220248cd4223508654244608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_61_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b02c0a1280a0280731c0701485001400 0x3795d8a557d818f4053ea4ef852fc943dc13f184b8411d8043f007fb813fed7bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5134d1583395ccc1732134c60d35b4fd2d2f2b47c4d0f094e 10 1023 4 15 11 2047 18 262143
def cc_61_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0340d02f5bc2f0a96a0a8264982519424190204801b56c1745c1705c152541323d0f03c0b406801 0xa04b93e94278ae4e9509c0b92e97e691b8d94f9926e1449e5da9cb3497f464304fe501249351742bed656d4cab9c9538e4bce657da4ada8157372a6e4575a0aca7155362a29b14220261695c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_61_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_61 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_61_5 (Nat.sub p 160)) (cc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_61_2 (Nat.sub p 64)) (cc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_61_0 : Nat → Nat := unpackHintV5 0x8fa058a852810987ee227b23c7b200789297810875e236a8b6654545b3a1572414da9842dad3f93435d9c3293428d9c28d002622b25111251002143d20311203001c63d11da90c558020a50002000000 0x2eaaaaaa6aaaa955ad6b95aaaaaaab755555544545438a95555555555595dbeaab71e3cf22183288a954671ec1c7d95555407816483d51cf510007181c611ea0b614004705541555514555000000aa00000aa0000950020000aa0b6000040400000010aa0000aa00a0800000005016ea9554080000000000002a80e0016c01544004000154a2a2002aaa802d85055554782a1800aa8228aaaaaaa00000155410aa0000000100000015400016c0006aa00000220ab54500004000aa4544401550416e82aaaa00a8700aa8228aaaaabb818de0e3ef7b0f0e860f28aa225551eed814f060070000554818ea8631800c6400555470800a0b6aa82aaaa28aa004000154000015400012a0040001540000016c80800000021540001540141055555555 20 1048575 8 255
def hc_61_1 : Nat → Nat := unpackHintV5 0x9c40259189283dea60522892f194bc010f203e854ea1036c3cb52629044a4002682886141fc1c7f001e01c463210414350c0d40030050744c1d0004c280a09028000a00014140005 0x175db3db5de5577baea977baeaa569aaaaaaa2a2aaa8715455555556eaaa995555555555555dec184ef71c190ef6034d8b76b9dbd9e0806bbdabdaf7b214deea82a1832889577b8fbb6797b5ee77b 18 262143 8 255
def hc_61_2 : Nat → Nat := unpackHintV5 0x98654b816570b2b8091c848e023720f3d062ee27741340e8a2043c2a0c24eb366919308818400b2205900268c0e8985f2a279013c00901c480021850c0981498050a0005 0x551450c1955510aaaabbddb3cee8ed55554d55552aaaaaaaad5550c631d355552aaaaaaa8000005300002a80002a9b0818cdeddd6c19b23696cd8b419b6d9e66b066c8819bd9e5dee8e96d69bd8317b066c8b71d77b 17 131071 7 127
def hc_61_3 : Nat → Nat := unpackHintV5 0xf30cbc408eec27bb00eec03b605ec417ac05d694ac298ab456911ca281e8505994825e0796416401969271881c6200178105cc156a09594154a1b528013e0c47880e43a142500050 0xf1e5500d8ef6b000000016b000000005ac0000000360100000000010705500000050415481ef7b391b8e6f7107decf26f7b8e46daaaa2a23d5438a8ab755547aaaa555555555555dec6103dec8d9b376f6782760f7b8e0c868a2860caa22555aaaaab755555555115150e2a5555555555555000000a6000055000055 18 262143 8 255
def hc_61_4 : Nat → Nat := unpackHintV5 0x9f6509a254952508ada589914885147dea77bc227803c6cab6676545d5a1594414fc9844fad3b39c3793a2e5942955024b4a2460524105241002311023100221101d1501755c125500c560023a200023 0x2a80000000001555400000080002a8000154000156540000000002aaa80000200008d8000000000400155000002000aaa0000abb0019b2a3c1446c0a8200078c06154453cf47a21550555545154dbc00d831e000c0000f1e550080180c646e82a060550c7433d0450c955555504551540080001640002a80002a80008d8000100000055000001102a8000002820ab000501b0002aa1550028222a1d011b00aaaaaa8228555555411455000002360000c000002a80020008382a8000200882a80010030018001b0000001801002a800800802a800000001e3caa2000006c000200000000020e0aa000080220aa00000001540000aa00aa000000000078f2aaa8ef60cdbb01a0000000000000aa008aa739ce0000000000aaaa0000000001540000aa0000ab35cd60000000000b9cd60000040000000000001b0380040000aa08002800022a8010c0801 20 1048575 8 255
def hc_61_5 : Nat → Nat := unpackHintV5 0x1759c500d4a49c151400054 0x46c00000000000aa020e000400aa02200000aa21b010002aa5523614054100050430aa82aaaa2855415555145500000000aa00005500550000000aa000055000055 18 262143 8 255
def nh_61 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_61_5 (Nat.sub p 160)) (hc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_61_2 (Nat.sub p 64)) (hc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_61 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c4a13857270a84e05c0168f328de649b80b43966a72cd240527ca0240149724d44052380a430147f1c978051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37766bcec979dd273b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6169ed44d185a5b3560662b8cc17185a3b193463068c2d0d84a70094b3b6b876d45611fac23b5b098b08dd64122c2333b6a076970ed282a4603b47ea318145361da3b4a8c0951413628253604b4a094130ed1ba1460424d88cd41092e21b50432a084090ed199e12f3c2567cd00f0939e1233b0b80251c75a79c1341d69669580d0ae1a05c1d68e604d0c416180341d68658934b628162451d29c3c8fc791d93c50270803c8dc94140f2331e076420f0841a0f0331e0563c08c740a00943168a62cd7865aa0b25f170282c548049f8a0140127625148049b809330f4bc024bc34a70092b0b6900914c22288424e046a40b148152f023420124e0405004918001f 8 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 164 (dagTraceF m_61 s_61 8 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 164 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) (nh_61 0) s_61 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 32 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_1 : treeBlockF 32 64 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_2 : treeBlockF 64 96 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_3 : treeBlockF 96 128 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_4 : treeBlockF 128 160 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_5 : treeBlockF 160 164 ch_61 = true := by decide +kernel
theorem nj_61_1 : ∀ i, 0 ≤ i → i < 64 → ch_61 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_61_1 h1 h2)
theorem nj_61_2 : ∀ i, 0 ≤ i → i < 96 → ch_61 i = true := block_join nj_61_1 (fun _ h1 h2 => treeBlockF_at nb_61_2 h1 h2)
theorem nj_61_3 : ∀ i, 0 ≤ i → i < 128 → ch_61 i = true := block_join nj_61_2 (fun _ h1 h2 => treeBlockF_at nb_61_3 h1 h2)
theorem nj_61_4 : ∀ i, 0 ≤ i → i < 160 → ch_61 i = true := block_join nj_61_3 (fun _ h1 h2 => treeBlockF_at nb_61_4 h1 h2)
theorem nj_61_5 : ∀ i, 0 ≤ i → i < 164 → ch_61 i = true := block_join nj_61_4 (fun _ h1 h2 => treeBlockF_at nb_61_5 h1 h2)
theorem nc_61 : ∀ i, 0 ≤ i → i < 164 → ch_61 i = true := nj_61_5
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_24 (kn_cons lb_12 (kn_cons lb_50 (kn_cons lb_47 (kn_cons lb_41 (kn_cons lb_33 (kn_cons lb_17 (kn_cons lb_0 (kn_nil)))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xffff0000ffff
def s_62 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_62 : Nat := 0x177700001f7f
def ep_62 : Nat := 0x808000000000000000000000060000000600000060000000e0800001222000010200000144400001040
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 6 f_62) (cur_62 0) (nh_62 0) s_62 6 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 6 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 7 :=
  lowerDagV5 (kn_cons lb_21 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def g_63 : Nat := 0x117177715371f7f
def ep_63 : Nat := 0x142008080000166000000a4800160060002200600106060004040e0801121222103210200114144415041040
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_61, s_61, 9, g_61), (m_28, s_28, 7, g_28), (m_56, s_56, 9, g_56), (m_60, s_60, 8, g_60), (m_57, s_57, 8, g_57), (m_32, s_32, 7, g_32), (m_59, s_59, 8, g_59), (m_62, s_62, 7, g_62), (m_58, s_58, 8, g_58), (m_55, s_55, 7, g_55), (m_1, s_1, 4, g_1), (m_24, s_24, 7, g_24), (m_26, s_26, 7, g_26), (m_29, s_29, 6, g_29), (m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14), (m_11, s_11, 4, g_11), (m_49, s_49, 5, g_49), (m_16, s_16, 4, g_16), (m_8, s_8, 4, g_8), (m_12, s_12, 4, g_12), (m_23, s_23, 7, g_23), (m_48, s_48, 5, g_48), (m_7, s_7, 4, g_7), (m_30, s_30, 5, g_30), (m_20, s_20, 5, g_20), (m_4, s_4, 4, g_4), (m_47, s_47, 5, g_47), (m_54, s_54, 5, g_54)]
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x82041020030008003f05f80fc07e03d09e80f016c33601b00d806c03601986cc06603301980c816403201882c40600aa180d2001 0xeb540d57e0bd7e0b3540a3720e5630da6f0ca5f0c16f0a95f0992707c5f0715f069470457e02d7e01d720556304c6f03c5f0336f0235f01347e845fe645be3c57e1c53deb5fddb5bdcb57db353d834fd6b4bd1b47cf343c525fbaa57b424fae247aaa3fa0a379795f861577994f699475e93f4a1373c1273a05f3985b2e0572d8532a04f2984b1c0471b8430f83f0f03b09037088330802b060270581b008170003f 13 8191 6 63 11 2047 20 1048575
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa86a0a466398251725c0701c064d81601625455048d20445104411038ce0380e0344a3280a020808 0x1ea6f7b181fe727d181e27f74d828d629edbe6b5d929be3a378a5be015d764ddc9276d151ab544e4d5514f64d9131354a4d5857e5ed5121355ad915c5454df94b544b5f93d634c9bd225f44dc90b486958d9b6e629bd725f585bd415f464d50127 10 1023 4 15 11 2047 18 262143
def cc_63_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x88211661906419064190641904d9304c112440e3380c2300c0300751c05214041100401004001000 0xbcdc3936dded3f624fd48df296dc653ef937ba49ed36fb29bec237ae5beb137aa49e93457e4de85689cd72215d9cdba526f995a25b6594d76115d784de4460825b6356888dbe1b45849be0a37 10 1023 4 15 11 2047 18 262143
def cc_63_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0a8aa0956505bd60581604cd3048520480f3384e0290a0208802008020044100310c03008402 0x7e488fa111fe2fbe4537b48c4413c5023c8d6b8eacf191ae2a33c445f868b70715e0229bd36279694ba19d542f9c8572009e2611ddda7bb14f7526ee0d39c63e3837c682fac24ddba3e36b45672fac04ddae383317d696aad0d3d9d27b3237648f8c36318a383025f 10 1023 4 15 11 2047 19 524287
def cc_63_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xb83702e0563ac1506a0540a43480fd1e03c0688d01a02c4580a0940242480710e01823006008210018401800 0x13f1c276bf4e458600ef351825eb95dd6fb9ad76d59eceb1d8c6eb08d75f18eb6315645ba98a750dbe99b3d2b5fa26af409be7933cda5f994af3093e591bba86f5f0ceac17cec2bca84f0d04f2715649ac4847d8f6e11ad222db83fb72896b10ed2215b04206c7d4c4f8dca09a440844 11 2047 5 31 11 2047 19 524287
def cc_63_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd1466210180389c0e06130180a2502452090481c8e07038148a050209008040110800400 0xc0ce57edb346b7e7d6bccacf9358f21b76326fc44cf8297ef92bde468ae8e175162e2385ba7cb58b168d52c9aad7569a78cb56dfaa81a53c60a4ce5461b286341e057 9 511 4 15 11 2047 19 524287
def cc_63_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xe070345a0d05cee161b054682aa50245208140200c460301088040188c04220100080000 0xde69fbad0f72b86db7dda6bbb0db359b5eac60f1ac5dedbfb1b5f4367e66c7c6d777d37eca67d747fa88df49b268354ce6f99a9f32e2a65354c76c98adf30ebf61354 9 511 4 15 11 2047 19 524287
def cc_63_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xa028098a6098242902318c2308492f48102400e2380e0308c0300a2244901c8701c0340c0300c003 0x7f4647eb457dc7c7d3457c3547b4727ac588546e8436f8336b82367813637fb457e26f7ca677ba3f7a2373b06f318671403f0a8370702777369793457856872b5c7767076b6c75a4f7524774d707246c73b6c72b6e723627026f6d2677156870b657035d 10 1023 4 15 11 2047 20 1048575
def cc_63_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x95250942328c23084a10805f1785d1705c06c5a159151324c0288a024490204801c4701846018006 0x91c7c9137c90b6c8f8348ec7c8e3458d5708cb5d8bb7c8a36888b548a46c8835088b5c884648ab5f89b5b8935787b53874709736d95b4f94b4b923478f3438da4f8c2478b23f86a3785b550b83784c6483b5482c7c81b547ea6f7d2678085e800521583d0b035 10 1023 4 15 11 2047 20 1048575
def cc_63_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x8460180200801f17c1e1781e0709c0701a2680bf24890240721c0611806010840088110401004001 0x9fb7d593649d4649c3649b5689a85c99b6499034a045b9f45758b5d9eb5b9e3579db559cb4f9bb4b9a34798b43980572b84f228471603f0c0379634e91b4296c7c9637c9537c9424f93a47935709285c900349036c 10 1023 4 15 11 2047 20 1048575
def cc_63_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4341b22c0ac6b0a86a0a82378c2307d1f07c1d2741a368146501314c12148111441103c80f00000 0xaf355b3562b1b6bb0367afb5d8c167ae95d5f13f4c937adb54acb7cad56bac567abb6e8b1677b95f6b957ab135a6470aa458a9955a214da893fa8137a7c70a717da194da6569a5465a445f7b15f4b94701817a5460a4472a306ca256ba1d67a956ba6d67a5c62a4b67a3b5fa2b57869677a15f6a157a114d4b137350672c05f2385701017 10 1023 4 15 11 2047 20 1048575
def cc_63_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xcd330cc330c0f00c0300b4e3a8c1d6741d06c9b06c18358960581422308014c50140320c03004801 0xc0d70bb97dc015dbf85cbeb7cbe135bd834bcb65bc34fbbb47c4b6dc334fc1b4bbf347bd343bb16d7c94f6c9476213f4f137ba3556193f4e9371803f0d03702817b9354b8935b7c7cb717db59458e16736867b5b67b534db9c6eb836bb6b67b63458d967b49456093f4d937360671703f0c83702017b2b69b3b456013fb2e70b236cb1570b097d8c967 10 1023 4 15 11 2047 20 1048575
def cc_63_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9e6529425088e208820280200801c4701c07019364190641631fc61180600cc300c0120400100000 0xd136ec7a6fbd2679896f8f167d093540127d0038cf8347094725847ce464c6965cd945ccb64cc135cb568c6165ca95dca05cc9364c8935c8034c735dc6b4fc6347ceb55cd34fcbb4bc9b47c7b43c59557e14f6f9476313f501372c84f248471883f0d837030176d947c447cbc17dc3945c2b7cc2135c114f 10 1023 4 15 11 2047 20 1048575
def cc_63_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xd016bac8d36a251ae3046084900a004007e2f4977ae058495d19221440808f11e03c0564a808d0e214828005 0xe145be0c57da34fd5b475895de0157df9558414f7794754137df0572d04f2784704817b8a5fb825fb1a578315f76157de13546127b724fb0a47dc36dd934fd4b47b6a4fb0247a4a37dd16d8214f741475313745127dc36e8115f73157db935d9b6504017d9c6ccda6fc3a67dac6eda36fd9367cd26fc3267a3a379c96f95967d894552937441273b86f378670782703817cc26fc2267d7b6ecba6fc1a679b96f94967d713543127d536552137d385cd5560d305ccaa6fc0267d3a5fd3257ca15fbf957a31279a85f928575182742017d6562d5b6fd4b67c9a6fbf267a2a379a16f92167d415d5113741927d285cd205090965c8a6fbe267c815fbd9579905f8f85740817 11 2047 4 15 11 2047 20 1048575
def cc_63_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x280a02718d2218820265d8158960508c8210801c4070000000000 0xe96bbd3d57a2aab453f5da6e9349f9da6d4e37e7e8b5a8fea51bf354567a7eb94dd2293a412766a5eb749f93b2d3a37e5edbca9b2b11fd3637e42dacc4fd6c9ba392765a7ab44d46c1e87435e2e9bc6d1788a2b253f59a6e340fc381b82817 10 1023 4 15 10 1023 19 524287
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_63_14 (Nat.sub p 448)) (cc_63_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (cc_63_12 (Nat.sub p 384)) (cc_63_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Bool.rec (Bool.rec (cc_63_10 (Nat.sub p 320)) (cc_63_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (cc_63_8 (Nat.sub p 256)) (cc_63_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 288)) (Nat.blt p 352)) (Bool.rec (Bool.rec (Bool.rec (cc_63_6 (Nat.sub p 192)) (cc_63_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_63_4 (Nat.sub p 128)) (cc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_63_2 (Nat.sub p 64)) (cc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_63_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def hc_63_0 : Nat → Nat := unpackHintV5 0xeb3134e5c95adae2bacf6eddcb2113c11284b5c2d4b17513ace125a2a2909d1164925aae8bb1aa86bd3d82511b787e756f2257649aa25e299c5989284ef2a6429b163da93c332e9f276ef022b92d18da7812b5890726e40099a3000026000000 0x55161c58755170b9543c9e160b110388c8462aaaaa1dd6aaaa288b545aaaaaa0d6547a82a8c155543aaa83060d062d55418355545c2e553f1f818f81838582c443e1f019f018320f8aaaaa83555d68355451516aeb554583060c583060c5aaaa83060c1832e0d383060c1832e0cb8b0e2c3aa972e1cb870e5cb9f0e1d5170b954b8fa2e3e818fa060e83c9e160b110b9702ebc01a70060c0389c8562aaaaaaaa0d06a83506aaeb5514a9168b51e5d478f060c18b060c18b060c183063c1a7060c183063c18f060d54197161c5871e3c3871e7c3874ea1d5ab5c2ea1743d6aaaaaa8582c1e3c07af0662034e00c1807139100d068306a0c1aa8b41a0c183060d50eeb991060b1eaaa0c583160c183360d383060cd8336aa6c39f0eb4cb544c2627018aaa0d06aeb551e2c58b163c7ac0c183160c1834eaaaa0c183060c7834e0c183060c7831e9c38b0eaa3c7870e3cf870eac3ea95d6acad555552b058883c780f5e00d38030601c4e442aaaaaaaa0d06a83506aaeb551401168b55e5d4997060c18b060c18b060c183069c1a7060c183064c193060d54197161c587267c3873e7c3873ea1d5170b898fa563e95ac0c7d030741e3f01ac1600b000000000001a0d060d41835516834183060c1aa1dd720d00164d41018b062c183066c1a7060c19b066d54d873e1d47c3e1f038000015541a0d5d67c58b3eaa800c183060c1aaaaaaace171f8fcaa0e07000000000002aa0d5575aaaa0d5500552e2c58b164cb800c183160c1834eaaaa0c183060cb834e0c183060c983267c38b0eaa4cb872e1c3972e7c387559c2e55263e8b8fa063e8183a0f1f8000d6202000000002aaaaaaaa0d06a83506aaeb5500062c18b062c19b06a5d6aa858f2ea5c19b4e0c183060c183366c39b3e1e0000000583060c1a1dd60c5a83060d45aac183062c183069c18355065cf87161cfa875478f162c58b1e3c7aa8f2e0c18f1e0c183060c183060c18f4e1c38f3e3c7870f552d5555543e0000000000008200358341aa8d0683060c183543bac1835060d664011683060c583060d38306aa0cba70e2c3a750eac2e5818fa060e83c9e0582034e00c180713900341aa9d0683060c183543bae41a20c550e1c38755170b9543c1e160b110381c8462aaaaaaa1dd6aa2a8c45aa2d5555506b2a3d415460aaa8b162c5aad52ad50b058888c46442a8b555559d6aa288b545aaaaaa1d54eac82a8c15552eac58b162cb9750e7c38b0eaeb543aa0c183160c18396aaaa0c183060cb83960c183060cb832e0c1833e0c1830f54ab555554aab058885cb8175e01c3e039600c18442a835555555559655758a2a97562c58b164cb80ac58b4eaa4cb970e5d7930e0c183160c18396aaaa0c183060cb83960c183060c983260c1835e0c1830f54ab555554a8001ac404000000005506aaaaaaaab2caaeb0045aac9ab162c58b56ac997555e5cf87161cfa8700183062c183072c18355065c183060c193064c183060c1af072c183067c183061eaa5aaaaaa95000003807003580000003518306aa8306a0c1a8341b552b3ac0116ab562c5a754e0c183160c183960c1aa832e0c183960c1830f552d54aab0582270072c018308806cb060d5506836aa567588315458b162d545c2e554f27800000001545aaaaa755550358822d516aaaaa87553ab2a3d4101516aeb55458b162c5aa972e5c3973e5c38b85caa5c7d171f49e5703060c583060c5aaaa83060c1832e0d183060c1832e0cb83060d183060c3d031e0c1d000000005c260000022a8355555550683541aaaa800206b0e1c3a2d16a7cba9b2e1c587d62c5870e2c58b3ea1c5c2e363e8f8fa56b078fc0c183160c183160c183060cf83460c183060cd83360c1aa832e0c1833e0c1830f40c78307400000000000020345830683068b5060c183551683418341a1e41a00081ac597555362d0ea3e1f03160c583060cd833e0c183360cdaa833e0c3c3c1c00883550683541a021ad54b8b162c5972ea1cf87161d5d6a8755bc2e552e3e8b8fa0f1f8183062c183067d5554183060c197068c183060c197065c183067c183061e818f060e800000002e130000011541aaaaaaa8341aa0d5554001035d48b45a8f2ea3c78b162c58f1e3c38f3e3c3b754f56b85d42e87ad5503060c583060c583060c1831e0d183060c1831e0c78306aa0cb83060d183060c3d5550000003c26000000020345830683068b5060c183551683418341a2e640010358b1eaaa6c39f0f4ca0c583160c183360cf83060cd8336aa0d1830f5400883550683541a021ad5478b162c58f1eb2b162d3aa8f1e3c38f3e3c3c3ea95d6acad503060c583060d1aaaa83060c1831e0d183060c1831e0c783060d183060c3d55500000000000008aa0d55555541a0d506aaaa00081ac59b362c58f2ea5c3d55540c583160c583360d4b833e0c383060cd833e0c183360cdd50020b062c1830e0c5a83060d010d68b558f1e2c58b163c78f551e5cf87161cfa87aaaa5a0f41eaad60c183160c1833e0c1aa832e0c183060c7831e0c183060c783460c1833e0c1830f555400000f09800000000080d3e0c1aa7d0683060c1a83068f5060d06879900040d68b458b4ea9e172c9e8183062c183068c18355065c183068c183061e818f060e800000000406a3060d54683418341a8e41a00081aeaa80020a0 24 16777215 10 1023
def hc_63_1 : Nat → Nat := unpackHintV5 0xbdd556bd2c2abbac60b3f1efaef140a75de5a351039e6d39993d4c93a566891aa381b9d87b519a6fdedd6b412765d15c5c1e6d55dd904a9ad146251d41d5143c396732068d2ced46282d3027982523251d1d058817d54c11e57c06aacf0001aa 0x2a9f0e2c3aaaf362c58b16bcdaaaaa80042e550f1f978fa5e3e800000000000155515541aaaa0d06aaa0003ddaf1fac1b1d1e3df931e4d758fb5eb41aa2d555549af162c58b5efd4993555555eaaaa7c38b0e9f5543aa810b91eaacaabc7d131f41e3f0000000001c03801ac0155555575aaaa0d06aaa0d5500055562c5a755aa55aa566c58b162d59b55554e1d79f5e7d3875000000000000000555155555555000545aaad555562c5a757aaa1d5478f162c58b1f0d478f555551eaaaa3c38f5e3c78f0f54caacab543e000000000000820035aaaaaaaeb5506aaaaaa8002a2d5555458b4eaaa1d561723d559553d02c4141113840aaaaaabad541aaa2a0c55162c58b55170b9553c9e160b111188c8462aaaabad4eaaaa288b545aaa87553ab2a3d415460aaaa1d55418b068306aaa0cf83170b954fc7e060e063e160b110f87c060c067c83e2aaaaaaaa0d5515062aa8306aaaaaa1c3a1d54387555170b954f8fa3e3e83c1e160b110f9303e4c0381c83e2aaaaaaaaaa835545418a8b575aaa2c3870e1d543870e1c3870e5c3870e0c583060c58306aaaa0cb832e0c183060cb83060c183545c2e552e3e8b8fa0f078183a063e8582c442e5c0baf00e07018300610ac555555555575a0d506aa8a830183068b45a9b2ea6cb870e1c3870e1c387438750ea1c5c2e363e8d8fa56b0783c2c161b2606c98081c0e42b0183418341835060d5541a0d9068830183aaa53e5d4f9745a2c38750e1c3a1c3870e1d43d555554b551f2607c980b0587c40e072201835060d41a0d55906cc88b060ca9168b51e5d478f0e1c3870e1c3870e1c3870ea1c18b060c18b060c18f063c183060c18f060c183060cbaa8306ad5ae1750ba1eb55555542c160f1e03d783710381c060c018440341a0c1a8306a83545a1dd60c1a83060e644583060b1eaaa1c3870e2c18b066c19b060c19b067c18306aab4cb544c2603055068355758341a833e6c58b162cf9b5555550e1c3870e1d55556a955695668f82c3e4c0f930440e07221555555555541aaa2a0c551e2c58b163c7ac1c3870eaa1c3870e1c3870e0d583060c58306aaaa0c7831e0c183060c783060c183561f54aeb5656aaaaa9582c441e3c07af00e070183006110aaaaaaaaaaeb41aa0d5515060306000a7cba9f2e8b45870ea1c38743870e1c3a873e3e8f8fa170b95ac1e0f0000000000000306a0c1a8341aaa20d906800008b45aaf2ea4cb870e1c3870e1c3870e1c38750e0c583060c583060c983260c183060d783060c183065d54183545c2e263e958fa56b0783c0c1d031f406b05802c0000000000068341835060d506a8b43bac1835060c1c834000f8b167d5500183060c19f06aaade171f8fcaa0e07000000000002aa0d55555541aaa0000c1aa8b162c59b2e6cb93266cbbf2e4c98070ea1d0e1c3871f0f87c3e000d688aaaaa7cd8b162c59f36aaa0001c3870e1c3aaaaab785c7c7d1f1f4aa1e0f0000000000002aa0d06aaaaaa8a8355400154bbf162c58b265c00e1c387550e1c3870e1c3970e1c383060c18b060d5554193064c183060c197060c18306ab785caa4c7d171f41e0f030740c7d0001ac404000000005555541a0d55555d683541aaa0008b5d6a8b162c58b55264c99726ec993265c9970e1c3872e1cf87101f0f87c3e0026130181c09aa820d25d1e2c58b163c78f1e4dd8f264c78f1e4d4b870e1c38856b170b87d54000c0e10341a00c0193764cda0c58b1ec4c58b36aa3c78f1e4dd8f264c78f1e1c3870e203e5d6ca3e1f5500030384aa0828b4993162c58b266c99355265c3870e1c3a87050085cb131f44c7d0783c00000300e00004c0683554001830106c83400182c18b065d41ad550b1e5d4b870e1c383060c19b360cd9f060c1c00000003161dd60d060c18b5060c1a08b55870e1c38750f552d547cd8b162c59f367cbaa9f2e1d0e1c3875a000000000000000068355441b320c1a8306a0008b55870e1c38750e0d583060c583060cbaa8306a8f1e2c58b163c78f551e5c3870e1c3870e1c183060c1831e0c18f1e0c18307552d541eaaa81c3e800000000000184c08200358341a83551a1dd60c1a83060c1835060d66400116870e1c38750e0c183062c183065d5418356172c1e0f030740c7d02c10381c060c018400d06a0d54e87758306a0c1839068a7060c 24 16777215 10 1023
def hc_63_2 : Nat → Nat := unpackHintV5 0xbea5a3b3aabfad01aaa841309f8e2d97c5f28fa20987e9ee7fea007849e8740d0f6f054269a159643d595ea5665622215111444b756746614542cce53e711736dde531955229cdf224cd401cedf8183d2c12e1570e99120a092404cd4f000133 0x45a2c58b162d7aa7aa96aa162d45a2c5af2eaabcba70ebcfaf3e9c3d000000000000000030688b55068366a418345a0c18306a000aa8306a0cba2d160d783060c1830e2c58b16bd5383063c783060c183060c183063c58b162c58b162c78f551e5c7871ebc78f1e1eaaaaaa5aa87c00000000000104006b060c18306a8b75aa8341a0c1a2d4183060d66a400155060d419745a2c183060c1830e2c58b16a9c18fa060e85c2e593d030060c0582c1138400c183060d516eb550683645830688b060c55162c58b55170b9553c9e160b111188c8462aa2dd6aaaaaa2883555550eaa756547a82a8c150e1c3aaaaaaaa0d506aa8341aaa0d06a87161f58b161c38b162d5506aa83170b8d8fa563e95506aac1e3f0b0586d781f5e088830500e1f2158aaaaa8341aabad55541aaaa8a54aaaaaaa83541aaa0d06aa8341aa2c58b163c78f0e3d98f0eaa835541d5ae1750b9555955aa8582c1e3c07af044418282719910aaaaaaaeb555506aaaa28aaa83541aa3c78b162c58f86aaaaa0c1aaaaa83067c38b0eaa835541d554aacaad07a0f556b560b111060a03d780f1e01c3e510f1555d6aaaa0d06aaaa8355551401555555506a835541a0d5506835458b162c9af4e1d7af261d5506aa83170b898fa563e95506aac9e5701ac1600b000000000015555555d6aaaa0d55540155506a83549af162c58b5f0d5555418355555060cf87161d5506aa83019c2e5541aab2f1f44c7d078fc000000000700e006b0055575aaaa8341aaaaa0d55540155506a835558b169d5506aa831e3c58b162c7c355555060d555541831e1c7af1e3c787aa556556aa1f00000000000041001ad555d6aaaa0d555555540155506a835458b4eaa835541c2e5541aab27a05888830504e102aabad55541aaaa8a2a8b162c5aa8b85caa9e4f0b058888c464231555d6aaaa9d55154622d516aaa1d54eaca8f5055182aaaa1c3aaaaaa8b161d0e2d54d9b362e172a9f1f47c7d078fc2c16221f2607c98070f907c5555555555551455555555458b162d54d9b361cd9b0e2e172a9b1f46c7d2795c2c16221b2606c982708562aaaaaaaaaaaa8a2aaaa870eaaaa87161d5458b555170b95558fa563e83c7e160b11179305e4c0387c8562aaaaaaaaaa8355454181c387545aa2d5586aaa6d36aaaaaaa87161f58b161c38b162d4faaa870eaa2e171b1f4ac7d23d559543c7e160b0daf03ebc1050440e1f2158aaaaaaaaaabad541aaa2a0c0e1c3aaaaa8b3e2c58b162f5aa2c5aaaaa2e171b8fcaa7e3f0b0586c3e221f0f907c5555555555514555e6c58b162cf9b55553e1c5874eaaaac2e553e3e978fa0f1f9782c443e4c0f9300e1f2178aaaaaaaaaaaaa28aaaab4aaaa2c58b16aadcfa70edcfa70ed4ab4aab542c162237260dc982723910aaaaaaaaaaaa2a0c0f52a7d3ea9f67a2d16aaa3c78b167d43d54b5130987c455555d68341d2a8b162c58f1e3c79f3e3d7af1e3c7aa8b163c39f0eab5ac5c2e5aa1e2f0984c55555a9516a8b5547aaa8f47aaaaaaaa2c58b163c78f0e3c7875550eab56b85d42e587aaad2aad50b0583c780f5e0828222708855555555555d6aa0d5515062a9f0e2c3aaab362c58b16acdaaaaad2ad52ad352aaab058881c3e2f260bc98442aaaaaa8355555545418a8b555aaaa3c78b162c58f86a3c7aaaaa8f55553e1c5874faaa1d56aaa65565583d07aab5ab058828220f5e03c78070f9443c5555555d6aaaaaa0d5515062a80282aaa8b162c5aaaf3e9c3af3e9c38b85caaac7d2b1f49e570000000000002aa8aaaaaaaa80000a8b545aaabd5549a4d5555555162c58b26bd3875ebc98757aaa1d545c2e263e958fa47aab2aa795c06b05802c10980000000002aaaaaaaaaaeb5506aa800070eaa2c58b166c99b264c99f26fc99326202c3eb161c58b261cf871f0f87c3e16000a2aa009f362c58b167cdaaa8001f0e2c393264d559c2e3e3e8f8fa550f1f80000000000001550683000051555500a55162c58b1e3c78f264c7937e3c78f101e1cf87261d987ad62e172d50b0005155004d8b164c4078b170d5478f1e4c7bf1e3c7931e4c9873e1eaa83c1ead64c141e130001015455499b162c58b264c140058b4eaa4c9930e4c98785caa4c7d131f49e82600008200002aa8a8002aaa8022aaa8b162c58b166cdaa9b264cdaf766c993366cd9b0e7c380f87c3e1f001b0981c0e06b55555 24 16777215 10 1023
def hc_63_3 : Nat → Nat := unpackHintV5 0xcce89aca809ac56148be0dd5b739b5affdcfaa29759fee8f963e6c8b26c68461b17f594277c1e6725d596d753a62d6a85d815558c92e4eea784839ac3ceed336c18b3275132e2d122925422321811df94a13ea840da9900cf82c0b28740002ca 0xea1f58f0e1c39752e870ed55000034eabc1834183a1e3cba970e1c387066d383060c183800000ea1f59b0e2c3970eb5543c79752e1c3870e1c3870e6cd87361c3878000000061d161c1a0cda9b060d362c59b1e3c387161c78f3e5cfa7d3e5cd9b0e2c39b3e1d99f3e1cd9b3751555555540000000000002c58b167c59f167c18b4f831687167c3d5001b162cd9b162cdc38755155543c78f365cda6d365cd87366cd9b0f400000000000000002c58b170c5c3162c5d51b062cda9b360c18b4015b38eacfab0e7c3ab3e1cf87aaaaa2a566cf8b5e2cf9b5e5cfabd3e5c78f1f40000000000000000acfaf3ebcfaf3e1cf9f0f547c19f4f833e802b56ad58f1e3c58f163c78f1e8f47971e1c78f1e3c3d555550f8000000020800d6ad1a3468d1a31e0c7a3c18f6a8015555555162c58b162c58b060c183060c58b060c58b060c18350e2c38b0e0c1830e0c58306aeb543aa2e17030740c5d2a971f45c7d078fc2c16030600c5822172e05d78070f90ac575a0d506aaaaaaaaaa8a2aaaaaaa2c58b162c58b160c183060c18b160c18b160c1830600b162c583060c383160c1aa932e5c3975e4c38b85c0c1d03174aa4c7d171f49e5700000001ac4040000575a0d506aaaaaaaaaa802a8b45a8316a0c18b162c58b162c583060c183062c583062c583060c1932eaabcb8b0e2c383060c383160c19f50e00b85c0c1d03174ad6563e898fa0f1f8000000000e01c00d6008b758306a0c18355060d418350683641a00aa2d16a0c5a83062c58b160c1830e0c58306a9c5c2e060e818ba56b2795c2c16030600c58089c21588b758306a0c183550683641a20c55162c58b55170b9553c9e160b111188c84622dd6aaaaaaab2d154620d555543aa9d5951ea0aa30543875168b0e8b45aaf2ea7cb8b0e2c58b0e0c1833ea1d38b85c7c7d2f1f4cd60f1f8582c3e4c0f9305e2070f90bc068341835060d5541834183641a20c162d55555555458716a8306aaaa2e17371f4dc7d2a878fc2c162f260bc9822070f90bc555555555555150607555552eaeb458b162c5aa0c1aaaa1c5c2e3f1f954bc5e160b0f87c442e1720f8aaaaaaaaaaa28aaaaaaa83065c183060c183060c1832e5c58b162c58b162d4383067c183060c1830e1c587161d5d6a875418fa060e85c2e552e3e8b8fa0f1f818030602c1622172e05d78070f90bc41a835575aaaaaaaaaa83454182c5aaaaaaaaa8b162c5b73e9c3b73e9c3aad4ad2aaad50b058dc9837260889c22106aaaaaaaaaaab22a0c5067cf83060c183060cfc3162c58b55553e0c1871e3d6a95a8f80c261301a0d5d60d06aab20d5555555060c783060c183060c183063c78b162c58b162c5ac0d983060c1830e2c58b16aa3c78f0e3c78781c3eaaaa1754aeb5656a818030602c16220f1e03d782708841a835575aaaaaaaaaac8a831168b161c5873ea1c58b5168b16dcbaab72e0c1d55554b5555550b058bc40e1f179305e4c220183645aa8341a0c1a8306b35222c183155060d419745a2c1831e3c183060c183060c1831e2c58b162c58b163c7aa8f2e0cf83060c1830e2c38b0e7d43d55555552d07a0f556b0600c180b058bc41ebc078f00e1f288780c183060d516eb55060d41835068366a44583060b16000a7cba9f2e8b4593264c58b0e2c38b3ea1cf8fa3e3e85c2e66b078fc00000000000000c1830000068aa8341b20d001055162c58b264c9932e5c9977e4c99343930e7c3aeb43a8f87c3e1f02c1880080aa220aa2c58b164c7931e3c7931f1c78f1ec4c3b30e3c39f0e2eaa5d6ca0b06200202a88825d262c58b163c78f263e38f1e3c98f263d4b930e7c3d550783d5ac160c260f0980000c006834060a008b45a932ea4c98b162c593264c393261d538b85c4c7d131f4b27a001600c098000000344183000550683641a000c162d55554014058b162d79f4e1d79f4e1d545c2e5e3e978fa554f2f80000000000014555555555540015555555060cb83060c183060c183064c98b162c58b162c5800d783060c1830e2c58b16aa4cb970e5d7930e0c7d030742e172a931f45c7d2797c030980000001ac404000041a835575aaaaaaaaaa834001168b161c5873ea1c58b5168b16bcbaaaf2e0c18000b85cfd60f1f978fa5e3e80000000000001a2aa0d068306a0c1ac8340009b726ec7dac1831e4c1837e3e9931e3ed63ed7ad55060d419745a2c183264c183060c183060c1835e2c58b162c58b164cbaaaf2e0cf83060c1830e2c38b0e7d43800c7d030742e172cbc7d131f41e3f0000000001c03801ac00183060c1aa2dd6aa0c1a8306a0d06c8b060d000 24 16777215 10 1023
def hc_63_4 : Nat → Nat := unpackHintV5 0xe4fae7e06d23db055ad09e9acc1921c555b1ba7eb6b6151aaa86e4a08a7f9b953d96255c900d8685aa998099447b395873c1de6c2de55fc31b57f9f24bd70945d1813b6e99367d3c2ee9e529995424a13e1d15e3173578108daa0546d2000151 0x150b458b168b2e2c58b162c593262c58b162c58b162c5bb162c58b162c58b265d9a4d665c59f0e1c58b0e1c587161d987661c085d0baab5d55555550000000001c03801ac00583168b062d162c58b162c58b160c5a2c18b438b161ea80078f2e5d98d8b166cd93266d9bb364c99b366cba97361cf870a66aa000e070358341a0d06a5d2eac3b30e5d43ab36cc5b316acdd2ad070e001542d54b534000000000000ada6aa8753acc1ab306b3200974b8f1e2c78b1e3ea26ad98b262d5ab265d54b971e3c78f1e3d98f1e4c98f1e3c7ab0ecc39750e3c7870e3cf870e043ea96d6b4ac3e1f555554000000000700e006b0056aaa3c1a8f06acc1a9306a1d4ecc802aab0ecc3aaab36cc5b316acdaaaaa800552a2d55555000001c0000000155555555555401516ab355549ab662c98b56ad49935555566aaaaac3b30e9f5543aa8154b2aadaeaaaaa8000000000e01c00d600aaaaaaaaaaaaaaaa00ad9b3564c993764c993564c993664c993667c39f0e7c39f0e00f663c58f163c78f2e3d1e8f1f554001550faaaa87c3e8a87d0f800000e01c00d60000000acfaf3ebcfaf3e4db93264c993461cf9f0e3c18f47831ed50033366c58b365d4b870e2c3eb01e3cba973e6ddd55541c3d55545541c0e00000d068341aad9b3563c78f163c58f1e3c7a3d1e5c99f3e2c98b3eac9973e934f97aa0000000e1c3873e1c3870e1cf87a80aaaa83d0f87d05541eaad600000f09800001c038000001f3e7cf9f3e7cf8f063d1e0c7a7c19349833e870e7c3870f54008b5993262c58b164dd9326aa4db833e0c183160c1832eaa0c1aa9f0e2c39f50e002805f85ccd626de8993a060e818fa0f1f800000e000001c00d6000d06a0d53e934983060c1a83060c4f8306c83400098b262c99749a5c3870e1c0aa1f44c7d07a00000380700358023468d1832693068d0e8d38791c001d439752e2c5972e2c58b162c58f52e3c78f3e3cf8f1e3cf8f8e1cf8f3e3c38f0f550f000880d60d068341a8b1162c58b162cba97aa96aa162d45a2c58f1eaa5cbb70eccfb33edc3d0000000000000000b45aaa2d16cc8b06a2c1a8022dd6a2c5aa2cb8b162c58b2ea5c58b161c58b0e2c58b162c58b163c7aa8f2e2c58b162c58f162c78f162c58b1e1c7b31e3c787aa96aaaaaa1f00000000000041001ac5a2d55160d45835168b45835160d66400587161d55458b51e3c79f1efc78f1e7c79f162c58b550e7c79f1e1c7871f0faaa1e0001101ad5555551162c58b16ab54ab543e162c58b162c58b55557e1e39f8e7df8750000000000000000015555555555540145aaaa8b75aaa87162c58b5551e3d5555478b162c58b162c5aaaa8f0e3e38f1e3c3ac3d556aa956a87c00000000000104006b555555555555555500162c58b0e2c0e1c3870e1c3d555550b162c58b162c5af2ebd5eaf2e1c3870e1c3870f40000000000000002c58b162c58b161c3870f542c18b458316800b162c587161f5870e1c3870e1c387161c3970e8743870e1c38b162c58b162c58f1e3d1e8f2e1c3870e1c3870e1c3870e1c38f0e1c78f0e1c387aaaaaa0f55541e1f400000000000104006b162c58b162c58b0e1c3870e0c3a1c1874583168b062daa00162c58b162c381c59f0e7c3d555550f858b0e1c587162d9978ec759970e1cf9b1e3c387a0000000002000000162c58b162c58b0e2c587aa160c5a2c18b4003870e2d162c5a2cb8b162c58b16ac58b0e1c38b0facf873e1c58b1e3c58b162c58b162c58b1e2c58b162c58b163c78f47a3cb870e3cf8f1e1c3d5555555550f80000000000020800d62c18b4583168b162c58b162c587162c38b062d160c5b5400974b9f0e7c38a1eaa5aa87cacdb716dc5ab363c3aa870e1c3a8f4387a00000000000000056af5543a7d995e0d57835004ba5cbab2e2cb8b2e5c3870e7c39f0ea1f5a870ea8f1e3c58f163c78f551e5c78f1e3c7971e3c78f1e3cb8f2e1c38f3e3c7870f552d5555543e000000000000820035ab57aaa5c1a9706a1d3e8f06a3c1acc802a870e1c3a2d52ad52b36bc5af16acdaaaa870e1c3870e1c3a8000000000000002aaaaaaaaaaa802a870e1c3a87d6aaab545aaa87478f1e2c78b1f0d55543870e1c3870e1d5547a8f1eab54ab541e55a587a80000000000041001ad55555555555555540154f873e1d46a956a87cacdc7171c5ab36aaaa1c3972e3c7870ea0000000004001ac000155555555555401555554f873e1d554478f1e2c78b1f0d555555543871e7c78f0e1ea95556a87c000000000104006b545aaad5553e1cf8752eaaa1f58f1e3c58f163e1a8f1eaaaaa3d55543871e7c78f0e1ea9955956a87c00000000000104006b555555546aaaaaaaaaa00974b870e1c38752aa5aa959b5e2d78b566c78f552e5c3a1c3870eb40000000000000009d4eaa8743b329c1aa706a00974b870e1c38750183060c1a835060c78f1e2c78b1e3c7aa8f2e1c3870e1c3870e0c183060c18307552d541eaa0000000000820035a5d2e1c3870e1c3aa87d61d5870e1c5870e1cb875478f1e2c78b1e3c7aa8f2e1c3870e1c3870e1c3870e1c38f0e1c78f0e1c387aa96aa0f55541e1f4000000000001c26041001ad3a9d550e87438343a8c38706a3c1a8f06b32006c58b2e1c3a1f5a1d6aa878f2e5cba9b4b972e5cb9b365cdbf2e5cb87367c3c0000000341a0cda9b060d 24 16777215 10 1023
def hc_63_5 : Nat → Nat := unpackHintV5 0xf72db7f05db4eb5d40e3e5deddb58cd266d4cd1554c78d62bffde4b9cd8cb345a2a73f02a011cb990dc18ce30b80b70b7b894b73f9e46ca1d6677d4960dda856e27f4a731c42f5df361f362bca95266958216d3f191a151275a906d2e90001b4 0x1516aaaaa1c3870e875543aa87561c387161c3a87555550e1d55540aa59556d75555540021300000003581c00e002aaaaaaaaaaaaaaa80070e1c3870e1c3870e1c38b0e1c3970e87438702a83c1e0e1e838fa000003581c00e0027469d1a7469d1870e1c387061d0e0c3b234f000aa9b0e2c3aa9b2e2c58b165cbaaaaa8001b85caa1e572b1f4ac7d0000000000002aaaaaaaaaaa8025d45bad555266c58b162cd9b55576a4c9aaaaaa9b0e2c3aa1d3eaaa01b85cac8f555563e898fa0f2b8000000000e01c00d600aaaaaaaaaaaaaaaa0088b161c5872ea1c58b5168b165cbaa972e1c38000b85c5d60f33998fa663e80000000000005a2d550e8b45835160d645a008b75a8b16a8b2e2c58b162c58b162c58b664cbaa972e2c58b162c5b3162c993162c58b161c5872ea1c58b0e1c59f0e1c0170b8bac2c5d0b1f4cc7d131f41e670000000001c03801ac005a2d55160d45835160d458350e8b645a00a8a2c38b0eaa2c58b162c58b16aaaaa0002e172a8799cec7d3b1f4000007000d6000000aaaaaaaaaaaa002e162d554478f1e3c78f1e3c58b162c58b162d55547871e1c587161d540000000038070035aaaaaaaaaaaa8028b555516eb5264d55555d8b162c58b162c5aaaaa7d550e2c38b0eaa028f555a170b95598fa263e83cce00000000038070035802aaaaaaaaaaaaaaa8022d0d87161cba87368b162c5a9716aa2c5870e0006e1717583cae563e958fa000000000000168b5543a9d660d598359568022d10e2cd8b52e4cd8b3e2cd9b3fac99752e5c9970000dc2e2eb1f8fc7c7c4c7c00001f000d6070005a2d553e9f4f83498364fa00a2c5a2dd6a8b162c99b162d98b162cd9b666c997552e5c997264cb97664cb93265cb972e6c38b0e5d43972e1cb870e5cb9f0e1c0370b8bac5c7d171f4ac7d131f41e57000000005c2600700e006b00168b554b8352e0d59835260d43a9d95680070e0007d3e5cfa7cb9b162cd8001c0e1c3870e1cf8fa3e3e8dc2e572b83c1e00000000000003e0c5a7c18b458b162cf8b3e2c3870e1e167e00266c99b162cd93499726932607161c9933e1cf87370b898fa263e95cae0f1f800260000000b162c593062d260c5abc5af161c59f0f0b57000b162c58b662c593262c58b162c593264dd93264dd8b3e0b161cf873e1c0162c58b2e2d168b162c98b361c38000b85cce67137744c9d078fc2c5d0b1f4000000700e006b000000162c58b162c58b162c58b162c58b0e2c587160c5a2c18b6162e00362d98b36cc993264c58b162c993264c9bb264c9bb367c38b3e1f0e7c3804c993665cdaed365c58b162c387000370b95cae26ae8993a0f1f8d8fa563e8000000e01c00d60000002c58b16bc5af164dd8b164c98b161c59f0e6c18b578316c2d5c002cb8b2ea1c58b0e2cf872eaa5c58b361c02eb0b85c1e571b8dc00000000000aa2d168745a2d16c8b400d8b166cd9b361c58fc3bf0e4c993365cda6d365c387000370b95cae0f2b8d8fa363e8000000000000058b162e18b7e2c38b4e1cd83169b062d85ab8015499326ec99326ed49935553e1cf874f8a80b3545aaa934ba1c0019cce5526ce8993a0f1f9591ea000000700e006b0000005555555555555555002e5cb9749a4c98b26ec59b266c993266c9bb162c5aa4d4369f40dab1f0f95c4e000e070358341add26a5d2e4c993764c993764c9aa81f0e7c397500060c18306a0d54183060d060c1b399c5d626ce8993a0f1f81c0e0000038070035800025d2e4c993764c993764c99326aa4c99f0e7c3972ea7c00b97165c5972e4c99355500067338bac4d9d132741e3f171f45c7d0000001c03801ac0000017abd5526dd499350e9f4b834ba8cb9706b2bd000e1c39b162cd9b4f973e9b2e02c59f162c59b367cd80000b162c580132e7d269f2e1c387d61c5870e1c5870e1c38700dc2e363e8f8fa572b8f8fa263e83c1e000000f84c0000e01c0000058b162cd83169f062d3e2cf8b3e0c5a4c18b43870e1e167e00162c58b165c38b0e1c3eb0fac38b166cd9b366c3873581af58b85cae57070f073f1b8dc000001ac3580000b162c58b162c5870e1c38b162c5c2c5c001c387168b162d165c58b162c58b264c00000058b162c58b0162cf932e7d269f2e1c5870e2c3870e1c3eb0e1c3873e1c0163e858ba170b99cce3e3e898fa0e1e0e7e0584c000000000e01c00d6002c18b4583168b162c58b162c58b062d160c5a1c3870f0b170025d2e5df97165c5972e1c387267cf8b262cfbf053ea972e5cb80002a80070e1c3a87d6a1c3aa03399c5d62e3e8b8fa3e3e898fa0f07800000002e130038070035801f4faaa5c1a9706a7c1a9306a1d0ec9f4015554d8b3e2c59b366d44b93266cfbb364c99b366c387161f5870e1cd872e1c287c3e1f0f8000381c01555555555499f3e2c98b3efd555554143870e1d55440673395554f8fa263e83c1e000000038070035802a2d5555499f3e2c98b3efd4993000000555053e5c3870e1cf8750eaaa1f580ce6723d55954f8fa263e8387839f8004260000000700e00000aaaaaaa8d555555555400d8b166cd87161d987661ea858ba665ddaed665c3870002a87d55555550000000000000b162c5b316fc587169c3bb062d760c5b540151b162cd8f47971e8f1e4cd8b162c59b363c78f1e3c7bb1e3c9931e3c78f265d9a4d665cd87161c78f0e1c79f0e1d987661c0ab5c2ea1743eaaaaaaa8000000000e01c00d6002c58b163c18b478316b3162ef831693062d0e2d387aa00162c58b161c587661d987162eaa999776bb59970e1c0028aaaaaaaa800000e001ac00000058b162c58b162c38b161c583168b062daa00 24 16777215 10 1023
def hc_63_6 : Nat → Nat := unpackHintV5 0xbdfc15bd6027b91513b5acdab1411baab5a3a665149f6dbe9f18159aa11e93cdb5909ccc8bad3c8435de7e058c730abf6e094068816260bdf15ae5765491954942d441b1e43b31a02f72f028e1a41cfef918712313095a08ce8f04511f000114 0xf6cf87b67e1e13555a555000162c58b553f6c3db3e1e1714ab4aab540000000000000aaaaaaaaaaaa001ea45a2d53ecf54fa7d54058b162d3e7d50e1eaa5a801103582aaad2a8b5ebc58b162c58b167cf8b162c5a00b3e7c38b161c38b16aa2e1756baa000005555a955168b5545aa8b545aaaaaa802c587162c587162c58b5550eab0ba17556b655655aa00000010400d60000aaaaaaaaaaaaaaaa00aaacdaf16bc5ab36a0001c3870eaaaab554ab4aaa54000000000000aaaaaaaaaaaa00a8b555aa801c3870e875543aa87861c387161c3a87555550e1d5556aaa587aaad2ad5ae0f507800410035800000002aaaaaaaaaaaaaaa802b166d54f873e1d5559b176c5ab36a000b4ab54ab078aa5550010000000000055555555555500545aaad5401e3c78b1e2c7c351e3d555547aaaa9f0e7c3a7d550eab55532ab2ac1e83d55ac004100358000000002aaaaaaaaaaaaaaa802a2d555015543aad23d5595680041003580002aaaaaaaaaaa80172e1c3870e1c38aaaaa870e1c3a8002a9b85c7c7d1f1f4aa1e0f0000000000002aaaaaaaaaaa8025d45bad5550e1c387543a1d55439b0e1c38b0e1d55438750eaaaaaa01b85cac8f5550f078387a0e3e8000000000d607003800aaaaaaaaaaaaaaaa0088b0e1c3aa1c3972eaa1c3870e1c38750e1c38000b85c5d63e3e8f8fa0f0780000000000005a2d55160d458350e87645a008b75a8b16a8b2e2c3870e1c3a870e1c3870e1c3870e2c3870e2c3870e5d543870e2c38b0e1c3870e2c3870e1c3802e17175858ba163e83c1e0e1e838fa0000000003581c00e000b45aaa2c1a8b06a1d0e8706a1c1ac8b40058b0e1c3870e1d55554401403870e1d54f8fa3e3e85c2e550f0780000000000001555555555554005c2c5aaa8870e1c3870e1c3aa871e1c3871e1c387161c387161c3aaaa8000000006b03801c55555555555500516aaaa2dd6875543870e1c3aaa87555550e1c38b0e1c38b0e1d5554051eaab42e172a8783c1c3d071f42130000000003581c00e002aaaaaaaaaaaaaaa8022d10e1c38b50e1cd870e1c3872ea1c3873e1cdc2e2eb1f8fc1c3c1c7c0000000070005a2d553e9f4383438364fa008b450e1c3870e8b16aa1c3870e1c38750e1c38001b85c5d63e3e8f8fa0f078000000000038002d16aa9f06a7c1a8743b27d005162d16eb5458b161c3870e1d43870e1c3870e1cb870e1c39b0e1c38b0e1c397550e1c3970e5c3870e1c3970e1c3870e01b85c5d62e3e8b8fa0f078387a0e3e8000000000d6070038002d16aa9706a5c1a8743a1c1a8706b29d000e1c39b162cd9b4d97369b2e070e1c387000e1c03870e1cdc2e363e8d8fa572b83c1e0000000000000162c58b360c5a6c18b538b4e2c3870e1e169e000e1eaa8fa7cb9f4f97362c59b0e1c0003870e1c3870e1eaaa8aaaaa8000000000000f83169f062d162c58b3e2cf8b0e1c387aa00a8d8b166c7a3cb8f478f0e1c3870e1c3870e1c3870e1c3870e6c3870e2c3870e3c38f0e1c3870e3c3870e1c3872e1d0e870e055ae1750ba1f555555540000000006b03801c00162c58b1e0c5a3c18b538b4e2c3870e1c3830e87061daa000e1eaa858b162cfa7cb9f4f970e1c387000e1c03870e1e8aaaaaaaa8000000000000058b162c583168b062d162c58b0e1c387aa00a85a2c58b4597162c58b0e1c3870e1c3870e1c3870e1c3870e2c3870e1c387161c5870e1c387161c387161c3872e1d0e870e042e85d55aeaaaaaaa816130000000003581c00e000b062d160c5a2c58b162c58b161c3870e1c18743830ed5000f1e5cbb3070e1c39b0e2c39b0e6c3870e6c39f0e1c39750e14cd54001ac381c068341a0d3e6cf8b3e2cf9b4ba5d69683870e1c3870000ea1eaa69685aa8000000000000fa7d3e0d4f835550e87664012e971e3c58f163c7d41c3870e1d43870e1c3870e1c387561c387161c3872eaa1c3871e1c7870e1c3871e1c3870e1c087d52dad695aaaaaa0000000003581c00e002753aaa3c1a8f06a1d0e8706a1c1acc802aaa870e1c3870e6c39f0e6c38b0eaa6c39b0e1c39b0e7c3870e14b5554001ac381c5555553e6cf8b3e2cf9b55550e1c387550050aa51aaaaaa00000000000055555555555500 24 16777215 10 1023
def hc_63_7 : Nat → Nat := unpackHintV5 0xaf1d63a9d9519f9e8f9a255e9495648a7e8685155a7ae28d75d543705d5e65ee9c61053a5b9d5a56b53a51f1314a61e4464d0541893139f9e439b01239202434313c2ccdd92841231fda1a1b552116ed1a123d2c0ded140adcc406d1030001b4 0x58baaa500045a5d99f6e1d99f6e1cd8b166cba97aaaa2a87ad550000000000003706adc1a8b45aaadd66cc8051b162cd8f1e3c7af5e3cf9f1e3c7a5d1e803c39f0e4c9972f5ac5c2eaa1f000000341acc18341b356ecea45a5d479751e3cb9b162c58b265c78f1e3c78f264c78f2e3c78f1e01b162cd8f1e3c38f663c39752e4cb970e5c987ab5c2ea1743d6aaaaaa80000000d620200000b45a3c1a8f06aaa4c1a9706add66cc800b175548b4580280b162c5b33edc3b33edc39752f4555552d5400000000000002d168b06a2c1aaa8b45b320142cf9f162c58b162c5af5e2c58b168b4ba00b3e7c38b161c393265cb8b85d5aea8000001a0d660c1a0c5a8b17528b16a2cba2d162c597162c58b162c58b162c993162c58b162c58b005b3161c58b161c58b162cba97265cb872e4c3c2e85d55ae5aaaaaa80000000d620200000b06a2c1a8b45aaa2c1a8b06a2d16cc802b36bc5af16acda5d2ea0001c3870e1c3d550750f5555552c540000000000009d4ea706a9c1aaa8743b3200974b97564c597164cb801c3870e1d43870e1c3870e1c387661c387161c3872eaa1c387261c9870e1c3872e1c3870e1eaaa96aaaaab5c1ea0f0001ac404000000004ea755498352e0d43a1d0e0d4383599002e5cd8b165c0d9f2e1cf871e3cb972ea6d2e4cb932e6cd9736fc997261eaaaaaa0d688000d068341a974b9f0e7c39750eacdb316cc5ab3600a01c3d55554b51555500000000000002b57aaa1d3eaf06abc1acc8025d2e5d593165c5932e00f1e3c58f163c78f551e5c78f1e3c7971e3c78f1e3c98f267c39f0e5d43932e1c3973e1c3d5552d555507a0f556b0003588080f098000000002b57aaa4c1a9706a3c1a8f06a1d3ecc8025d2e5c98b2e2c99700ba97265cb872e4c3d175898fa2e3ea8000d620200002aa9306a5c1aaca00a8a1c3875555555366c387439b0fad54d9b366e172a9f1f47c7d07571f3f0000000000002aaaaaaaaaaa802aa2aa0006c58b366d54d9b361cd9b0e6e172a9b1f46c7d2b95c0000000000000aaaaaaaaaaaa00aaaaa1c3a80001c38b0e1d5458b555370b95558fa563e83c7e000000000000555555555555000e1c3aa2d536aac3555369b5555550038b0fac58b0e1c58b16a7d55438755370b8d8fa563e91eaacaa1e3f000000082006b000055555555555555550040550e1d0e1c3aaa87361c3870eaa6e370783c1e0f000000000002aaaaaaaaa802aa8b16aaa0001c581c387555550e1c5c2e555e3e978fa0f078000000000001555555555554015168b545aaa007161f5870e1c3a1d550eaa1c58750eaaaaa1c3aaaa870e1c5c2e47aab2a8783c1c3d071f40020801ac00000001555555555555555402d70f45dac7c4c5550e1d55400058b0e1c0e2c3eb553e6d5545c2e551f43e83c7e0010000000000555555555555000e1c3aaa2d16aa8b5516a8b5555550058b862c5870e1c587d69f5543aa8b1f42c5d0b85c8f556550f1f800000041003580002aaaaaaaaaaaaaaa802aaaa9b36a0001c387155554387370b95558fa563e83c1e00000000000055555555555500545a2d5369b55003870e1c38b0fad43aaa870eaa1e18750eaaaaa1c3a872eaaaa1c387370b91eaacaa1e0f070f41c7d00082006b000000384c0015555555555555554003870eaaaaa6cf8b162c59fd6a8b16aaa01b85c6e3f2a9f8fc00000000000aaaaaaaaaa00aa8b167f58b166cfa0073e1d5543af0e6e172a9f95c1e0f000000000002aaaaaaaaa802aaf367c5af167cda8001f0e7c38aaab4aa7c7d2f1f41e3f00000000000002aaaaaaaaaaa802aaaad28001b162cdaac33f0c3c33f0c3952ad2aad50000000000002aaaaaaaaaaa8007a953e9f54fb3d169b5501e3cd9b3ea1eaa5a8011035aaaad2a9b162cd8f1e3c79f3e3d7af1e3c7a01b363c39f0eab5ac5c2e5aa000005555a9516a9b5547aaa8f47aaaaaa806c58b363c78f0e3c7875550eab56b85d42e587aaad2aad5000000082006b0000555555555555555500 24 16777215 10 1023
def hc_63_8 : Nat → Nat := unpackHintV5 0xb89b10b3215eae253fa3a2a19f15239ae10d9439aa8da9a4820ee781e80981e80081c40980b04580b00080b0007fc43b7971956dc6eb66f5b46041ad5a158b5381a5484ace41b5a5367ece2fe9a5246ae01dc5a91232e50b8da906514f000194 0x5162d459745a2c38b0e1c3870e1c3870e1c3870e1c3aa87d61c5870e1c3870e2c38b0e1c3870e2c3870e1c587161c3872e1d5163e858ba170b8bac1e0f070f41c7d02c05801ac00000000e13000160d45835168b5543a1d0e0d0e8b0e1c1ac8b40058b00045a2d696858b162e99fa61e99fa61cba97aa5a9a19aaa000000000000168b45835160d5545a2d99000167cf8b162c58b162cfcf162c58b45a5d9859f3e1c58b0e1c78f2e5ea99a8582c0d6000d068341a028b16a2cba2d162c58f162c58b162c58b162c78f162c58b162c58ba85b3161c58b161c58b162cba971e3c7871e3c3c2e1f55550baa5b5ad2b540b016006b0000000000160d45835168b5545835160d45a2d99005550005555162c58b55667d987667d987aa5516d7555554000000000000aaaaaaaaaaaa000aa2cfbf162c58b162c59f3e2c58b16aa2cf9f0e2c5870eab555542c1606b0055550155168b5545aa8b545aaaaaaaa2d98b0e2c58b0e2c58b16aaa1d56aaaaa96555b5d502c05801ac0000000001555555555555555400387000162c58b5eaf2ebd5e5c3870e1ea8387a0e1c387aaaaaaaa2aa000000000000162c58b160c5a2c18b458b162c3870e1ea8000168b162d165c58b162c3870e1c3870e1c3870e1c3870e1c38b0e1c3870e1c587161c3870e1c5870e1c5870e1cb8743a1c3d55555555556b83d41e0580b003580000000000b062d160c5a2c58b162c58b161c3870e1c18743830ed5001752e2c79f0e5d1f13178b2eac0f307098b5e2c58b162c38b0e7c39f0e2c58001752e1c3d555555545555502c000000000000058b162c58b162c38b161c583168b062daa00005a2c58b4597162c58b162c78f162c58b162c58b162c78b162c58b162c58f1e3d1e8f2e2cf870e2c5870e2c38b0e7c39f0f55555555541e83d55ac1602c00d6000000000002c18b4583168b162c58b162c58b062d160c5a1c58b0f540000b458b168b2e2c58b162c587162c587162c58b163e858ba170baa81602c00d60000002c18b4583168b162c58b162c58b162c5c2c5c004c9870e2c397260b4ba972ea5cb9b361c587366cd9b2eaa1cdc2e3e3e8f8fa2eb078fc0000000000002d169f06a7c1aaa874fb27d00264c982cba5cb80281b162cd9b366c39b361cba97370b8d8fa363e8bacae5700000000000000b45a6c1a9b06aaafd655a002c5870e2c5970ea0008b4b97161c38b161c381c5872ea1d58fa563e8dc2e2eb078fc000000000000bc1aaf06a2d16aa874fb2ad000e1c3a2d2ea5cba972e5cd8b162c5932e5cd97364cb93265d997265c9930038b0fac58b0e1c58b165d43932e1c3973e1c39b85c6c7d2b1f45d6263e8b8fa0f1f80000000d620200000b45a6c1a9f06aaa4c1a9706a1d3ecab40058b162c58b162d168b50000e070e1c3870e1c3870e1d438b85cbc7d2f1f45d60f0780000000000005a2d160d45835550e87645a008b458b162c58b162c5801c587d61c3870e1d43870e1c3870e1c387161c397550e1c3930e4c3870e1c3970e1c3870e1c387170b8bac4c7d171f41e0f070f41c7d0001ac40400000000168b5545835160d43a1d0e0d43835916800b161c38b0e2c5a2d1600a02c381cf9b0e1cb970e1cba87170b998fa663e8bac1e3f0000000000000b45a2c1a8b06aaa1d16c8b4003870ea2c5a8b2e8b458b165c58b162c58b162c58b264c58b162c58b162c0162d98b161c387161f59750e4cb870e5cf870e2c7d0b1742e17175898fa2e3e83c7e0584c0000000d620200000b06a2c1a8b45aaa2c1a8b06a1d16c8b400d9b162c58b2e5d169750000e1c381c3870e1c3870e1d439b85cac7d2b1f45d60f07800000001000005a2d4e0d53835550e87653a008b4b97362c58b164cb801c3870e1c587d61d43870e1c3870e1c387661c3970e5d543a1c387261c9870e1c3872e1c3870e1c3870e6e17175898fa2e3e83c1e0e1e838fa000358808000000002d16aa9306a5c1a8743a1c1a8706b29d003e7cfaf3e7cfaf3e0cf83554ba5d40012e833e1cf87264c9830697060cb9740e5d9cce3ebe8f9fa071f8bac1e3f0000000000000001f3e2c58b167d7aaa8001f0e2c393264d5159c2e3ebe8f9fa550f1f80000000000001553e835555555003e6d78b3e2d79b4ba5d4000f873e1c993265cba072f4bc7d1f1f45d60f1f800000000000017abd3e0c1a9f06aaa874fb2bd00 24 16777215 10 1023
def hc_63_9 : Nat → Nat := unpackHintV5 0xd399cfc7c2f6bbcefdb43de4ae0d8ca312bf9e213c96a9de91a9408cad3f84d5f67e8195777dc16bbef061c27f5b998a53c1f64d918c4771883c22d43721402fa9de2f60122e5044293946243d3f1c99e916ed6b10bd8c0add780758e10001d6 0x8b0005265c0555136aaa9349aaa87362c59b264c9bf271c9935547aab1b85c4c9d13574aaae57000001ac1600b000000015555555555555554000362c59b264c9c726fc9930e6c0e1c387261c9870e1c3870e1c3870e001c5807261c3970e8743870e1c39b85c4c9d13574ae570783c1c3d071f406b05802c00000000000162c58b264c58b269c58b4e2d38b0e1c3870e0c3a1c1876169e000e1c0003870e1c05e9f2e7d5e5cd8b166c99326cc9c7264c993266cd87039b264c9930e1c3930e4cf873e1d58fa3e3e8dc2e264e89aba572b83c7e000003582c01600000001f062d3e0c5a2c58b164c98b164d78b16bc5af161c59f0f0b5700070e000bd3e5cfabcb9b162cd93264cd9b0e07367c39f0eac7d1f1f46e172b95c1e3f00000000000001f062d3e0c5a2c58b16bc5af161c59f0f0b57000b16000a1c3a970e8b4b9f438750e1cd87161c50eac7d2b1f46e1717583c7e0000000000005e0d57835168b5543a7d95680008b4ba972ea4cb97362c58b165cb93265c9972e5cb978e5c9932e4c3870e6c38b0e4cf870e7cf870ea1f5a870ea9b85c4c7d2b1f45d62e3e8b8fa0f1f80d60b005800000000002d169306abc1aaa9706a5c1a874fb2ad0050005555550e1c3870e1c3870e1c38745563e958fa370b9543c1e00000000000055555555555500015555543870e1c3870e1c3870e1d43eb554daa2d526935557aaaaa1d370b898fa563e9543c1e5647a81ac1600b000000000015555555555555554015401415554d87161d44b970e1cf970e1cdc2e55563e958fa0f1f8000000000000155555555555400055555555555555361c587267c3873e7c3875551370b898fa563e955543c7e03582c0160000000000a8b54daab0d5549a4d5555555361c587267c3873e7c38752eaaa1f59b85c4c7d2b1f48f556550f1f80d60b005821300000000005555555555516aaaaaa001c38002972ea5cba2d2e1c3a870e1d0e1c3870ea2b1f4ac7d1b85c5d60f078000000580000009c1aa706a2d16aa8743b29d0001169752e5d49970e1c3870e1c3870e1c3870ea03060c183060c183060c183506a0c19b85c4c7d2b1f45d60f0781c0e03582c01600000000008b4ba972ea4cb870e1c3870e1c3870e1c3870eaa1f587361cd870e1c587161c387261c9870e1c3875e1c3870e1c3970ea9b85c4c7d2b1f45d60f078387a0e3e80d60b005800000000002d169306a9c1aaa8743a1c1a1d161c383594e80028000aa8b45a8306a0cba936ea4c98b162c5835e0c183060c393264d3935e4c9af54e2e17031f40c1d132744d5d2b593cae03582c0000016000000030688b060c183060c1aa2d16aa0d06c8b060d00000d8b166c9a5d265cd8b166c987261cdc2e263e958fa572b95cae03582c0160000000b162c593062d062d162c58b85ab800387000162c58b3eaf2ebd3e5c0e2c58b0e2c58b3e1cf87170b8f8fa5e3e99cce0f47e8000000000000058b162c583168b062d162c58b0e2c58b161e162e00162c001168b5161d4387161c58750e1c5a1c38a1c5c2e7e3e9f8fa2eb078fc0000000000002d168b06a2c1aaa8745b22d000e022d16a5cba7dd62c58b162c58b5162c58b5161c387170b8fc7e2eb17a2f4000000000002d168b45aaa2c1a2c1b22d0001458b5165d168b162cb8b162c58b162c58b165cb8b162c58b162c5870e1c58b3e1c38b161c5870e2c38b0ea1f5a870ea8b1f42c5d0b85c5d62e3e8b8fa0f1f81602c00d600000000002c1a8b06a2d16aa8b06a2c1a8745b22d0050005555550e1c3870e1c3870e1c387515170b978fa5e3e9543c1e00000000000055555555555500015555543870e1c3870e1c3870e1d43eb5545aaa8b45aaa2d516aaa1d163e858ba170b9543c1e5647a82c05801ac000000000155555555555555540287eb16a2e3e1c7dac98bd5550005555161c5875452e5c387162c387170b9547d0fa0f1f816001ac000000000155555555555400055555555555555167c387162c387161c5875551163e858ba170b955543c7e0580b00358000000000aa8b45aaa2d545aa2d5555555167c387162c387161c58752eaaa1f58b1f42c5d0b85c8f556550f1f81602c00d60000000000aaaaaaaaaaa2d555554003808b45a8b52e1c3870e2c3875e1c3970e2e171f97c5d60f41e8000000000005a2d168b55438343870e0d91680070e0008b45a8b16a5cb870e1c3870e1d0e1d43a82e172f1f4bc7d17583c1e000000000000168b45835160d5543a1d916800b166d162d165d16970e1c3870e1c3870e875058f858b8dc6e2eb0783c0b036001ac0000005a2d168b5543a1d916800701168b45a5c183060c18306835062e171f97c5d607038000000000005162d459745a2c38b0e1c3870e1c3870e1c3870e1d4060c183060c183060c18306a0d4183163e858ba170b8bac1e0f0381c0b016006b00000000 24 16777215 10 1023
def hc_63_10 : Nat → Nat := unpackHintV5 0xc80145c3113cbfa8dab9798cae7ebfa93d50a191eb9a01e492edc58be5c2857d9a809939755ecf74e81d7450266ed55f6a1530627de65d514b5631c84eb5df41bb3f3cfd2f32a2972d814824ca2e1f89501bb8f41495c90e4993048671000121 0x7cd9f167c59f36aaa0007c39f0e4c99355aaa00051aa00110000000e6b00001553e83555555555500266c98b262c99355500056bd9ab264c987264c3aad5500028d50008008130000855555555555500545aaaaaab56aaa1d56a96555b5d52b0414110221555555555554519161c387543872e5d543870e1c3870ea1c387aaaaa96aaaaaa160b0b88cc98332601c0e440b45aaa2c1a8b06a1d0ecc88b116eb5162d5165c5870e1c38750e1c3870e1c3870e1c5870e1c5870e1cbaa870e1c587161c3870e1c5870e1c387aaaa5aaaaaad707a83c2c16171058b016bc0381c0e1c03b3088168b5545835160d43a1d0e0d43835991160b161c3870e1c3aaaaaaaaad070e1c3aac3e5555aa556a0f33260cc980b058881c0e442aaaaaaaaaaa8a28b555516eb43aaa1c3870e1d5543aaaaa870e1c5870e1c5870eaaab52c3d556aa956ad707a83caf050160b110381c0e1c03bf0885555555555555555140e1c39b162cd9b4d97369b2f070e1c387aa0e1e83870e1eaaaaaaaaaa8d82c364c0d93066430381c88162c58b360c5a6c18b538b4e2c3870e1ea8169c56cdfab0e1c3870e1c387264c98b262c99b264c9a4d265e8002aaa8a83c0140000007000380109d1a7469d1a7461c3870e4c193498326d5002b561c3870e1c3870e1c3870e2c3870e5c3a1d0e1eaaaaaab5c1ea0f2b000e07038700e1109d3a74e9d3a74e1c3870e1c18743830ed509d388b9162c587161cba87162d45a2c58f1eaa5cb870f555552d5555542c16171038cc664c1993088168b5543a2d160d458359911602130058b162c7a971e3c7931e4c78f1e4c7c73e1c987aaa0f07ab582c982c1e1300001a0d0683516eb5162d5165c58b162c58b162c58b163c78f551e5c58b162c58b1e2c58f1e2c58b162c38b0e5d438b161c38b3e1c3d5552d555507a0f556b160b0b882c580b01e03c7807199443c168b5545835160d45835160d43a2d991166b10f04f5b341ea4c55516eb161c58755162c58b162c58b55555a55aa5583cd41e5555160b11038cc2604c28878aaaaaaaaaaaa282c0401e3c7931efc78f1e4c793162c58b55261cf87a1f0faa83c1ead680b11e13000380aaaa8a2d55545bad478f555551e2c58b162c58b16aaaa9f55438b0e2c3aad4b0f555aaa5583d07aab5a0a02c16220f01e3c038cca21e2aaaaaaaaaaaaaaa8a0b2e2cba87162c38b3e1c7aa97162cd87aa5aaaaaaa8b882c16071986c36442a8b45a1d168b45b3222c362c59b366cd871707861c78f1e6cb9b4da6cb870f555555555555546c1610c0e06c981b261102c58b170c5c3161c5a70e6c18b4d8316d502c162c58b165c38b0e1c3eb0fac38b166cd9b366c387b5d5af5d555556bad7542c161f0f81f581f586c36440b162c58b162c5870e1c38b162c5d502c581c387168b162d165c58b162c58b1e3eaaaaa858b162c58ba162c78f1e3d1e8f2e1c5870e2c3870e1c3eb0e1c3873e1ea85c3eaaaaaaaa0f41eaad62cf80b1602c161f0f83cf80f1e01c381cf9443c160c5a2c18b458b162c58b162c583168b062d0e1c387aa058b0b97362cb8b165cb970e1c38743eb43a8f1e5d4bd551736fea0f555555170f84c260341a0d06a5d2e5d597165c5972e1c3871e3c78b1e2c7d28f547971e5eaa6556a83870e1d43eb50e1d5aaaa5aaaa1f0fa83d07aab59f0f85c42e5c0b9f01e7c078f00e07288787d3eaa9706a5c1a8f06a3c1a8743b3227c5555551e3c78b1e2c7c3555555550e1c3875555aaa955560f41eaad67c3e22220f3e03c7807039443c545aaad5551e3c78b1e2c7c351e3d555569555547970e1c3873e1d43aaa87d75552c3d5569560f41eaad67c3e27c1411079f01e3c0387039f28878aaaaaaa9d55555555554505bad16a5c58b162c5975262c58b164c98b267c58b162c39f0f0155002c26000b0983c0990341a0d0682d16aa2dd6933eaaa93262c58b16aa7d43c030f56a01098002c41e04c9555455ab266c98b262c993265c9a4d264cf873e1cf873e1e8002aaaa80028826001300078004c008567d79f5e7d79f260c9a4c193439f3e1ea80098ad58f1e3c58f163c78f1e8f4797561c3870f5555541e83d55ad5800f01e3c038510f15a74e9d38f063d1e0c7a1d3a70f5427004d8972e9349a93264c980282a93264cd8b166c993271c9b3264cba972e5cb872f0cb87370b8993a26ae8bac5c7d171f4ae5701ac1600b0000000000005a2d264d49b75552e0d4b8355eaf655a002cd8b365c9970e1c39f26fc993260aaa2a4c9877e4cf9f0ea3e1f1395c001ac582c05555 24 16777215 10 1023
def hc_63_11 : Nat → Nat := unpackHintV5 0xc1fddbbbcd8cb6c542af65d8a31f129bc5d696cd3e9308f18c49b08595ad7ee1ad79256f7291a56df527626ee25bc9a9568d4f4b22db44f58b3fd1493a4563347d722f1d5829b55a24d93720b5091c19271489e40f89400c14dd04cdd2000133 0x2a5545a2d5516aa2d516aaaaaaa8b3e1c38b161c38b0e2c3a975550fae1742eaad6caacab542c058b0160b1050440e33221555555555545aaaaaa8a070f5548b45a8b16a5cb870e1c3870e1d0e1d43ad5555552d542c1637260dc981710381c88168b45835160d5543a1d99116522d2e1c3870e2c993162c58b162c593762c58b164c040170bab5d5000b0580b260703840d068341b522d458b5162cb9745a2c3870e1c3870e1c3870e1c3ac0c183060c183060c183060d41a83070ba17556b96aaaa16bc058b0160b0b881c0e0301911522d458b5162cb9745a2c3870e1c3870e1c3870e1c387550fac38b0e1c3870e1c587161c3870e1c587561c387161c5870e1cb87561742eaad72d555550787d0b5e02c580b0585c40e07038700e1102c1a8b06a2d16aa8743a1c1a1d161c3835991160b160007d3e5cfa7cb8b162c593264c587161cf873e1e80028aaaa8160b000000000e6b0000059f060c5a2c18b16a2c58b162c58b161c58b0f540100974993264c9972e4cbbf264c98b162c5870e4c39f0e87d687580aa1602c00984c0e10341a0d06c02a4d8ea9349a2d16aaa4c39f0e97543eb80961602d098001c25555eaa2e80009a4cb934993162c58b264c987264c38b162c5af5f40014555540b00058001300008160c5a2c18b458b162c58b162c58b162ea802a168b162d165c58b162c58b0e2c58b0e2c58b170ba17556baaaa1602c580b05801102c18b4583168b162c58b162c58b162c5d502c583c7870e2c38f1e8b4ba972ea5cb9b361c587366cd9b2eaa1eaaaaaa5aa8d82c3e4c0f9302e2070f9102d169f06a7c1aaa874fb3227c1e3c7a2cba5cbad2d1b162cd9b366c39b361cba97aaa5a9a96aa360b0d930364c0b881102d169b06a6c1aaaacc882c58b162c58b168b45ad2d0783870e1c3870e1c3870ea1eaa696a5aa8582c9e4c279302e207039102d168b06a2c1aaa8743b3222c162c58ba0e1c3870161352e3c78f1e4dd8f264c78f1e1c01736b65aa0580070380d068341a8b458b162c58b162c5d41c587d61c3870e1d43870e1c3870e1c387161c397550e1c38f0e3c3870e1c38f0e1c3870e1c38785d52dad695aaaaa83c3e8582c2e20f1e03d78070381c3807088168b5545835160d43a1d0e0d43835991160b161c38b0e2c5a2d16b4b42c3c1d59b0e1c78f0e1cba87aa5a9a99aaa160b19930664c0b881c66440b45a2c1a8b06aaa1d16cc88b03809749931e4c78f1e4c79f1e3c78b162c5d13007873e1ea85cdad94580b26000f098138068341a0d05870e1d458b5165d168b162c78b162c58b162c58b163c78b162c58b162c5d42c5ab162c3870e2c3eb2ea1c78f0e1c79f0e1e170faaaa85d52dad695aa1602c580b0585c41e3c07807199102c1a8b06a2d16aa8b06a2c1a8745b3222c3e6e78b3e2d59b4ba5d6968f873e1c78f1e5cba872f5534b52d554ac0f9303e4c0b881c3e442b53e0d4f835550e9f6644f81c3a2d2e2c993162c58b162c593c62c58b17002d58b0e2c3eb3e1c987aa041613000983c2068341a0d4ba5cf9b3e2cf8b3e6cb970003e1cf872ea1c99327542c01415400000000000007d3eaa9f06a7c1a874fb3200974b93264c593164cdd0002b5eacba97264c393264c3d50b0028550004c001e000042b57aaa4c1a9306abd5ecc8025d2e3c78b1e2c78fa95ab2ea5c78f1e1c78f0f0faa5b5ad2b54ac0b883c780f008856aaa3c1a8f06ab3222aa870e1d5555554d9b0e1d0e6c3eb55366cdd52ad555551b058887c981f2601cf87cf910aaaaaaaaaaaa28aaaaaaaa9b162cd9b55366cd87366c3d552aad555551b058886c981b2603322155555555555451555438743870eaaa1cd870e1c3aaad555555221b0d81c0e0703910aaaaaaaaaa28aaa2c5aaaaaa874387555550e1ea9556aaaaa8582c44664c199300e07221555555555554515168b545aaaa87161f5870e1c3a1d550eaa1c58750eaaaaa1c3aaaa870e1ea96555b5d555550b058af050440e07038700efc221555555555555555451554387555555161c3a1c3aaab36aab54aaadaeaaaaa8582c44664c199300e3322155555555555450380a934faa4d268b45aaa9300fa87aa656d62c05a130010270aaaa21c3875545a2d5516aa2d516aaaaaaa8b16ac58b0e1c38b0fad3eaa8755aaaaaa59556d7542c058b0160b1660a0881c66442aaaaaaaaaaaaaaa8a2aab367c5bf167cdaaaa9f0e7c3aaaab54ab5555554ac110f9303e4c0387c8855555555555514 24 16777215 10 1023
def hc_63_12 : Nat → Nat := unpackHintV5 0xbbf5a3b49dd6ae4995a975359e8eba999d3c95a0ff8e01e889014084891e7f7d4377cdec71559e6c294b6501ca593af252ada34dfd2c4a4cec438db03d419335bde12f559a2a5d3e1f9ab11a85451698fb0ef5e90eac1209655204fd1a00013f 0x4ba5c3870e1c387550fac3870e1c5870e1cb87568bac1e0f070f41c7d01710381c0e1c038409d4eaa8743a1c1a1d0e1c1aca745381c3d55334f973eb32e6c58b363c78f366c3c1cd9f0e7c3d55555555551f2607c981b058cc0387c883e0c5a7c18b458b162d98b161c59f0f540b3e0b17554a1c3a8f0e8b4b8f438750e1cd87161e50f5555550f5aaa6e4c1b930360b0b881c66443706adc1a8b45aaa1d4ecc8b7292e8f262c59b1e3c78f267c793263c78f0e00f0e7c38256b170b87d54004c2604c1a0d0683427522d2ea3cba8f1e5cd8b162c5972e3c78f1e3c7972e3c7971e3c78f0e1c39b0e2c38f1e1c38f3e1c3a87d6a1c3ab56b85d42e87ad5555551b0583c780f02e2172e05c038cc88168b478351e0d554b8352e0d43a9d9916e2d2aaaaaaa870e1c3870e1c3870e1c3aaaad2b52ad533260cc981b058881c0e442aaaaaaaaaaa8a52a870e1c393162cd8f1e3c793763c9931e3c7820702b58b85cb540021c45555a95555543870e1c3870e1c3870e1d43eb554daa2d51e8f5547aaaaa1dab5c2ea172aad52ad2c3d4d82c1e3c07af0440e0714108855555555555555551455555a5555361c587552e5c3871e3c3876aa55a555aa360b1121930864c038cc8855555555555514a362c5931e3c78f264c7933e3c78f55401e1cf8726056b170baa9498003c262084e15556a55555555555555361c5871e3c3871e7c3875555ab5c2ea172aaaad51b0583c780f5e088881c664454a8b54daaa3d5547a3d5555555361c5871e3c3871e7c38752eaaa1f5d5ae1750b961eaab4aab546c160f1e03c1050440e33221555555555545aaaaaa8a070f554a5cba8f1e8b4b870ea1c38743870e1c3ad5555542e87ad5537260dc981b0585c40e0722138354e0d45a2d550e8766453949747870e1c393162cd8f1e3c793763c9931e3c7930102b58b85c3eaa05800f0984c0e07081a0d06836a45a5d479751e3c3870e1c3870e1c3870e1c3ac0c183060c183060c183060d41a830756b85d42e87ad55551b0583c780f5e05c40e070180c88a9169751e5d478f0e1c3870e1c3870e1c3870e1d543eb0e6c39b0e1c38b0e2c3870e3c38f0e1c3870e3c3870e1c3872e1d5ab5c2ea1743d6aaaaaa8d82c1e3c07af02e2070381c3807088168b478351e0d5543a1d0e0d0e8b0e1c1acc8a70d9b000362c59b3e9f2e7d3e5cd87161c993267c39f0e5401415555400000000000002c58b167c18b4f83169f167c587167c3d5004024d2e6c58b2e4cbbf264c993264c9972e1c39f0e4c3a1f5a1d422a8983c002068341a0d09c022d36a9349aa4dc6aaa7c3930e97543eb0896260f1098004aaabd5458d0001b162cd93499326932e6c58b364c987264c9875ebca80282aaa826000f0000002058b162c9831693062d5e2d78b5e2d78baa0026546c58b363d1e5c7a3c79b162cd8f1e3c38f1e1ead70ba85d0faaaa360b078f01e001102c58b163c18b4783168b162c5d502c0e1eaa858b162cfaccbb34f97838b162c38b162cf873e1eaaaaaaaaaa8582c3e4c0f9306601c0f8440b162c58b062d160c5a2c58b161c58b0f540b160b175548b45a8b0ea1c38b0e2c3a870e2d0e1e43a1c3d555554b550b058dc98372605c40e332205a2d160d45835550e8b66445948b4b8b264c58b162c58b164cf8b162c58700f87161c105c2ead7542c26001309813068341a0d05d4a2c5a8b2e8b458b165c58b162c58b162c58b2e5c58b162c58b162c3870e2cf870e2c5870e2c38b0ea1f5a870eac2e85d55ae5aaaaaa8580b1602c161710b9702e01c66440b06a2c1a8b45aaa2c1a8b06a1d16cc88b169555555543870e1c3870e1c3870e1d5617354aaaab542c1633260cc98220703910aaaaaaaaaaaa294aa1c3870e2c993162c58b162c593762c58b16081c0170bab5d500087115556a555545a5d543870e1c3870e1c3870e1d43eb5545aaa8b45aaa2d516aaa1d85d0baab5aad52b328b5e02c580b058881c0e282110aaaaaaaaaaaaaaaa286b09aaad2aaaaa8b0e2c3aaa1cb970e1c58b0e1e174d5ad569556a8582c442619c980719910aaaaaaaaaaaa2942c99f162c58b162c593262c58b16aa807c38b0e4c0170bab5d50b098002c4109c2aaad4aaaaaaaaaaaaaa2cf870e2c5870e2c38b0eaaab0ba17556b5555aa16bc058b0160b1111038cc88 24 16777215 10 1023
def hc_63_13 : Nat → Nat := unpackHintV5 0xcbbb04c485cdbd11ddb4fe05ad4deca5c5e29d0a2f950dff8cc213857dd178db297255a165ef1a5fb18f5a3d5d5479714f8d3b4b90ff45e56b3ce24136fd792d965a28754822d9671d3d671b547a1870b914d4e70d05f406a59803c0b90000f0 0x1835060c1870e1c3aaa2d16a0c1a832ea6dba9b361c587d62c5870e0c583060c1a8b162cfa87170b818fa060e8d9ba36ae95ac1e3f0b0580cf8030606cd81b3e07c40e1f20f80c1a0d160c183060c183545a2d06a8b068b060d9160c1a22c18303870e6c58b366d2e9b2e1c587d62c5870e2c58b0e1cdc2e363e958fa572b83cae360b0d8000708560b162c59b062d062d162c38b4e1e16ae0582c58b161c0e1c3870e1c0058b0264c9a4d265c387000170ba7f0783c4c7d131f4002c00038001c00162c58b162c58b0e1c387160c5a2c18b6162e00162c58b0e2c3eb0e1c3870e1c3870e2c3872e1d0e870e1c387170ba83c1e0e1e838fa160b00381c0e1c038402c58b162c58b161c3870e1c18743830ec2c5c0b16070e0004d265c9a4c98b162c593260002c381cf873e1c98fa263e85c2ea0f1f816000b02600004c200160c5a2c18b458b162c58b162c38b161e162e0016070e1c5a2c58b4597162c58b162c58b0e1c38b0fac387163e858ba170ba83d0b0162c0582c00e100b062d160c5a2c58b162c58b161c58b0f0b1702c581c387162c58b369b2e6d365c3870fac38b0e1c38b0e1c3870e2e171b1f46c7d2b95c1e0f0b0586c981b260cc86070390ac162c58b160c5a2c18b458b162c3870e1e162e058b0d8b166c3870e070e1c393260004c99349a4cb870e0006e172b95c1e0f131f44c7d04c0000980700038004c162c58b4e2d38b0e1c387260c5a4c18b6169e00261b162cd870e1c387161f5870e1c3870e1cb8743a1c3870e1cdc2e572b83c1e0e1e838fa360b00381c0e1c03842b058b162d38b4e2c3870e1c3830e87061d85a78169c2e5cba2cba5cba970ea1c39b361c58750e1cda1c39750e6e171b1f46c7d17583cae360b0d930364c0b881c7e42b05a2d360d4d835550ea7655a2070e1d169752e5cb974fa972e5cd97362c58b165c5972eaa2c58b165c5a972e5cb870e1c3870fac38b0e1c38b0ea1f5a870ea9b85c6c7d1f1f45d62e3e8b8fa0f078d82c367c0f9f02e2172e05cf80700e107c168b4d8353e0d554b8352e0d43a87593e89f058b368b168b2e874387161dd61c3870fac3eb0eeb7587170b8dc6e2eb0783c2c161b0d85c40e0720f82d168b45aaa1d0ec8b44581c38745a8b16a2c5972e8b458b16a2c58b16aa2c5972e2c597162c58b162c58b0e1c387161c38b0e1c3870fad43eb50e1d5163e858ba170b8bac5c7d171f41e0f0b3e02c580b0585c42e5c0b9f00e0720f82c1a8b06a2d16aa8b06a2c1a8743b22d11625d2e4c993164c593361c38001f0e7c38a1c01428bac4c7d131f41e3f0004c002600130017abd55260d498350e9f657a004c4ba5cb97165c5972e1c3870e1d43eb50e1d5a2eb171f45c7d07a02e2172e05c03840aaa5c1a9706a1d4eca22aaaaaaaa1c3870e1c3870e1c3870e1c3aa9b85c6c7d1b1f4aa1e0f1b0586c981b260881c0e42b155555555555451543870e1d14993262c98b266c0140387000a550f07898fa263e8000100e002002aaaaaaaaaaa802a870e1c3a87d6aaaa2d5543b4aa1e0f2b23d4110381c5042055555555555514555555554d9b0e2c3aa972e1c39b2e1c39ba174aa6c7d1b1f41e571b0160886c981b2601c2158aaaaaaaaaaaa281c387545a2d5369b5545a2d552e975554fa5d55550e1c3eb0e2c3870e2c3a875550facdc2e363e8f8fa47aab2a8783c6c161b3e07cf827c14110381c83e2aaaaaaaaaa8b55555514555162cdaa87161dd6aeb0fac38743eb0fac5d0ba55371b83eb83eb8580b044361b03eb03eb20f8aaaaaaeb5d6aa8a070e1d55168b5545a5d5168b545aaaaa8b4baaaa1c5870e2c3870e1c3eb50eaaa1c38b1f42c5d0b85c8f556550e1e0e7e167c058b0160b13e0a0881c381cf907c5555555555516aaaaaaa284cd93164c59326aaa0007c39f0e4c980028d131f44c7d2a878fc1300100100098400aaaaaaaaaaaa001c387555555555555550e1c3eb0e2c3870e2c3aaaa9b85c6c7d1f1f4aaaa1e0f1b0586cf81f3e088881c0e41f03870eaaaaaaaaaaaaaa1c5870e2c3870e1c3eb5555163e858ba170b955543c1e167c058b0160b11110381c83e2aaaaa870eaaab4aaaa1e8111103840aa2c38b0eaa2e172a8793c2c16220711908c5555555514545aaaaa870ea5d5543eba47aab2a87a04141103840aaaaaaaaaaaaa281c38745974b9752e5d4b970e1c3870e1c3870e870ea1d439b370b571b1f46c7d17583c1e366c161b2606c981710381c8560b45a6c1a9b06aaa1d0eca74538974b870e1c38750993262c98b266c9930005000a2eb0783c4c7d131f4004c098001c000e001313a9d550e8749835260d653a00aa1c3870eaa2e172a8783c2c16220703908c55555555144ba5c3870e1c3a87060c18306a0d4183a2eb0783c0e0701710381c060320 24 16777215 10 1023
def hc_63_14 : Nat → Nat := unpackHintV5 0x809d717b99417691427241146ae1d864e1805ec98658759552ad724fb0bf4a754f455548414105398ded33c5722d25a826d1951b6ada13360d0792e90001e4 0x2e5c387161cd97555555366c38b0e6d5555370b958fa3e3e9543c7e360b0f9303e4c110387c8562aaaaaaaaaaa8a1b360002a00a06c38b0e4c993555370b8f8fa3e3e9543c7e0000000000000555554fa0d5555555400993000150050362c59b264c393264c3aa9b85c4c7d131f4aaae5704c0040040000555555555555004ba8b75aaaa6c58b36a875554dc2e5647aaaab95c6c1628208810ac5555555555551445a2c58716a870e5cbaa972e2c38b162c3972ea1cb8b162c5c2e2eb331f47c7d078fc2c161710f9303e4c0387c805a2d55160d458350e8b645a22c445800b1605cb8000b161c587165d4393264c5c2e2eb1f1f47c7d078fc00000000000002d16aa8b06a2c1a8745b22d00445802813260002c58b165d4b93261c993261c5c2e2eb131f44c7d2fa001604c001600000b45aaa2c1a8b06a2d16c8b40116eb5162d5165c58b162c59752e2c58b0e2c587170b8bac2c5d0b1f542c16171058b0160100b45aaa2c1a8b06a2d16c8b44582c5870e2c58b0eaaaaaaa8b0e2c58b0eaaa7c7d331f42e172a878fc7c981f2602c16220703e102aaaaaaaaaaaa8a0b858b55551e3c78f162c58b551e0f0582c4405555555514162c001400144993262c38b0eaa7c7d1f1f42e172a878fc22000000001cd6000027d06aaaaaaaaaaaa002c580028002893264c393261c58b162d5498fa263e85c2e555f42000b0010260000aaaaaaaaaaaa080a2d55545bad55438b162c5aaa8f555a170b9569050160b110205555555555551445a5d4387161cda2c5aa97166cd87161cd972ea1cb972e5cdc2e2eb2b1f47c7d07571f571b0585c43e4c0f9300e1f21582d16aa9f06a7c1a874fb2ad13e22d0d9b0002e5c000d87161cba87264c99b85c5d63e3e8f8fa0f1f800000000000005a2d553e0d4f8350e9f64fa008b45000162c000d8b166cba97264c393264c39b85c5d6263e898fa572b826001300098004c00260b45aaa4c1a9306abd5ecab40098a2c5a2dd6a8b162cd8b166cba972e5cb872e5c39b85c5d62e3e8b8fa572b8d82c2e2172e05c021582d16aa9706a5c1aacab440e1c3a6c5a5cba6d36a5cb972e5c38b16a1c3aa972e5c38b0fac58b0e1c58b165cba9f0e2c5a97161c39b85c6cdd1b5745d62e3e8b8fa0f1f8d82c366c0dd702e2172e05e18070f90ac168b4d9b536dd554b8352e0d43a7d95689f116aa8752e5c3870eaaaa6d555369b45aaa1c38b0fac58b0e1c58b169f5547aab1b85c6cdd1b574aa1e3f2cc140d82c366c0dd70440e1f2158aaaaaaaaaaaaaaaa281c3800070e1c00d8b166cfa4cb934f97366cdd7375cd9b0e2c3eb162c38700162c058b167c39f0e6e171f1f44c7d1b3746d5d2b95c1e3f06c003606c2600000007c00162c58b3e0c5a4c18b4d9b162cd9f162cf8b3e2c38b3e1e167e000e1c000d8b166c9a4c9934997038b0e002c581f0e7c39b85c4c7d131f4ae57078fc130009800004c00162c58b260c5a4c18b578b5e2c38b3e1e16ae00 24 16777215 10 1023
def nh_63 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_63_14 (Nat.sub p 448)) (hc_63_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (hc_63_12 (Nat.sub p 384)) (hc_63_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Bool.rec (Bool.rec (hc_63_10 (Nat.sub p 320)) (hc_63_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (hc_63_8 (Nat.sub p 256)) (hc_63_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 288)) (Nat.blt p 352)) (Bool.rec (Bool.rec (Bool.rec (hc_63_6 (Nat.sub p 192)) (hc_63_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (hc_63_4 (Nat.sub p 128)) (hc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (hc_63_2 (Nat.sub p 64)) (hc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_63_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def f_63 : Nat → Nat × Nat := unpackForestF 0xe8b55e935de895500c5fe6b45e734de694500c5be436de426ce4b65e416d00c57e2345e2b4de214500c53df45bdf457df157df155df05700b5fde13500b5bdd16d00b57dbb6edb93500b53d8c6ed8b6fd9c6cd8b67d894500b4fd736ed713500b4bd2562d236fd5560d2367d215dd325fd3257d205cd205000b47cfb6ecf935cf838cf83400b43c5b55cdc64cd945c5b4fcc364cc135c5b4bca568ca15dca05cc5b47c8364c8135c8034c5b43c635dc634fc6347c595500a5fbb36dc3c7cc3945bb34fc237cc2135bb34bc114fbfd70bf95dbf85cbb347bdb7cbd935bd834bb343bbb65bbb4fbbb47bb16d00a57ba355b4c6eb8b54b8935b4b6bb747cb717db4b67b4b45b5367b534db494500a4fb3b45aed62b2670b236caeb6bb0d70b097daeb67aeb5daf355ae95d00a47adb54ab56bacb7cab567ab36eab13500a3fa9c58a9955a156ba813fa8137a7470a717da1567a6569a1462a5460a1367a4472a135fa306ca1357a1d6ba1d67a114d00a379845b9fb7d984579835b98357983559d4649834f9c3649834b9ad689a85c98347993649903498343980570095f86b6d9647c9637c86b4f9537c86b4b93a4f93a4792d709285c86b478fc7c8fb7c8fb6c9036c8f83486b438e47c8e34586a4f8cd708cb5d86a478bb7c86a3f87b5f8a46c87b5b87b5788b5c8846487b538747086a370095785b557a46e84c647a36f83b547a36b82c7c7a36781b547a3638005e800527a3457ec647eb457a26f7d47c7d3457a2677c3547a23f7ac727ac587a2370094f793456a562785686a36f76e7076b6c6a36b7524f7524774d706a36773b6c6a3637236e723626a35d70568703657035d6a26f6eb4f6eb436d5706d37d6d35d6a2676c36c6a23f6b36b6ac606a23700947693645f56f683545f56b66b7c66a7c5f56765454653545f5635f36e63b645f26f62b7c5f2676157e613545f25f5fe725fb6c5f2570093f5e4684ad6f5d4584ad6b5bc705ba7c4ad675a4585a3544ad63593554ac6e4ac6b4ac63575694ac624ac5b5537e550344ac534ab6f53c604ab674ab5f51e725186c4ab5750c684aa6f4fc704aa674e57e4e4584aa5f4d4604aa574aa4f4bd724aa374a84f0093749455493583cd6b47c7d47b703cd6746b483cc6b45b703cc6744b583cc5f43b483cc5b423604206c3cc5740b48408443cc533dc5f3ea443e8443dc533da463cb623cb4a009273ab4f3a94f3a9370085f0085b2eb6d3847c3837c2eb4f36c7c36b452ea4f35c702ea37333553334f3324f332372e96d3247c2e94f3047030d8c3025f2e9372f3702e92700857008532ab6f2aa6f2aa372a96f2a9372a9270084f0084b293451cd62285681cb6f2736e1cb5d25568253652535d1ca6f244601ca37235681c96f20b6f20b4520a6f20a371c95d1e6721e4601ec601e27f1c9371d3601c92700847008431ac541ab54105631036e193641026f17d7e17b541025f16b641016f14c5414b7e14b541015f125631226f12d7e1225f1013510b7210b48101270083f0083b0eb5409d6309a6f0d57e09a5f0996f0b57e0b3540995f0a3720992700837008330082b06c5f0695f06947008270081b015630146f0457e0145f0136f02d7e0135f01d7201347008170003f 9 11
def ch_63 : Nat → Bool := dagCheckNodeV5 fullMask g_63 ep_63 5 31 bds_63 468 (dagTraceF fullMask rootStock 11 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 fullMask g_63 ep_63 5 31 468 bds_63 (dagTraceF fullMask rootStock 11 f_63) (cur_63 0) (nh_63 0) rootStock 11 = true := by decide +kernel
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
theorem nb_63_14 : treeBlockF 448 468 ch_63 = true := by decide +kernel
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
theorem nj_63_14 : ∀ i, 0 ≤ i → i < 468 → ch_63 i = true := block_join nj_63_13 (fun _ h1 h2 => treeBlockF_at nb_63_14 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 468 → ch_63 i = true := nj_63_14
theorem lb_63 : LowerBin fullMask rootStock g_63 12 :=
  lowerDagV5 (kn_cons lb_61 (kn_cons lb_28 (kn_cons lb_56 (kn_cons lb_60 (kn_cons lb_57 (kn_cons lb_32 (kn_cons lb_59 (kn_cons lb_62 (kn_cons lb_58 (kn_cons lb_55 (kn_cons lb_1 (kn_cons lb_24 (kn_cons lb_26 (kn_cons lb_29 (kn_cons lb_15 (kn_cons lb_14 (kn_cons lb_11 (kn_cons lb_49 (kn_cons lb_16 (kn_cons lb_8 (kn_cons lb_12 (kn_cons lb_23 (kn_cons lb_48 (kn_cons lb_7 (kn_cons lb_30 (kn_cons lb_20 (kn_cons lb_4 (kn_cons lb_47 (kn_cons lb_54 (kn_nil)))))))))))))))))))))))))))))) rc_63 nc_63 (by decide +kernel)

def wg : List Gate := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3939033216)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3939033216) = g_63 by decide]
  exact lb_63

end PEqualNP.Outside.L_meta_48593

theorem PEqualNP.Outside.L_meta_48593 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48593.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3939033216) 13 PEqualNP.Outside.L_meta_48593.root_lb PEqualNP.Outside.L_meta_48593.wg 18 rfl PEqualNP.Outside.L_meta_48593.wfits PEqualNP.Outside.L_meta_48593.weval
