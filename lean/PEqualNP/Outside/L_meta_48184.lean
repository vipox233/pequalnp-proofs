import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48184

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

def m_0 : Nat := 0xcccc00000000
def s_0 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_0 : Nat := 0x44c00000000
def ep_0 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
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

def m_1 : Nat := 0xcc00cc00
def s_1 : List Nat := [0x44004400, 0xc000c00, 0xcc00]
def g_1 : Nat := 0x4004c00
def ep_1 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000
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

def m_2 : Nat := 0xcccc0000
def s_2 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_2 : Nat := 0x44c0000
def ep_2 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_3 : Nat := 0xc0c0c0c00000000
def s_3 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_3 : Nat := 0x4040c00000000
def ep_3 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_4 : Nat := 0x4444444400000000
def s_4 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_4 : Nat := 0x4044400000000
def ep_4 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_5 : Nat := 0xcc00cc00000000
def s_5 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_5 : Nat := 0x4004c00000000
def ep_5 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_6 : Nat := 0xc000c000c000c00
def s_6 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_6 : Nat := 0x40004000c00
def ep_6 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_7 : Nat := 0x222200002222
def s_7 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_7 : Nat := 0x200000222
def ep_7 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_8 : Nat := 0x808080808080808
def s_8 : List Nat := [0x8000800080008, 0x80800000808, 0x8080808]
def g_8 : Nat := 0x800080808
def ep_8 : Nat := 0x8080000000008000008000000000800080000000000000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x4040404040404040
def s_9 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_9 : Nat := 0x4000404040
def ep_9 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_10 : Nat := 0xff000000000000
def s_10 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_10 : Nat := 0x17000000000000
def ep_10 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_11 : Nat := 0x4400440044004400
def s_11 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_11 : Nat := 0x40004004400
def ep_11 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_12 : Nat := 0xf0f000000000000
def s_12 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_12 : Nat := 0x107000000000000
def ep_12 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_13 : Nat := 0xcc000000cc0000
def s_13 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_13 : Nat := 0x40000004c0000
def ep_13 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_14 : Nat := 0x22222222
def s_14 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_14 : Nat := 0x20222
def ep_14 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_15 : Nat := 0xcc000000cc00
def s_15 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_15 : Nat := 0x40000004c00
def ep_15 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
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

def m_16 : Nat := 0x4444000044440000
def s_16 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_16 : Nat := 0x4000004440000
def ep_16 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_17 : Nat := 0xc0c00000c0c0000
def s_17 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_17 : Nat := 0x40000040c0000
def ep_17 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_18 : Nat := 0xaaaa00000000aaaa
def s_18 : List Nat := [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa]
def g_18 : Nat := 0x2000000000a2a
def ep_18 : Nat := 0x20000000000200002000000000a0800020000000000200000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb1e54b327d13969924c4a6000f 7 127 3 7 10 1023 13 8191
def nh_18 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x33eb2c33933233133000f 3 9
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 7 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 7 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 7 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 7 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xf00f0000f00f0
def s_19 : List Nat := [0x5005000050050, 0x3003000030030, 0xf0000000f0, 0xf00f0]
def g_19 : Nat := 0x70050000f0070
def ep_19 : Nat := 0x8002000000000000000000000000000000000000000000000000000020000000000200004005000000040
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_19 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 10 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 10 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 10 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 10 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xa0aa0a00a0aa0a0
def s_20 : List Nat := [0x202202002022020, 0xa0a00000a0a0, 0xa00a0000a00a0, 0xa0aa0a0]
def g_20 : Nat := 0x20000000a0020
def ep_20 : Nat := 0x80020000000000000000000020000000a0020000000000000000000020000000000200000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1e302080e3024b263988c592e548902e108800f 7 127 3 7 10 1023 14 16383
def nh_20 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0xc72631f1814b8a4442e51824b084400f 3 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 10 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 10 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 10 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 10 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xf000f00f000f0
def s_21 : List Nat := [0x5000500500050, 0x3000300300030, 0xf000f0, 0xf000000f0]
def g_21 : Nat := 0x7000f00500070
def ep_21 : Nat := 0x8000000200000000000000000000000000000000000020000000000200004000000500040
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a192430a123434d263a88d9d3a54d883a10d800f 7 127 3 7 10 1023 14 16383
def nh_21 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6ce3469a10e886c00f 3 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 10 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 10 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 10 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 10 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff00000000
def s_22 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_22 : Nat := 0x155f00000000
def ep_22 : Nat := 0x4a000000000000040a0000000000001000000000000000155000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xaa00aa00aa00aa
def s_23 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_23 : Nat := 0x2000a000a002a
def ep_23 : Nat := 0x80020000000080000002000000000000000000002000a000a000800020000000000200000000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_23_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_23_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_23 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_23_2 (Nat.sub p 64)) (hc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
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

def m_24 : Nat := 0xffff000000000000
def s_24 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_24 : Nat := 0x1117000000000000
def ep_24 : Nat := 0x6000000000000000600000000000011120000000000001114000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xcccccccc00000000
def s_25 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_25 : Nat := 0x4044c00000000
def ep_25 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_0, s_0, 4, g_0), (m_4, s_4, 4, g_4), (m_3, s_3, 4, g_3)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_25 : Nat → Nat := fun p => Bool.rec (hc_25_1 (Nat.sub p 32)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_0 (kn_cons lb_4 (kn_cons lb_3 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcccc0000cccc0000
def s_26 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_26 : Nat := 0x40000044c0000
def ep_26 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_2, s_2, 4, g_2), (m_16, s_16, 4, g_16), (m_17, s_17, 4, g_17)]
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
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_2 (kn_cons lb_16 (kn_cons lb_17 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xff000000ff00
def s_27 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_27 : Nat := 0x150000005f00
def ep_27 : Nat := 0x4a00000000000000000000000000000000000000040000000a0000001000000000000000150000005000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xf0f00000f0f0
def s_28 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_28 : Nat := 0x105000005070
def ep_28 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_28_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_28_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_28 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_28_2 (Nat.sub p 64)) (hc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 64 (dagTraceF m_28 s_28 5 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 64 bds_28 (dagTraceF m_28 s_28 5 f_28) (cur_28 0) (nh_28 0) s_28 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 64 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 64 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 64 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 6 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xcccc0000cccc
def s_29 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_29 : Nat := 0x44c00004c4c
def ep_29 : Nat := 0x480000000000000000000000004800000000000004080000080800000000000000000000044000004040
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x333300003333
def s_30 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_30 : Nat := 0x111300001333
def ep_30 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xaaaa0000aaaa
def s_31 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_31 : Nat := 0xa00000a2a
def ep_31 : Nat := 0xa2000000000000000000000000a000000200000000a00000a0800000000000000200000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcc00cc00cc00cc00
def s_32 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_32 : Nat := 0x40004004c00
def ep_32 : Nat := 0x400480000000400000048000000000000000000000004000400080000000000000000000000040004004000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_1, s_1, 4, g_1), (m_11, s_11, 4, g_11), (m_6, s_6, 4, g_6)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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
  lowerDagV5 (kn_cons lb_15 (kn_cons lb_1 (kn_cons lb_11 (kn_cons lb_6 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xcccccccc
def s_33 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_33 : Nat := 0x44c4c4c
def ep_33 : Nat := 0x48000000000000480000000000000408080800000000000000000000000004404040
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555555500000000
def s_34 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_34 : Nat := 0x1115155500000000
def ep_34 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xffff0000
def s_35 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_35 : Nat := 0x155f0000
def ep_35 : Nat := 0x4a000000000000040a000000000000100000000000000015500000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xff00ff00
def s_36 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_36 : Nat := 0x15005f00
def ep_36 : Nat := 0x4a0000000000000000000000000004000a0000000000100000000000000015005000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xf0f0f0f0
def s_37 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_37 : Nat := 0x10505070
def ep_37 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_37_0 p) (Nat.blt p 32)
def hc_37_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_37_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_37_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_37 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_37_2 (Nat.sub p 64)) (hc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
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

def m_38 : Nat := 0x33333333
def s_38 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_38 : Nat := 0x11131333
def ep_38 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xaaaaaaaa
def s_39 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_39 : Nat := 0xa0a2a
def ep_39 : Nat := 0xa2000000000000a002000000000000a0a0800000000000000200000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xf000f000f000f0
def s_40 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_40 : Nat := 0x10005000500070
def ep_40 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_40_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_40_0 p) (Nat.blt p 32)
def hc_40_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_40_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_40_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_40 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_40_2 (Nat.sub p 64)) (hc_40_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_40 : Nat → Bool := dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 64 (dagTraceF m_40 s_40 5 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 64 bds_40 (dagTraceF m_40 s_40 5 f_40) (cur_40 0) (nh_40 0) s_40 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 ch_40 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 ch_40 = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → ch_40 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 64 → ch_40 i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 6 :=
  lowerDagV5 (kn_nil) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xff000000ff0000
def s_41 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_41 : Nat := 0x170000005f0000
def ep_41 : Nat := 0x4800000000000000000000000000000000000000060000000a000000120000000000000014000000500000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0x5555aaaa
def s_42 : List Nat := [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa]
def g_42 : Nat := 0x15550a2a
def ep_42 : Nat := 0x4000200000000004000a0800000000100000200000000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_42 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_42 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 10 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 10 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 10 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 10 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0x5500aa005500aa
def s_43 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_43 : Nat := 0x15000a0055002a
def ep_43 : Nat := 0x400020000000000000000000000000000000000004000a0000000800100000000000200000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
def cur_43 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_43 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_43 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 10 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 10 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43 : treeBlockF 0 10 ch_43 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 10 → ch_43 i = true := fun _ h1 h2 => treeBlockF_at nb_43 h1 h2
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_nil) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0x4444444444444444
def s_44 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_44 : Nat := 0x4044404444444
def ep_44 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_16, s_16, 4, g_16), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9)]
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_44_1 (Nat.sub p 32)) (cc_44_0 p) (Nat.blt p 32)
def hc_44_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_44_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_44 : Nat → Nat := fun p => Bool.rec (hc_44_1 (Nat.sub p 32)) (hc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 43 bds_44 (dagTraceF m_44 s_44 6 f_44) (cur_44 0) (nh_44 0) s_44 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 ch_44 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 43 ch_44 = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 43 → ch_44 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 43 → ch_44 i = true := nj_44_1
theorem lb_44 : LowerBin m_44 s_44 g_44 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_16 (kn_cons lb_11 (kn_cons lb_9 (kn_nil))))) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0x8888888888888888
def s_45 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_45 : Nat := 0x800080808
def ep_45 : Nat := 0x8080000000008000008000000000800080000000000080008080800000000000000000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0x55550000aaaa
def s_46 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_46 : Nat := 0x155500000a2a
def ep_46 : Nat := 0x40000000200000040000000a0800001000000000200000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_46 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_46 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 10 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 10 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 10 → ch_46 i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x55005500aa00aa
def s_47 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_47 : Nat := 0x150055000a002a
def ep_47 : Nat := 0x4000000020000000000000000000040000000a000800100000000000200000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_47 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_47 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 10 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 10 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 10 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 10 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x2222222222222222
def s_48 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_48 : Nat := 0x2000200020222
def ep_48 : Nat := 0x22000000000000002200002000200020020000200020002020000000000000000000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0x5050505050505050
def s_49 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_49 : Nat := 0x1010105010505050
def ep_49 : Nat := 0x40400000000040000040000000004000400000000000000000000010101000100000000000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xc0c0c0c0c0c0c0c
def s_50 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_50 : Nat := 0x4040c040c0c0c
def ep_50 : Nat := 0x408080000000408000008000004000800080000000000000000000000000000000000000004040004000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_17, s_17, 4, g_17), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_50_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_50 : Nat → Nat := fun p => Bool.rec (hc_50_1 (Nat.sub p 32)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_17 (kn_cons lb_6 (kn_cons lb_8 (kn_nil))))) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xa0a0a0a0a0a0a0a
def s_51 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_51 : Nat := 0x2000a000a0a0a
def ep_51 : Nat := 0x80a000000000800000a000002000a000a0000000000000000000000020000000000000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xff00ff00ff00ff00
def s_52 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_52 : Nat := 0x1100150015005f00
def ep_52 : Nat := 0x4004a000000040000004a0000000000000000000000040004000a0011001000100000001100150015005000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) (nh_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 7 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV5 (kn_cons lb_32 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf0f0f0f0f0f0f0f
def s_53 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_53 : Nat := 0x107050f050f0f0f
def ep_53 : Nat := 0x4080a000000040800000a000006000a000a0000000000000000000001020000000000000104050005000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 7, g_50)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) (nh_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 7 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV5 (kn_cons lb_50 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x5555555555555555
def s_54 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_54 : Nat := 0x1115155515555555
def ep_54 : Nat := 0x440400000000440000040000004004000400000000404000400000011101000100000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_44, s_44, 7, g_44)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) (nh_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV5 (kn_cons lb_44 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xaaaaaaaaaaaaaaaa
def s_55 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_55 : Nat := 0x2000a000a0a2a
def ep_55 : Nat := 0x80a200000000800000a200002000a000a00200002000a000a0a0800020000000000200000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_31, s_31, 5, g_31), (m_39, s_39, 5, g_39), (m_48, s_48, 5, g_48), (m_45, s_45, 5, g_45), (m_20, s_20, 5, g_20), (m_51, s_51, 5, g_51), (m_14, s_14, 4, g_14), (m_8, s_8, 4, g_8)]
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10218064d2260b9242350884e74cd433104c01f 6 63 2 3 10 1023 14 16383
def nh_55 : Nat → Nat := unpackHintV5 0xda80a669a60071e96a8e638e6380365b006c0000 0x9d5aec0eb38c6b19d4015b4b008f3eb611ee718e633d002ae78edc37680d407412a9c633bdeb006538c6700000469d7a010e3cf8025 16 65535 7 127
def f_55 : Nat → Nat × Nat := unpackForestF 0x201914cd82e10cca42250884e104c01f 4 10
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 3 7 bds_55 9 (dagTraceF m_55 s_55 7 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 3 7 9 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) (nh_55 0) s_55 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 9 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 9 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_31 (kn_cons lb_39 (kn_cons lb_48 (kn_cons lb_45 (kn_cons lb_20 (kn_cons lb_51 (kn_cons lb_14 (kn_cons lb_8 (kn_nil)))))))))) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xffff0000ffff
def s_56 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_56 : Nat := 0x155f00005f7f
def ep_56 : Nat := 0x4a2000000000000000000000004a000000200000040a00000a0800001000000000200000155000005040
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 6, g_28), (m_22, s_22, 5, g_22), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_46, s_46, 5, g_46), (m_15, s_15, 4, g_15), (m_7, s_7, 4, g_7)]
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_56 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x15739c6798c60000b9756e382f6579ce33bc6300009f2d5abb4e08dda3b702deb19ce3008702a34265538ce3000005d0e3c00b51a74025 16 65535 7 127
def f_56 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 3 7 bds_56 9 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 3 7 9 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 9 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 9 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_cons lb_22 (kn_cons lb_27 (kn_cons lb_29 (kn_cons lb_30 (kn_cons lb_31 (kn_cons lb_46 (kn_cons lb_15 (kn_cons lb_7 (kn_nil)))))))))) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xffffffff00000000
def s_57 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_57 : Nat := 0x1117155f00000000
def ep_57 : Nat := 0x448000000000006004a000000000006040a0000000011121000000000001114155000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xffffffff
def s_58 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_58 : Nat := 0x155f5f7f
def ep_58 : Nat := 0x4a2000000000004a002000000000040a0a0800000000100000200000000015505040
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 6, g_37), (m_36, s_36, 5, g_36), (m_35, s_35, 5, g_35), (m_33, s_33, 5, g_33), (m_38, s_38, 5, g_38), (m_39, s_39, 5, g_39), (m_42, s_42, 5, g_42), (m_1, s_1, 4, g_1), (m_14, s_14, 4, g_14)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0xb739c6798c60000b56aed384f9a79ce33bc6300005eae5d5b8e10edc37682deb19ce3004684c38159538ce3000005a8d3a00ba1c78019 16 65535 7 127
def f_58 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 9 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 9 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 9 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 9 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_37 (kn_cons lb_36 (kn_cons lb_35 (kn_cons lb_33 (kn_cons lb_38 (kn_cons lb_39 (kn_cons lb_42 (kn_cons lb_1 (kn_cons lb_14 (kn_nil)))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xffff0000ffff0000
def s_59 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_59 : Nat := 0x11170000155f0000
def ep_59 : Nat := 0x4480000000000000000000000060000004a000000060000040a000011120000100000001114000015500000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_26 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def g_60 : Nat := 0x1117155f155f5f7f
def ep_60 : Nat := 0x4484a200000044800004a200006004a004a00200006040a040a0a0811121000100000201114155015505040
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_59, s_59, 8, g_59), (m_57, s_57, 8, g_57), (m_25, s_25, 7, g_25), (m_52, s_52, 8, g_52), (m_40, s_40, 6, g_40), (m_53, s_53, 8, g_53), (m_54, s_54, 8, g_54), (m_44, s_44, 7, g_44), (m_58, s_58, 8, g_58), (m_56, s_56, 8, g_56), (m_7, s_7, 4, g_7), (m_37, s_37, 6, g_37), (m_50, s_50, 7, g_50), (m_32, s_32, 7, g_32), (m_28, s_28, 6, g_28), (m_26, s_26, 7, g_26), (m_55, s_55, 8, g_55), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12), (m_41, s_41, 5, g_41), (m_24, s_24, 5, g_24), (m_34, s_34, 5, g_34), (m_49, s_49, 5, g_49), (m_38, s_38, 5, g_38), (m_36, s_36, 5, g_36), (m_42, s_42, 5, g_42), (m_46, s_46, 5, g_46), (m_9, s_9, 4, g_9), (m_21, s_21, 5, g_21), (m_51, s_51, 5, g_51), (m_19, s_19, 5, g_19), (m_5, s_5, 4, g_5), (m_13, s_13, 4, g_13), (m_47, s_47, 5, g_47), (m_43, s_43, 5, g_43)]
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xce0e607301902c806307181842ba25c06e01700b60db02d816c0b60590ac81640ae15606b01580aa0cd226813019803d3c0f8001 0x693203cdf01caf80ca6006936032dd0184c80fa6f0753583699c174c60b03404cb001f1b00e2c00613b02c9b814090072800a35f049ab82297c104b606a57025298108ec0646e024660f2378751ac388ce1a4630c9b7862dac2e6ce12b6308da7844d2c2068e0ab43014920061380206d2a45f94e2dca115e478a722b5f90dadc82d5e3d6a71e34f8eda5c72d1e3868718a5f8bd2dc5695e294a71424f88925c4291e204870d23f8651dc308de164670495f7fcadbf055df22a6f794f798a5bc651de2286eb13f73c9db884ddbb266da92f6c495b4849d98246c085f59c2daa415d3f0a69e04f4b425a5011d270868983f4101d9ca0dcd30666082f2d81593a09c800463701f1700d87c05c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x92320221440843081e1bc0780e09b0b60644c0570ae050698520a02384700d09811ca288500810c218011001 0x2dd6fb359ebc6fab19e9c57a2dbe836b9ad9e5b6392d6e43578ed2e2b478896a0a427e8e8281028491e864761109124721f0204c6e8edb2336a11089246619081241e491857c1a491787c589614a4458d7060145090058145293143545a93d5a4b5491d3a431405049244c0d1204410490312442170f278 11 2047 5 31 11 2047 18 262143
def cc_60_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c230669906418160162545324c121481023c4e1344a328082200711c061144320c0300c01204001 0x3646fd519f436fcedaf2367c4d8f0b4bbed1ef04eba0dad270b09a0a01026082b27024042a260a49a088102004078101c0827d7c9c9c06810988e04810948e040100e08232500c0421956845520156 10 1023 4 15 11 2047 18 262143
def cc_60_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8dc2c360a8d42a150994c243209044621103d1c0c260289408240201004420088402001 0xfe593e97cf6593c57cee5f3a934e4573f46ff919fd36ff2dafb367e8d8f9b4be2d1f814ede4db6864d61f34864cd5f3287cc60d3005c 9 511 4 15 11 2047 18 262143
def cc_60_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa05db741c1701b16c1b060d805c5705856054550505404c530485204812040900400e2380d103400 0x4fb50b4acf6119eba2bd6b5aaa685505ae94b3d195ba22af4252e78a3ce0649a08930df25c3e4104c950892619244124787c8d0491611221ae4385c854c9080920a334dc6f998d72d19e5231c926f904d71c99e3131c524f894970c91e0d21c084e 10 1023 4 15 11 2047 19 524287
def cc_60_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a9a8a1a0a099986e686160605249483a3838382a2821201911100908080801 0x2f8125e07cb90b97f19ef535dda67ba4977091edc275ab70b325f6449ec5b857b60ac6815915aad2b5494ca74974cdc290a65026b 8 255 3 7 11 2047 19 524287
def cc_60_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x84a107c9f07c1f07c1f07c1a5681284811144101401003c4f0384e0344d0340b22c0b02841904001 0x1ae1937c126b064dd049b496f6529ec15bd72a7ac48f91b5f1363e04d7bc98f7119ed85cd50a9a80db49326827ccd4c9964d3253e63944c6269869734637e7c67ce49d985bf28b5e4167c52c78852f08a3e007c 10 1023 4 15 11 2047 19 524287
def cc_60_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x88602801f1785e0745d0705c0701a264590605805c5705856054541501404885d104400882000800 0x7f93f8057c7f4707e25c741217cc687b95c7aa3f7a23379c707895c77a5c7695c75a6b753507435c7395c8126f80a6b7ea677da637d24d7c16f7b16b79167781637712f7612b74927731236d0646c864718346c06470824 10 1023 4 15 11 2047 20 1048575
def cc_60_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c5f0785e0745d0705c06c5b0684fb3c0f03c0e1380e0380e0380e0380e0380e0074100040000000 0x8fa448ec5a8d9448c9448b9448a9449356f9256791b569126b902638f25b8e2358d16b8c1638b15b8a1238857c8936f88b6b87b678736386a6f8626b85a678526384a3f8423b83a37832338283681c68 10 1023 4 15 11 2047 20 1048575
def cc_60_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0582854098cc2432088c42030078bc1c2e0701a0c060301804820100802210080400200 0x9f1489e9449d8449c8649b8449a864998449884c9d4639c36f9b34f9a26f9924f982379784e970369634595a6f9516f9492792b7c90a44 9 511 4 15 11 2047 20 1048575
def cc_60_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x942328862084610806007c5e1781d14e9304c121481114411040500400e2380c2300b12c0b02840a 0xafa3faf233aec70ada7cac97caba4bab370aa17cb3361b2a6db223bb0a37b013bae137ad12fac12baa927a9923a8034a7044a585ca4a64a4024a0844a3034a2024a092da8b4ba7b43a6a4fa624ba5247a3a43a2a3fa1a33a104ea0036 10 1023 4 15 11 2047 20 1048575
def cc_60_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xd06832390c0e02e370b8586c160a1502633090c82231080c02002e100804020088040000 0xbe85cbd834bc844bb05cba264b9824b8834b7824b684cb5824bfb4fbf34bbe347bd343bc24fbba4bbaa47b9243b823fb723bb6237b5233b484eb4036b193fb1470 9 511 4 15 11 2047 20 1048575
def cc_60_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xac283a02719c26167590641725c170549504c9304c1124411040500401003c4f0384e03441c04001 0xcfb7ccf17ccd14cce144cd466d146fd046bcec67cdc63cc94ec106fb506ba9867a18638a04f8304b730476e043c9c56cb356ca568c9b68c8c6dc7a4ac7b64c7264c5964c3c68c2a64c1964cbc55cab59c9347c8255c6a4bc623bc514bc4947c413bc3137c212fc1123c0044 10 1023 4 15 11 2047 20 1048575
def cc_60_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xd02f5bc2789c26198251941c9701b16c156541415014048911440f23c0f03c0d20ac200441000400 0xdfa5bdf253ba05ba485342823e1b6be0b63e015cde954de136b906ba386341833dd264dc27cdcc6fdbc67db24ec206fb806bad067a28638484b77047da17cd9c67d914eb706bac0678404b76047d8370d702fd6827d6370d5360d3b40d3c56d3256d7d67d5c67d4c57d435ad2b42b606baa8679805b948578384b74847d1964d0944 10 1023 4 15 11 2047 20 1048575
def cc_60_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8320c8311c4301c02f192e40902408c6308c16d58151541505414148920445010f4210800200000 0xee244ed244ec45af0d6fefd67ef356eea6beda63eca5beba35bc06ba68639905b45023e9d7ceab6fea36be9367e8b63e8136c406fbb86bb0067a60636203f5d03b5083744833e7468e503fe5d7ce4c70e3a5c44021e6a6fe626be4267e3263e2a4dc306fba86bae067a50636102f5c02b4f02743023df964df164e1134 10 1023 4 15 11 2047 20 1048575
def cc_60_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82a0a82a0a46817a9e0781d1741c14a92048102400f13c0e1380d1340d016050140140401004001 0xfd83ffd470ff361fea6dfe23bfca378583b790376402f5d82b5282747023fb1346382dfbb4bfab43fa14ef99368c04f8504b780476f0436283f46033f8848f8044f7144f6164f5144f6c63f5b6ff4b4ff414ef3936c506f8b04f51837f2b45f226fc486f51027f037c 10 1023 4 15 11 2047 20 1048575
def cc_60_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x92324248490812d315cab04ac941282324608c1092103e47c0f81d23a047088101200400788f01c23807000e 0x21f6f90f567875ad438d5e1b6ad0396b7a4adafe1ad360b611813828b7c0c5adfc2cefb96363037afc1ad640cea88631cc0f8c206c4702e1101385d26c085adf92cebe06b584338e207c5f0362281708009c2e93a022d6fa9635e835a9e18c1502708c56851ab4255a2116d107c6d8352541ad920c4c90ac5584dacc20d1e0e4ab05a4b8291da6812d2a08e8683b3e01b9980bc9204704144814ae4064d20769f0334b811a3c04d0e0129d0013646827a1812cf608e700433281f97a0eca806e48033 11 2047 4 15 11 2047 21 2097151
def cc_60_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc55a2b0551aa1326604c098128a504a0904e7dc82cd4909012019b320334600c0180300510a005000800000 0x8fdad44c96a406ad1225b8f91abda56d9b2469d05b2501186804e1d47b1926f8e92ec205bde528ad492764837a58114ae04e298178ce2b46cd5a34ad119b688de2ac6ad663268ef594b790a3baa4edcd26e9c04b4ac23a240ed0206e3d01f1a00d8a205c320271824e774a7ba852dcc28ee194348827a2212d0108e720431e40f8ce06c5002e1881374c9db964dd10076800371e00f8cc06c4f02e180138ba3645b1822c6c2e913b7209ba1e0ecfd06e3b01f1900d89a05c2e0271524e76ca7ba252dc628ee094348027a1c12cfb08e710431d00f8c406c4b02e12813899a244a91227add1246388d274165bdd929ec686f4782789205e1d6b224017 11 2047 4 15 11 2047 21 2097151
def cc_60_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xb12c0b02c092240902409024090240901c8701394c0f43480d00000 0x89e497853f4983f16c1794b619466d87a3f77d3f6bd274903f2d0271641793f4893b44936489324492d4892944924489204491a556e52f689233442f26c231f81f1b01b15c170f0139123568123264230e81367d212602190a6d6dd2f6cd2b6ad276752333c2f2fc2b2c027258231f01f1a81b154170e013 10 1023 4 15 10 1023 20 1048575
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_60_18 (Nat.sub p 576)) (cc_60_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_60_16 (Nat.sub p 512)) (Nat.blt p 544)) (Bool.rec (cc_60_15 (Nat.sub p 480)) (cc_60_14 (Nat.sub p 448)) (Nat.blt p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (Bool.rec (cc_60_13 (Nat.sub p 416)) (cc_60_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_60_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_60_10 (Nat.sub p 320)) (cc_60_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 448)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_60_8 (Nat.sub p 256)) (cc_60_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_60_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_60_5 (Nat.sub p 160)) (cc_60_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_60_3 (Nat.sub p 96)) (cc_60_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_60_1 (Nat.sub p 32)) (cc_60_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def hc_60_0 : Nat → Nat := unpackHintV5 0x97200896d81296b80895804e9560089540089520089418428ca9dc81c2ba79621873697e681ad45fb21a56fa2e5269244de92044725e44500843c8223e09703572262a92b82571481cb23017a14410c9b60931e604b91e00012e000000000000 0x871309c9c0c3c2c2c1c131f46e2787872700c2d0744d0781c9c0c0c0c0c3c2c3c2c0c0c0c0c1c1c1c1c0c0c0c0c1c1c1c1c3d04c4c03030303030303030b15501c1d11555540d55555555aaaa03aaaaaaaa95562740c0c0c0c3c2c3c2c0c0c0c0c1c1c1c1c0c0c0c0c1c1c1c1c1c3c1e1c1cec1c1c1c4c1c1c0c0c0c0c0c0c0c0c1c9c1c1c1c1d55540d55555555aaaa03aaaaaaaa9556274544d103540d50b543d50744541d075541d5555908c3c03030030303030300c3c4c3e1c3c3c0f0f0f0f030303030003c070fc0700c0303c0f04c4c03c3c6c3c6c0f0303030303030f0f0f0f1b01b154155155554146d87030303030f0f43c0c0c0c0c4c4c4c4c0c0c0c0c3c3c3c3c4c4c4c4c0c0c0c0c0c0c3c3c3c3cfcfcfcfd55555555555543c3c4c0c0c0c0c0c0c0c0c0c0c0c0c3c3c3c3c3c3c3c3c4c3e1c0c0c0c0c0c0c3cfc3c1c3c3c3c1c4c4c4c4c0c0c0c0c3c3c3c3c3c3c6c6c3c3c3c3c3c3c6c4c4c4c4c0c0c0c0c0c0c3c3c3c3c6c6c6c6d555555555555551b61c070700c0c00c0c0c0c0c0302c4c03c2c9c2c3c230303030304c1e1c1301c131300c0301c0704c4c06c6c6c6c6c1b0303030303030b1b1b0b0700714155155554146d8700c0c04c4c0303030304c1e1c0701c030300c0c0701c130700c0c0c03030309c1c1c0f070701c1c131300c0c0c0c0c0c6c6c6c6c1c01c1c1c1b06c1c1c51555541544551b61c070300b1305c2c5c2c000300c0701c131305c5c5c5c5c5c2c6c6c2c1c01c515555051b61c030300b1300c0c0c0c000300c0701c071300c0c0c0c0c0c2cfcfc2c1c01c515555415454070703130300c030303030300c0c0b0f04c0f0b2702c4c0303030304c8c1301c13078700c0c030301c0713131b1b04c1313131b04c4c0303030303030b1b1b0b07007511514555550546d878701e1c6cfc03030131300c0c0c0c01c1300300c0701c500c0c0c0c9c9c1c104c4c0303030303031b1b1b1b0700706c6c1c1c1c03030131300c0c0c0c0701c13078700c0301c0708c1c0c0c03030300c1c9c07070f01c070704c4c0303030303031b1b1b1b0700701c1c6c1c6c071455554115541d146d87030303030f0b0f0b030303030707070703030303070f07870707070707230707071307070303030303030303070f070707071b1b1b1b0303030303030b0f0f0f0b1b070707070707071b071b0707555555555555546d8700c0c02c3c030303030000c0303c1c1c070f07870fcfc0303030303030b070f0b0700714555550551500c0c03c1303c2300c0c0c03030302c3c030303030707070000c0303c9c0f0707070f078706c6c0303030303030f0f1b1b03c0f0f0f1b0b0f0f0b07007145551155550546d87030303032727030303030303030327271b1b1b1b0303030303031b1b1b1b1b1b1b1b5555555546d870b0b0b03030303030303030b0f0b0b02c2d0b02e1c0c0c0c0c0c0c2c2c2c2c2c2c2c2c0c0c0c0c2c2c2c2d55555555556aaaaaaaaaa9540c0c0c0c2c2c2c2c2c0c0c0c0c2c0b0b0b130b00c0c0c0c0c0c0c0d50b0b0b0b030303030b0b0b0b0b02c1c2c0b075555555555555aaaaaaaaaaaaa550000030303030000000c003002c00b0000000c02c000015554400400402aaa88008009540c0c0c0c0c0c0c0c0c0c0c0d55540d5555aaaa03aaaa95564ed513540d5035550f541d55559 24 16777215 10 1023
def hc_60_1 : Nat → Nat := unpackHintV5 0xb1e9faab8998a26a489b09d88f92de8871c87c4b0a7bd81c7b48247489b06b824264f1a45bf240525a664d314a47018c3c8a9e3c28183c08083bc8103b102e3af0083ad00839d83e3379982a7a402469841b6242102ace0a0988004a70000012 0x3032727032703030327271b1b1b131b131b3b03031b1b1b03031b1b1b0f1b0f1b1b071b1b1b1b071f47d0347d1f47d1f47da86e1b80e0386e1b86e1b955a581540030300c0c0c0c0c0c0c0c0f130f0f1543c3d40c0c0c0c0010c1c10c1c0300c0f03c501515540d5541280a8aaa03aaa0954270f00c0c00c0c0c0c0c030f130f870f0f03c3c3c3c0c0c0c0c000f01c3f01c0300c0f03c505545540d5541282aa2aa03aaa0955604544d130045543d0440d503542d50f541c0155640c0c0c0c3c3d0f0f0b03030303450f0f403030303030303030b15502c4c2c4c0c0c0c0c2c2c2c2c2c4f070b13c1d555555555556aaaaaaaaaaa9540c0c0c0c3c4c3e1c3c3c2c4c0c0c0c0c0c0c3c3c3c0c0c0c0c0c0c0c0c2c9c4c2c4c2c4c0c0c0c0c2c2c2c2c2c4c2c1c2cfc2c1d55540d55555555aaaa03aaaaaaaa9556274544d103540d50b42d50f43d50b42d551355507445559130b4540303030303030303030303030f15143c3d0f030303034310c1d0c430713131313030303030f0f0f0f555555555555aaaaaaaaaaaa550f0f130303030303030303030303030f0f0f0f0f0f0f0f130f870303030303030f3f0f070f0f0f0713131313030303030f0f0f0f43d1f5555555503555560f86eaaaaaaa80eaaaa55590f5550f43d5513b544d13440d503542d543d0f541d1155661c0709e1c1c1209c030300f0b130f130f8700c0c0c0c15400c0c0c0c0c0c0c0c2c2d554000300c0b02c01c01c51540d5505454128aa03aa82a2a09556274030300f0b130f130f870303030303c3c0c0c03030300c2c4c4c000300c0b02c2701c3f01c51540d5515514128aa03aa8aa8a09556270544c103540d50b543d411552741107005559055000c0c030303030303030302c4c3f0f0b0b3f0f0b0b0303030301304c050500c0301c07140545550355504a02a2aa80eaa825501c1c03030030303030300c0b1300f0b270b0f09c0c0c0c0c13078704c0704c4c0300c0701c505545540d5541282aa2aa03aaa095560544c011553b41103540d50b543d50700555900c0c04c4c0303030304c1e1c0701c030300c0c0701c130700c0c0c03030309c1c1c0f070701c1c51540d5541511528aa03aaa0a88a95560544c103540d50b543d50741c01150741c101155564070300b1305c2c5c2c000300c0701c51175555412885eaaaa095560544c117545d50b543d5070055590707050030303030303030300c0c3f0f0b0b3f0f0b0b02c4c0303030305050000c0301c074505145555418a0a28aaaa825501c1c0c4c0c0300c0c0c0c0c030302c3c1303c2c9c0b1300c0c0c0c133b04c0704c1e1c030300c0c0701d1347c455451540d554184e1b22aa28aa03aaa0955644d0404550544c103540d50b543d50741c01155642c3c9e1c3c2c070b0f1f46e87870b103230703d209c03030131300c0c0c0c01c1300300c0701c15400c0c0c0c0c0c0c0c2c3c3c2c1c1c01451540d5541054528aa03aaa082a29556403030131300c0c0c0c0701c13078700c0301c070ec1c0c0c03030300c1c9c07070f01c0707145503555045544a2a80eaa822aa255581513040d503542d50f541c014115507411564030300b0f00c0c0c0c0fc4cfc4c00c0c0c0c0c0c0c0c1c1d554000300c070f03c1c1414515554151504a2aaa82a2a0954030300b0f00c0c0c0c3b04c1309c0c0c03030300c1c1c1c000300c1c3c1e1c0f070703c3c51540d5515514128aa03aa8aa8a09556270544c103540d50b543d411552741107005559030303030f0b0f0b030303030707070703030303070f078707070707073b0707071307070303030303030303070f07070707555503555555556aaa80eaaaaaaaa55591513440d503542d50f541d074442d50741d550742d55564030300fc4cfc4c00c0c0c0c0c0c0c0c0b0f00c0c0c0c1c1d554000300c14140701c51540d4505554128aa03a282aaa0954030300f04c0f0ec03030300c0c0c0b0f00c0c0c0c1c1c1c000300c0f2703c1c1c1c3c1e1c51540d43d1f1155554128aa03a0f86c8aaaaa095560544c103540d50f41011550b543d50741c01155641327 24 16777215 10 1023
def hc_60_2 : Nat → Nat := unpackHintV5 0xa9948ca9d012aa43062276534e98a89da4294028c9082a18d32e81389f9e4940a73b0ae9ab746a66c882981833459c8d3157d1ea51d08492c635c470482900d3683b489d8ca74562c00d388ef4221f488e863b32e13d8a283733060af05b816f29a029465000014a 0x30303030b0b0b0b030303030b02c2c2c4c2c0303030303030303a82c2c2c2c0c0c0c0c2c2c2c2c2c0b070b02c1c7d1f40d0342c2d0b1f42c2d42c6d42d0b6aaaaaaaa696a9a400000c0c0c0c0000003000c00b002c0000000000340d0b42d06c0041f0000aaaa200100269030303033333030303030303030333331f47d0340c0c0d1f47d1f47daaaaaaaa5a1e963ba84ea03a80eaa83ea07aaa1b9500c0c0c0c0e1c0c4c0303130304c4c03c5c5c5c3c23030303030008c0705c0700c8c03030ac27013131313001b05c5c5c5c5c5c5c5c06c03030303030303031b1b1b0f1b0f1b671b07001b0711301f5171710340d1f47d1f06a203003a030320380e0380e030955a580c0c0c0c0c4c4c4c4c0c0c0c0c4c4c4c4c0c0c0c0c9cacac9c4d1340d0347d1f47d1f44c030303030300c0c0c0300c0c8c2c8c3c8c3c8c2c8c1c8c2308c1d680e50380e0380e0380e0380e6035680da0303030313030313030303030387130f1313130f13271313131303030303133f1307131313071313131303030303272b2b2713131b1b131313131313131313131b1304c4c4c4c4c03030303030303031b1b1b0f1b0f1b531b071b06c1b07131f5131351344d0340d1f47d1f47da80c0e80c0e80e0380e0380e0380e03955a580c031300f0f00c3c3c0c002300c0f03c44c0347d0f43d1f0404c4c4c4c00c0c8c8c8c8c0c0c3c2c3c3c3c3c3c2c8c1c008c1c283e421300e0383e0f86c260f5403d808c3c031300f03030f2300c3c4c3e1c3c3c0f0f0f0f030f0f030003c070fc0708c0303c0f013131313000f03c3c6c3c3c6c6c03c03031b231b1b03030f0b0f0f0f0f0f0b1b07001b0711300f50f1f10347d0f43d1f06a21300fa0f1b20380e0f83e1b0955a584c0c4c0c3c3c3c3c0c3c3c0c4c4c4c4c0c5c5c0c3c3c3c3c4d1340d1743d0f47d1f44c130b130b1300c0c5c5c5c5c0c0c3c2c3c0f03c2cfc1cfc3f0fc1d683e51384e0380e0f83e1b86e5a0f59683da0f0f130f1703030f0f0303130313030f0f0f0f0f0f0f0f130f87030f170f0f030f3f0f070f0f0f0713131313031717030f0f0f0f0f0f1b1b0f0f0f0f0f0f0f0f0f0f1b1304c4c4c4c4c03031717171703030f0b0f0f0f0f0f0b1b071b06c1b070f1f50f0f51344d0345d0f43d1f47da83c6e83c3e84e1380e0383e0f86e1b955a580c0c0c0c3c3c3c3c0c0c0c0c8c5c5c8c0c0c0c0c3c3c3c3c7d1740c0d031f43d0f47d1f48c171317132300c0c0c0c0c0c0c6c2c0c0c3c2c0c0c0c0c0c0c8c1c8c2308c1d680e50380e030380c0e0380e0380e6035680da0f0f0f130f0f0f2303030303030f030f0f170f0f0f0303030303030f03030387231717230f3f0f070f0f0f07030303030f0f0f0f1b1b171317131b230f0f1b1b0f0f0f0f0f0f0f0f0f0f1b03030303030303031b1b03030f0b0f0f0f0f0f0b1b071b0b1b0b1b071f45d0f1f50f0f5030340c7d0f43d1f47da80e0380c0e80c0e80c0e030380e0380e03955a580c031300b1300c2c8c0c000700c0701c44c0347d0b47d070404c4c4c4c00c0c8c8c8c8c0c0c2c2c8c3c8c3c2c2c1c1c001c1c287e421300e0382e1b81c261b5406d801c1c03130230303232300c0b1300f0b270b0f08c0c2c8c0c13078704c0704c4c0700c0701c04c4c4c4c006c1b231b1b1b1b1b01b00c0c6c8c6c6c0c0c2c2c6c3c6c3c2c2c1c1c001c1c44c07d47c7c40d1f42d1f41c1a884c06e86c6c80e0382e1b81c25569600c4c04c4c0317170304c1e1c0701c070705c0c0701c130700c1c1c17030309c1c1c0f070701c1c04c4c4c4c00c0c5c5c5c5c0c0c6c2c6c3c6c3c6c2c1c1c001c1c1c1c1c1c06c01b01c1c1c1c44c0345d1f47d07041c1c41f5a884c0380e1b86e07081c1c81ba5569601c4c02c4c170b170b0000c0701c07013131313017171717171717170b0b1b0f1b0f0b0b070700070711305d1742d1f41c1a884c1785e0b86e070955a58031300b1300c2c5c0c000700c0701c44c0345d0b47d070401c1c4c1c00c0c5c5c5c5c0c0c2c2cfc3cfc3c2c2c1c1c001c1c284e421300e0382e1b81c25a1359404d801c1c4c4c5c0304c0c4c0c0c031302c3c1303c2c9c0b1300c2c5c0c132304c0704c1e1c071705c0c0701c4c4c6c6c04c01304c4c6c04c4c4c4c00c0c5c5c5c5c0c0c2c2c6c3c6c3c2c2c1c1c001c1c4c7c413511300d1742d1f41c1a84c6c813a21300e0382e1b81c25569600c4c04c4c032323030001c0301c0711300d1f47d1f41c101313131300303232323230303230b230f230f230b07070007070a079084c0380e1b86e070981d50076003130131300c8c8c0c0701c13078701c0301c0708c1c0c0c07072300c1c9c07070f01c0707013131313003031b231b1b03031b0b1b0f1b0f1b0b070700070700701c1c6c1c1c6c6c01c11300d1f47d1f41c101d07507071f1f1a884c0380e1b86e07080781e81c1c6c6c955a580c0c0c0c8c5c5c8c0c0c0c0c1c1c1c1c0c0c0c0c1c1c1c1c7d1740d0347d1f41d0748c171317132300c0c0c0300c0c8c2c8c3c8c3c8c2c0c0c0c0700c0d680e50380e0380e0380e0380e6035680da0323030303032317172303030303070707071707030303870307030307070707072307070713070703030707270707070f07070303031b05c4c5c4c6c03030303030303031b0b1b0f1b0f1b0b07070701c07070707070707071b07071b1b070707071f45d0340d1f47d0741d070741d41c1c7c7d6a0380e0380e0380e0380e030380e80c1c0c6e955a580c2304c1308c030300c1c0c0b1702c3c2303c2c9c0c0c0c0c05c170030300c0c1c0c0c0e1c0701c05c4c5c4c06c6c6c6c06c01b06c8c6cbc0c0c0c0c0c0c0c0c2c2c6c3c6c3c2c2c1c1c001c1c45c1f1f107d40d0342d1f41c1a880c0303200e80e0380e0380c255696032b032b030f0b0f0b030b0f030707070703070703070f07870707070707230707071307070303070707230303070f070707071b06c4c6c4c6c03031b2b1b1b03030b0b0f0f0f0f0f0f0b0b1b0b07070701c07070707070707071b0b07071b0b070707071f47d0347d0b43d0741d07075071f5a86e1b80e0382e0f81e0781c1e81c6e955a58032b00b0f00c2c3c0c000700c0f070701c3c1e1c47c0347d0b43d07040fc4cfc4c00c0cac8cac8c0c0c2c2c1c1c3c1c2c2c1c1c001c1c283e421b00e0382e0f81c25a0f59403d800cac03c1303c2300c3c8c0f030302c3c030b0f030707070001c0303c9c0f0707070f078701b131b13003031b2b1b1b03030f0f1b1b00f003c0f0f1b0b0b0f0f0f0f0b0b070700070711f00d1f43c7c40f50b43d0706a21b00e0383c6c80fa0b83e070955a580c0c0c0c8c5c5c8c0c0c0c0c8c5c5c8c0c0c0c0c9cacac9c7d1740c0d031f47d1f47d1f48c171317132300c0c6c9c2c8c3cac3c8c2cbc1c8c3f08c1d680e50380e030380c0e0380e0380e5a03580d680da2305c4c5c4c8c0323030303230303030b030b0b0b0b03030b0b030303030303030b030b03030b0b0b0b0b02c1c2c0b070303030b030b03030b0b0b0b1f45d030350303503035031f50b42d0b42d0380e0303a0303a0303a0303a0380e0380e60348c8c8c8c2c2c2c2c0c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c7d1f40d1f42d0b42d0b46e1b86e1b82e0b82e0b986d670353030b0b0b0b030b0b030b0b0b0b030b0b030b0b0b0b0b0b1f47d0347d0b0b42c7d0b42d0b02c2c2c4c2c03030b030b0b0b0b03030b0b0b0b070b02c0b075a0b946e1b80e0382c2e0b1b82e0b986d5a0b6800000000000b0b0b0b0b0b0b0b030303030b03000000000000003035030350340d0b42d00000303a0303a0380e0380e00603400000c2c2c0c0000000b000347d0b42d07c000000030000b002c001020000380e0b82e06c0186d0210 26 67108863 11 2047
def hc_60_3 : Nat → Nat := unpackHintV5 0x8a3d3d430a851fee65cf841cc77214038f8a61bc02f0d6d1cc65e5613116771741528addb0c5364e2271ea512764648f092a4474c4207a700f004f46fb214317d9716f2730a39500476a9820c4bc0e967305ea58427e1dc0ec94a0458c3014a388000294 0x9c3c031300f03030f2b00c3c4c3e1c3c3c0f0f0f0f030f0f030003c070fc0708c0303c0f1415515555410544c011550f41103548d50b543d5070055484c03e83c6c80e23031b83e0f86c25a1d5546c4c2d1505c5c0c0c5c5c0c0c4c0c4c0c3c5450f0f43c0c3c3c0d0c43074310c1c4c4c4c4c0c5c5c0c3c3c3c3d5555555555546c6e83c3e84e1380e0383e0f86e1b96543c3c4c3c5c0c0c3c3c0c0c4c0c4c0c3c3c3c3c3c3c3c3c4c3e1c0c3c5c3c3c0c3cfc3c1c3c3c3c1c4c4c4c4c0c5c5c0c3c3c3c3d5555555555550f5550f43d551513440d517542d50f541d11550f0f1b1ba0f0f83e84e1380e17031783e0f86e1b96875551b055000c4c232303032323030302c4c3f0f0b0b3f0f0b0b030b230300050501c0301c0714054555554121306c6e06c6c00e23031b82e1b81c25501c1c03130370303233700c0b1300f0b270b0f09c0c2c8c0c13078704c0704c4c0700c0701c5055455555041513004554ed0440d523542d50f541c015521301ba1b1b20388c0c6e0b86e07096875551b00c4c04c4c0317170304c1e1c0701c070705c0c0701c130700c1c1c17030309c1c1c0f070701c1c5155550544541513040d517542d50f541c0150741c101155521300e17031786e1b81c20707206e96875551b01c4c02c4c170b170b0000c0701c07145555410544c117545d50b543d5070055484c171785e170b86e07096875551b0707050171703031717030300c4c3f0f0b0b3f0f0b0b02c4c030b170305050001c0301c074505145555411b1b01313821300e0382e1b81c259501c1c4c4c5c0304c0c4c0c0c031302c3c1303c2c9c0b1300c2c5c0c133b04c0704c1e1c071705c0c0701d4454515555051341011541513040d517542d50f541c015513131b1b204e13a21300e17031782e1b81c25a1d5546c03130131300c8c8c0c000700c0701c15400c0c8c8c8c8c0c0c9c2d6c3d6c3c9c2c1c1c01451555504151484c0388c0c6e1b86e07081c1e06c6c155403130131300c8c8c0c0701c13078701c0301c070ec1c0c0c07072f00c1c9c07070f01c07071455554115541d1f10544c103548d50b543d507005045541d045484c0388c0c6e1b86e070807a071b25a1d5546cac0cac0c3c2c3c2c0c2c3c0c1c1c1c1c0c1c1c0c1c3c1e1c1c1c1c1c1cec1c1c1c4c1c1c0c0c1c1c1cac0c0c1c3c1c1c1c1d5555555555551513440d52b542d50f541d1150741d550742d5551b86e038ac0c6e0b83e0781e0707a071ba5a1d5546c032b00fc4cfc4c00c0cac8cac8c0c0c0b0f00c2c3c0c1c1d554000700c14140701c51551415550486c038ac0c6e1b1b00f0f80b83e0709654032b00f04c0f0ec030f2b03c0c0c0b0f00c2c3c0c1c1c1c000700c0f2703c1c1c1c3c1e1c5155445555041513040d52b543d04045542d50f541c015521b00e2b031b83c3c6c6c80f83e82e0f81c25a1d5546cdc0cdc0c2c2c2c2c0c2c2c0c2c0b0b0b130b00c0c2c2c2cdc0c0d50b0b0b0b030b0b030b0b0b0b0b02c1c2c0b0755555555555551b86e0380e0b0b82c6e0b0ba0b1ba0b82e550000030b0b03000000dc003002c00b000000000155544004004000e0382e0b81b00206c0154dc0cdc0c9c9c0c9cdc0c0cdcdc0c9c9d555555553b544d50354dd5543d50755551b86e038dc0c6e1b86e1b86e5a1d5546c2a80030300c0c0c0c0c0c0c0c0f0f2a83c3e80c0c0c0c0008c1c08c1c0300c0f03c44c0f0f41b1b00340c0c0d0f43d1f04a01626aaaa09a4230f00c0c00c0c0c0c0c030f130f870f0f03c3c3c3c0c0c0c0c000f01c3f01c0300c0f03c44c03d43c7c40d03030343d0f47c1282aa2aaaa825a1e942a13008aa83e0880ea03a82ea0fa81c02a1b95130b8a80303030303030303030303030f2a283c3e0f030303034310c1d0c430713131313030303030f0f0f0f1b1b50f0f51344d0340d0f43d1f47da9a5aaaaaaaa5a50f0f130303030303030303030303030f0f0f0f0f0f0f0f130f870303030303030f3f0f070f0f0f0713131313030303030f0f0f0f0f0f1f1f50f0f43d44d1340d03030343d0f47d1f6aaaaaaaaaaa9687a583eaa83e0faa8a84e203a80ea0ba83ea0788a86e542a80030300c0c0c0c0c0c0c0c0b1308c3c2c2c8c3c2c2c0c0c0c0c0028280300c0701c44c1f1b41b1b00340c0c0d0b47d0704a01626aaaa09a4070700c0c00c0c0c0c0c0302c4c03c2c9c2c3c230303030304c1e1c1301c131300c0301c0711301f51f1f10340c0c0d0b47d0704a0aa8aaaaa09687a50a84c022aa2382203a80ea0ba83ea0700a86e5403030131300c0c0c0c13078701c0700c0c030301c0704c1c03030300c0c0c27070703c1c1c070711300d03030347d1f41c10707107d4a2aaaa0a88a9687a50a84c203a80ea0ba83ea0700a81e070808aa86e54070300b1305c2c5c2c000300c0701c44c171745d170b47d0704a2aaaa09687a50a84c217a85ea0ba83ea0700a86e541c1c2800c0c0c0c0c0c0c0c03030fc3c2c2cfc3c2c2c0b1300c0c0c0c2828000300c0701c6c6c04c4d044c0340d0b47d07062414a2aaaa09694070703130300c030303030300c0c0b0f04c0f0b2702c4c0303030304c8c1301c13078700c0c030301c0713131f1f104d13511300d03030342d1f41c1a22a28aaaa825a1e961382022a82a13080ea03a82ea0fa81c02a1b9500c0c04c4c030303030000c0301c070aa00303030303030303230b230f230f230b070700a11300d03030347d1f41c1070741b1b028aaaa8205896a900c0c04c4c0303030301c0704c1e1c0300c0701c2307030300c0c0c03072701c1c3c0701c1c44c0340c0c0d1f47d0704075071f128aaaa822aa81e1b25a1e942a13080ea03a82ea0fa81c02822aa078221b95030303030f0b0f0b030303030707070703030303070f07870707070707230707071307070303030303030303070f070707071f47d0340c0c0d0b43d0741d07075071f5aaaaaaaaaaaa5a1e962a13880ea03a82ea0fa81e22a0781eaa0782eaa1b9500c0c03f133f130030303030303030302c3c030303030707aaa0000c030a0a01c0711f00d03030346c6c03c3d02d0f41c128aa8905aa825a500c0c03c1303c2300c0c0c03030302c3c030303030707070000c0303c9c0f0707070f078711f00d03030343c3c7c7c40f43d42d0f41c128aaa22aaa825a1e942a13080ea03a83e0808aa82ea0fa81c02a1b95 25 33554431 10 1023
def hc_60_4 : Nat → Nat := unpackHintV5 0xf00336e8c1d0e2b184db41dcd399eac8a2bec44118bcd9dab102f6aa69a6a331ce9d51789679b69019988851f28179b67722967191646b499262b226572ae24e1a444a190041c21635531c2f09922739f41e523a1719ce0d42760701900001c0 0x32b003c4c3c3c00c0c3cac3c3c0c0c0b0b00c2c2c0d502c1302c2300c2c8c0b030302c02c3c2c3c0b00b0f0b02c2c2c0b0b0b0001c03007070070701c072847c0347d0b0b0b0b0b542d870b1f102d41c121b00e0383c6e83c3e82e0b81c1c1c1c1ca07a1d86d00c02c030b0306c1304c3b00c6c1b030306c2c3c0f0b0001c0301c072800c0c2c2c6c7c41b1b41c01c86c0380e0b86e0707070707281e871b86e0000000303030303030303000aa0f0fa03030303000000000000431f4350c7d0d030303030b0f0f0b00000000aaaa00aa000000300c002e1c0003c0c0c0c0c000000000000041f0030303030b0f0f0b00000220aaaa20021ea80002130000a080203a80ea0ba83e829a87e4000c0c02e0b0b00c0c0c0c283c3c00c0c0c0c0c0c0c0c2aa0000300c0701c01c1c01c1c131300c0c0c0c2c2c2c2ccc7d0d331f4341c01ca2aaaa82a20aa80303002e1c2c2c00c0c0c0c0c0c2c3c2c0c0c0c0c0c0c0c0c00000c0301c07007070070704c4c030303030b0b0b0b0b0b0b42c7c2d0700728aaaaaaaaa00a1ea82a13080ea03a82e0ba82e0fa82e0baa82eaa81e9a87e400000000000030303030000030303030b0b0b0b021c2000aaaaaa0800203aaaa0ba6a400b0b0a0030303030303030300c0c0a8a02e00c0c0c0c01c1c01c1c000300c0701d0c7d0d431f434131300c0c0c0c2c3c3c2c1c01ea280a2aaaa0aa82c2c2c0c0c0c0c0c0c0c0c03030000b0b00b8703030303030303c07070070707070000c0301c070f1f0f43c3c3d04c4c030303030b0f0f0b0700783e1baaaa28aaaaa00a1eaa0faaa0f83ea823ba84e13080ea03a82ea83e0fa81e9a87e40000000b8700c0c0c0c00000c0c0c0c0c0c0c0c2c2eaa80000000000000c0c0c0c2c2c2c2ccc7d0d331f4340002aaa80000800872a8000002e1c0c0c0c0c000c003002c000000000000030303030b0b0b0b0107c00002aaa8088080087aa000080ea03a82ea0ba000a080029a87e40000000030303030303030300430f330b430f330b030303030000000000000a5131350340d1f47d00000000aaaa0069000000300c00000b03c00c0c0c0c0000000000187000130340d1f47d00000220aaaa20021da40000002820080ea03a8cea0fa096a1f50003030131300c0c0c0c000300c0701c51555504284c4c00c0c0c0c0c0c0c0c8c2c8c3c8c3c8c2c1c1c0141550a2aaaa0555415003030131300c0c0c0c000300c0701c1875055035550513503540d50b543d50700500a2aaaa802875556650a84c203a80ea33a83ea07955561f5555a595405090030303030303030300c0c430f330b430f330b04c4c0303030300707007070000c0301c070585180340d1f47d0706a280a2aaaa09a55030303030303030300c0c130f130b130f130b04c4c0303030300707007070000c0301c0700141870340c0c0d1f47d07061386eaaa8a2aaaa802876984eaa84e13aa0a84c203a80ea33a83ea07966a1f87d40000003030303000000000555500000003030303030303033f0b3f0f3f0f3f0b0000555500aaaa20021c55000000000303030300000000061d555400000c003002c00f000001002aaa880087550220000080ea03a8cea0fa0955540028200000c0c0c0c2c2c2c2c0c0c0c0d0c431343134300c0c0c0c0c0c0c0d6aa41c1c1c1c0c0c0c0c1c1c1c1c1c07070701c1c7d1f40d03642c2c2da50f0f50741daaaaaaa8a8aa69030303030b0b0b0b030303030b02c2c2c4c2c0303030303030303541c1c1c1c0c0c0c0c1c1c1c1c1c07070701c1c7d1f40d0350b61c2c2d42c2c3c1d076aaaaaaaaaaaa07a1da623a84ea03a80ea0ba82ea0b82eaa0baaa0796a1f5a80c0c0c0c3c2c3c2c0c0c0c0c1c1c1c1c0c0c0c0c1c1c1c1d55550b61d55551513440d503543d41d1155aaaaaaaa81e875556658eea13a80ea03a82ea0fa81e555587d5556963355a800000c0c0c0c000000000d0342d90000aaaa021c2069000aa03aa82e09a87d000c0c0c0d0c431343134300c0c0c0c0c0c0c0c3c2c3c2c0c0c0c0d6a681c1c1c1c0c0c0c0c1c07070701c1c1c1c1c1c7d1f40d0342c2d6942d90741daaaaa8a8aaaa69030303030f03c4c3c3c3c03030303030303030f0b0f0b03030303541c1c1c1c0c0c0c0c1c3c07070701c1c1c1c1c1c1c1c7d1f40d0342c2c2c2c2d50b61c1d076aaaa0f86eaaaaaaaa07a1da623a84ea03a80ea0faaa0f83eaa0ba83ea07966a1f87d6a373737370b0b0b0b030b030307070707070707070707070755555555aaaaaaaa81e875588ea13a8dea23a82ea0ba81e5555a80c0c0c0c2c2c2c2c0c0c0c0c1c1c1c1c0c0c0c0c1c1c1c1d5555542d553f0fc4cfc4cfc03030303030303030b0baaa07074455555aaaaaaaa81e8755561500c0c0c0c2c2c2c2c0c0c0c0c1c1c1c1c0c0c0c0c1c1c1c1d5555550b61d551513440d03540d542d41d1155aaaaaaaa81e875556658eea13a80ea03a82ea0ba81e5555555a5956a0b0b0b0303030300c0c0b0f0b00b0b802e1c0c0c0c0c0c0c070701c1c000300c0701c3c3c3c3c131300c0c0c0c2c2c2c2c1c01eaa8a2aaa20aa80c0c0c0c2c2c2c2c2c0c0c0c0c2c0b0b0b130b00c0c0c0c0c0c0c0ea07070707030303030707070707070701c1c1c070733333333030303030b0b0b0b0b0b0b42c7c2d07070707aaaaaaaaaa8aaaa03030303030303030707070703030303070707070303030307070707aaaaaaaa81e87aa8eea13a80ea03aaa0fa81e9a87e6a055000c4c232303032323030303c3c550f0f5030f0f0300043070430708c0303c0f14054555554121303c3e06c6c00e23031b83e0f86c255 24 16777215 10 1023
def hc_60_5 : Nat → Nat := unpackHintV5 0xea6950e3f99cde496cd5e21ace29eec759b4bd1a90b571eaafd168a901b49f72649f081a9e28389719c48d4a74840a50750bc06c0242638220599a7a5052524a49824349c042e8183c31ae32da562c01b6217aa2138b7c095a8c08e81c00023a 0xc0c0c0c0000000155540000000c0c0c0c0c0c0c0c2c2c8c3c8c3c2c2c0000000002aaa80155695400000c0c0c0c00000008710550355400140d503542d50f500000002aaa828700555665000000c00300cc00f000404044004002000000c0c0c0c0c0c0c0c010c3c2c2d0c3c2c2c000c0c0c0c00000000000000000d0342d1f402aaa802aaa8001a44030303030303030300130f0b0b130f0b0b0003030303000000000000040870340c0c0d0b47d00aaaa00aaaa0a1c01a4130001304c00000003000c033003c001007c0800c0c02c2c030303030000c0301c07145542d8755410544c103540d50b50700554a2aaaa07a1ca95559943b204ca03280ca0b282c80b94545544163310a80303010c4d0c4c00c0c0c0c0c0c0c0c0b0b00c0c0c0d4260000300c01c1c01c1c0701c47c0340d0b0b0a40b641c128aaaaaaaa81c29a40303003c4c3c3c00c0c0c0c0c0c0c0c0b0b00c0c0c0d50000c0302c01c1c01c3c1c1c0701c47c0340d0b0b0b0b0b542d870704a2aaaaaaaa07a1ca9a423204ca03280ca0f8820f83c820b282c80b94a1f1a8030300b0b00c0c0c0c02c2c2c4c00c0c0c0c0c0c0c0c00000c0300700700707007070cccc030303030b0b0b0b0b0b0b42c7c2d0700728aaaaaaaaa82aa00c0c02c030303030000c0301c070030303030b0b0700728aaaa81e872aaa0ec813280ca0328a0f206e9287c6a0000003030303000000000000000b0b2b0f2b0f0b0b000000030303030b2b2b0b00571f3755c7cdd000380e0380e000303a0303a0380e00c00003021c4c3c2c2c4c3c2c2c000c0c0c0c001304c001300000003000c00f014c00000000000131f1344c4c4d00030303030b2b2b0b07c004000c0e80c0e8000e0380e03800c002870380e50c7e1c3c01d1f43871b8000000c2c2c2c3c0c00000000000c0c5c5c5c5c0c0c00000000000c5c5c0c2c2c2c2c007d0d1f434000e0382e0b8000a1c1c1e83c1e86e1b80b03c5c0c0c3c3c0c0c000002c087030b0b0b0f030003c0f0003c0000005c003002c00b0000000000003c7c3d0f0f0f4000c5c5c0c2c2c2c2c1f001000f1ba0f0fa000380e0b82e007000a1c6e1b8030300b0b00c0c0c0c000300c0700c05c4c5c4c000c0c0c0c0c0030303030301c1c000c0c171700c0c0c0c2c2c2c2c1c01d5c7cdd571f37480c030380c0e0380e03080c0e80c0e80e03803c4c3c3c0030300c2c0c0b0b0b0f00c0c0c0c0c0c2c0c0c0e1c0b04c0b08c0b00b0f0b0f02c02c3c2c03030300c0c0c0b0b0b0b0f02c2c2c2c0001c1c01c1c0300c0701ca05c5c0f1f0f43c3c3d0303030357030b0b0b0b0b1f102c2d0700720300c0e80c0e80c0e030380e0380c1c0c0c1ca03a1c0e03800c0c00b1700c0c0c0c0000c00c0701c05c4c5c4c000b0b230f2b0f0b0b030300030305c5c030303030b2b230b07007231f2348c7c8d20300c0e030380e0380c20303a0303a0380e00f0f000c0c030b030000700300c0302c2c2c4c0b0f0b0303030303030700305c5c0f0f43c3d030303033303070070b0b0b0b20300c0e030380c0e030380c20380e0380e017131713000c0c0c8c030b0302c2c0303003030300c0c2c0c0c0c0001c1c00c0c030700c0c0700c171708c7c8d231f2340c0c0c0c8c0c2c2c2c2c1c01c80c0303a0303a030380c0e0380e03080e0380353002c2c00c2c2c2c0c000700c01c01c02c2c2c4c00c0c2c2c2c0c0c007070007070cccc033333030b0b330b0b0b070070b0b0b42c7c2d21b00e0382c2e0b1b81c20707a0b07a1b86e0000030b1703000000000003031717171703030b0b230f230f0b0b00000005517554000000000e0382e1b8001c1d5555400000c2c5c0c0000017000c00f00cc0000000021c41545d551001000503545d50b543d41000005000000000e0382e1b801c00287555646d42c3c2c00000c2c5c0c00000000000c0c5c5c5c5c0c0c2c2c3d7c3c2c2c00000000d17171742d1f4000000000e0382e1b80001c1e84c1e986d104c5c0c0c4c4c0c0c004c3c2c2c4c3c2c2c000c2c5c0c001304c001300000017000c00f00cc0000000000000040870345c5c5d0b47d07c004004c6e84c4e8000e0382e1b801c0028761b4030300b1700c0c0c0c000300c0701c05c4c5c4c000c0c0c0c0c0b0b2b0f2b0f0b0b500514555541450520300e0380e0380c203035555500c0c02c5c0303030306c1304c2300c0c0c03030306c2c3c0f0b330000c0301c0728545c40d87555546d1f1155410544c10350b543d51b41011550741c0115520300e0380e0380c1c0c0c1ca03a1d65556940c6d405c4c5c4c003031502c5c1f0f0b0b1f0f0b0b03030303570306c1304c2306c06c7c6c7c1b01b1f1b3700c0c0c03030306c2c3c0f0b3300007070070700c0301c072845c5c5c0303030303540d870b47d1b1b1f1f106d1b5070480c0303a0303a0380e0380e0307030307280e87680d8032b00b0b00c2c2c0c0b04c0b0ec030b2b02c0c0c0b0b0b0b0f02c2c2c2ccc000700c0701ca145542d87555115410544c10354ad50b50b4cc101155070055486c0380e0b82e0707070707281e87555646d41321e1c032b00b0b00c2c2c0c000700c0701c04dcc4c00c0cac8cac8c0c0c142d0b01c1c001c1c47c0347d0b0b50b42d8707042c2c02c2d086c0380e0b82e07072207a1c1c1e83c1e986d 24 16777215 10 1023
def hc_60_6 : Nat → Nat := unpackHintV5 0x82a87c9fb01f47a4c8e9ddf1687378809be51f26c5c671a7214a66a4649909140618454177b1cc5a5c72155f27051188c92663c04408b2103319e3c40918e301c033e49b8bfe1f62908de09a713623c45b07e621619acbd852e27a0c810701df282048c5e0000246 0x30300b0f00c0c0c0c000300c0b02c551361d5555041f503140c50b143c407102c5528aaaa83e87825516610a84c20385ea03aa1ba0700a5555045a5812a030303030b0b0b0b030303030707070703030303070707075555555541d874fc3f133f133f00c0c0c0c0c0c0c0c2c2d5541c1e2291552aaaaa82daa555a55030303030b0b0b0b030303030707070703030303070707075555555541d874ed513540d503542d50b541d56aaaaaa0ba1ea95559962a13880e2fa80ea82e81e22955555569655a80c0c0c0c3c2c3c2c0c0c0c0c2c5c2c5c0c0c0c0c2c2c2c2c5c5c5c5c0c0c0c0c2c3c3c2cbc2c2cbeaaaaaaaaa8030300b0b00c0c0c0c0b078701c0700c0c030301c0702c1c03030300c0c0c0b070702c1c1c070704c4c030303030b0b0b0b070070707107c1d28aaaa82a22aaa00c0c02c2c0303030301c0702c1e1c0300c0701c0b07030300c0c0c03070b01c1c2c0701c1c131300c0c0c0c2c2c2c2c1c01c070741c7c4a2aaaa08aa8aa80c0c0c0c3c2c3c2c0c0c0c0c2c4c2c4c0c0c0c0c2c2c2c2d1361d55540d555544d40d503542d50f541d50b556aaaaa6a9555994030300b0f00c0c0c0c000300c0b02c551361d5555041f503140c50b143c407102c5528aaa982551661030303030b0b0b0b030303030707070703030303070707075555555541d8748d513540d503542d50b541d56aaaaa6a95559940c0c0c0c3c2c3c2c0c0c0c0c2c2c0c0c0c0c2c2c2c2ccccc0c0c0c0c2c3c3c2ccc2c2eaaaaaaaaa800000c0c0c0c0000003000c007002c00000000b00000c0c0c0c2c2c2c2c1f0010cc0002aaa8800800aa80c0c0c0c3c2c3c2c0c0c0c0c2c2c0c0c0c0c2c2c2c2ccccc0c0c0c0c2c3c3c2ccc2c2eaaaaaa0fa1eaaaa3ba84ea03aa03aa1ba07aaa6a1f9a8000000ac8c0c0cac8c0c0c001c1c1c1c3c3c1c1c0c2c3c0c000000000000fc7cfd3f1f3f40cacac0c2c3c3c2c000000000e0382e0f8006e1b8000000c2b000b870000f030b0f03000000000000000000707007000303070707230303070b0707070f07070800041f0032b2b030b0f0f0b0007070741c7c1d000206c00e0382e0f808702006e1b82c2c01c1c05c5c0c0c5c5c0c0c0313001c1c1c070702c1c030b0f03007828000700c0701cfc7cfd3f1f3f4131300c5c5c0c2c3c3c2c1c01c283ca21300e0382e0f81c8a1b86e0b0b0b0f1703030f0f030300c4c0002c2c02e1c0c2c5c3c3c0c01c1c01c1c000700c0701c1c3c1c1c1c1c1c1c3c1c3c1c1c1c1c01c1c1c4c00c0c1c1c1c5c0c0c1c2c1c1c1c3c1c1ea0f1f0f43c3c3d04c4c031717030b0f0f0b0700707070741c7c1d0f0f1b1ba0f0f83e884c0380e0b83e0a1c2801b86e2f032f030b0b0b0b030b0b030b02c2c2c4c2c03030b0b0b2f030307070707070707030707030707070707070701e0728cccccccc0cbcbc0c2c2c2c2c2c2c2d0b1f0b41c1c1c1c6e1b80e0382c2e0b1b82ca0b1ba0781e1b86e00002f2303032f230303003f0f270b3f0f270b0003272f0300000000000707513135000347d1f47d000000000380e1b86e0061b4000000c2f000002c0f003272f0300000000000000000070700700030307070723030307330707070f070708187000130347d1f47d0007075071f5000206c00e0386e1b8087020186d00c4c04c4c0317170300707131300303171717170303230b230f230f230b0001c0301c070a0514551755541510484c0380e1b86e4505425500c4c04c4c031717030001c0301c070070707130030307070717030307330707070f0707a818750551755505555513503545d50b543d50700541d075541d550084c0380e1b86e0a1c280555646d4141d000c4c171703031717030304c4c3f0f270b3f0f270b03171703000078280700c0701c41c0507140d17171747d1f41c12130284ca0380e1b86e070986d544c5c0c0c4c4c0c0c031304c3c4c2c4c3c4c2c131300c5c5c0c01c1c01c1c000700c0701c1c4c1c1c1c1c1c1c4c1c4c1c1c1c1c01c1c1c4c00c0c1c1c1c5c0c0c1ccc1c1c1c3c1c1ea00141870345c5c5d1f47d07041c1d41c7d44c4c6c6e84c4e13a21300e0386e1b82870a0186d0000030b0b03000000000030707072303070707070b0700700555500555000380e0b82e002015400000c9cbc0c00000c0cbc8cbc8c0c0c9c2cfc3cfc3c9c2c0000000000015555555400000e0386e1b800000015400000c9cbc0c00000000000c0c1c1c1c8c0c0c1ccc1c1c1c3c1c1c200061d5554015554000c02f002c00f0001c00001c070001c0010000e0386e1b8087020154081b02b032b030f0b0f0b030b0f03070707070307070307070707073b07070713070703030707072b0303070b0707070f0707a955550b61d555555551513440d52b543d41d1150741d55074cd5551b86e0380e0b83e81e870707a07070b555646d4ac0cac0c3c2c3c2c0c2c3c0cfc3f133f133f00c0cac8cac8c0c0c1c1d41d07070707070703070703070707070701e07287d1f40d1f42d0742c2d41c1d41d0746e1b80e0382e0f82ca0f281e81e986d2b032b030f03c4c3c3c3c03030f2b0f0f03030f0b0f0b030b0f03541c1c1c1c0c1c1c0c1c07070701c1c1c1c1c1c1c8c1c1c1c4c1c1c0c0c1c1c1c8c0c0c1c3c1c1c1c1c1c1c3c1c3c1c1c1c1c1c2c1c1c1c3c1c1ea1f47d0347d0b0b0b0b0b542d870741d07075071f51b86e0380e0f0f1b1ba0f0f83e82e0fa07a1c1c1e81c1c2d86d2f032f03272703272f03070707070307070307070707073b07070713070703030707072f0303070707070f0707a80cbcbc0c9c9c1c1c1c1c1c1c1d071f0746e1b80e0386e1ba07a1c1c1e81c1c6c6e1b800000c0c0c0c0c0c0c0c000000000c0c0c0c00000000010c7d0d431f434000c0c0c0c2c2c2c2c02aaa802aaa8002a80b00c0c0c0c0c0c0c0c000002c087030303030303000003c070000000f1f0f43c3c3d00030303030b0b0b0b00aaaa00aaaa0a1c02a80f0000f03c00000003000c00b002c001007c08 26 67108863 11 2047
def hc_60_7 : Nat → Nat := unpackHintV5 0x8e689d21c73a6829c901ebe3d278005f1cfb20a6d4cd41a3e22a6320bb18bf01262b009976129655610494831aa4cb4ab11f027a3f89070f081b43700a40db201c32548e8afa33629e840096f2161f84c706b02621528b304382240b94a981f91d803409480001a0 0xc4c02c2c030b0b03007070f07003031717171703030a0b82c02c01301c5c0b0301c07007070070704c4c031717030b0b0b0b1f3f5ac7cfd0700721300e0382c2e82e0ba1c2c2c02c2e01c21b86e01c1c2c2c5c0302c0c2c0c0c031302c2c3c3c02c00b02c2c3c03c4c3c3c00c0c3c5c3c3c0c0c2c2c0b02c2c2c0b0b00c2c2c0ea02c2c0b01c13078701c5c0b03007070070701c070b1f102c2d04c4c031717030f1f0f43c3c3d0b0b0b0b070070b1b202e884c0380e0b0b0b0b0ba82e8707086e1b8031300b0f00c2c3c0c03c3c3c3c00c0cac8cac8c0c0c281e070000700c0701c01c1c01c1c131300cacac0c2c3c3c2d6c7d6d5b1f5b41c01c84c0380e0b81e0b0b00707807086e1b80313003c4c3c3c00c0c3c8c3c3c0c0c0b0f00c2c3c0ea01c0704c1e1c0700c0f0070700707070701c0702c1c0c0c07072b00c1c3c1c070070f070f01c01c2c1c9c07070f070f01c070704c4c032b2b030f1f0f43c3c3d0b0f0f0b0700701c1d071f121300e0382c2c2c2c2ea0ba1c1c201e07a07071b1b21b86e0000030b0b03000000c02b001c0800000ac000b00000032b2b030b0b0b0b0107c000000380e0b82e0206c01b001b86e00c4c03c3c030f0f0300f0f0f0f003032b232b2303030a0f83c000ac0303c0f06f0706f0711300d1f43d0f44c4d43c3d47c121300e0383e0f86c2c06c2e06c261b4500c4c07c0c0c7cac0300f130f0f000f03c7c3c3c3c3c3c03c03030f230f0f030303c3c03c3c2c3c3c0b030f0f03a8000b01c0b01c2b00c03c1c03c1c0f03d1361c4c4c44c4c4c0d1f43c3c7c7d43c3d0f50f43d1f0484c06e86c6c80e0383c3c6c3c3ea0fa1c6c261b44c0c4c0c3c3c3c3c0c3c3c0c3c13130f0f0f00c0c5c5c5c5c0c0d69544c4c4c4c0c5c5c0c3c3c3c3c8c23072308c1d135555175555151544e1380e0383e61b0b5551b86e55130313030f03c4c3c3c3c03030f170f0f03030f0f0f0f030f0f03a84c4c4c4c0c5c5c0c3c0f070f03c1c3c3c3c3d1361d55545d5555555544d40d517543d5543d0f5542d50f541d50b5544e1380e0383c3c6c3c3ea0fa1c6e1b955591b5075f01d7c47e1b130313030f0f0f0f030f0f030f143d0f00c0c5c5c5c5c0c0c3c2e83e0f0b13131313031717030f0f0f0f17c1d7c07131343d130345c5c5d0f43d1f143c51f47d1384e0380e0f0f83e0f1b0ba130ba1b86e61b551317030313130303130313030f0f0f0f0f130f130f0f0f0f0f130f0f03c4c3c3c3c03030f170f0f03030f0f0f0b0f0f0f0b0f0f0f0f030f0f03a84c2c4c1c4c2c4c1c4c4c4c4c0c5c5c0c3c0f070f03c1c3c3c3c3c4c4c7c4c4d51361c0d17171743c7d43c3d43d0f47d1f44c6e84c4e84e1380e0383c3c6c3c3ea0fa1c6e1b986d00c4c03c3c030f0f0300f0f0f0f003032b232b2303030a54000ac0303c0f043070430714555555554121300e0383e61b0b0541b09540313003c4c3c3c00c0c3c8c3c3c0c0c0f0f00c3c3c0ea000ac0300f0700f0703c0f1544d875543d1f5555554107d40c52b143d1043d0f1042d27143d0f101c40b15484c0380e0f0f1b0f0fa83e871b095456946c6c4ac0cac0c3c2c3c2c0c2c3c0cfc3f133f133f00c0cac8cac8c0c0c1c1e81e07070707070703070703070707070701d07147d1f40d1f42d0f42c50f141d41d46e1b80e0382e0782c2e81c1e81e07986d2b032b030f03c4c3c3c3c03030f230f0f03030f0b0f0b030b0f03a81c1c1c1c0c1c1c0c1c07070701c1c1c1c1c1c1cec1c1c1c4c1c1c0c0c1c1c1cac0c0c1c3c1c1c1c1c1c1c3c1c3c1c1c1c1c1c2c1c1c1c3c1c1d51f47d0347d0f0f1f1f50f0f43d42d0f50761c1c1d41c1c2c6e1b80e0382c2c2c2c2ea0ba1c1e0781c1e81c6e986d00cac02c2c030b0b03043134313003032b232b2303030a540001c0301c070070700707145555555541c1486c0380e0b982c2c1501c25500cac00f130f0f003030f2b0f0f030302c2c030b0b03a8000700c0b007070070f070701c07145555555541d87150ec413140c52b143d1043d0f1042c50b102d5486c0380e0b0b0b0b0ba82e87070954591b104c878700cac02c2c030b0b030001c0301c070136b13003032b232b2303030a0b82c070700070711f00d1f42d0b41c1c441d87070750f07521b00e0382c2e82e0ba1c1c20b0b00b0b861b4032b003c4c3c3c00c0c3c8c3c3c0c0c0b0b00c2c2c0ea02c1302c3b00c2cac0b030302c02c3c2c3c0b00b0f0b02c2c2c0b0b0b0001c03007070070701c071447c0347d0f1f50f0f50b42d0707070707141d8721b00e0382c2c2c2c2ea0ba1c2c6c80ba070986d0000030b0b03000000005555021c10000552b5542d040000380e0b980155546d2b032b030f0b0f0b030b0f034310c4d0c4d0c03032b232b2303035a550707070703070703070707070701c1c1c07075555555454551b86e0380e0b982c2d5541e07954ac0cac0c3c0f130f0f0f00c0c3cac3c3c0c0c3c2c3c2c0c2c3c0ea0707070703070703070f01c1c1c0707070707070707555543d1f5555555541d874ed513540d52b543d5543d0f5542d50f541d546e1b80e0382c2c2c2c2ea0ba1c1e0795556946c6d4ac0cac0c3c3c3c4c3c3c3cec0c0c3cac3c3c0c0c3c3c3c3c0c3c3c0ea032b2b030f0f070f0f0f070f0f0f0f032b2b030f1f0f43c3c3d0f0f0f0f1b86e0380e0f0f1b0f0fa83e871b86e1b86e00c0c02c2c0303030302c1e1c0701c030300c0c0701c0b0700c0c0c03030302c1c1c0b070701c1c131300c0c0c0c2c2c2c2c1c01c1c1c41f074a2aaaa0ba1e0a88aaa82a13080e17a80ea82e81e07008a81e070808aa9a87e6a00c0c02c2c0303030301c0702c1e1c00c0301c070aa003030303030303030b0b00701c1c1c1c028131300c0c0c0c2c2c2c2c1c01ccc7cfd331f3f4a2aaaa0ba1e820a8aaa00c0c02c2c0303030301c0702c1e1c0300c0701c0b07030300c0c0c03070b01c1c2c0701c1c131300c0c0c0c2c2c2c2c1c01c070741c7c4a2aaaa0ba1e08aa8aa82a13080e17a80ea82e81c02822aa078226a1f9a80c0c0c0c3c2c3c2c0c0c0c0c2c4c2c4c0c0c0c0c2c2c2c2d555555556284c4e00c0c0c0c0c0c0c0c2c2d5548c1c2c0b08c1d1552aaaaa6a95569540c0c0c0c3c2c3c2c0c0c0c0c2c4c2c4c0c0c0c0c2c2c2c2d1361d55540d555544d40d503542d50f541d50b556aaaaaa0fa1ea95559962a13880e17a80ea86e81e22955561f5555a5956a00c0c02c3c030303030000c0302c0b1544d8715555042a800c0c0c0c0c0c0c0c2c2c114fc1c00fc1d5554a2aaaa0fa1d82550a45 26 67108863 11 2047
def hc_60_8 : Nat → Nat := unpackHintV5 0x8f191da2e71be88d45921252207ebcbb1ed21ba7634a29c8021a6bc8c719df22661b8b897352725790a8948b2b24f146312502ea43d4ad8fbf26c3a7c900d1c30630787f0aa32f626b07b886628c1d109106a3142176c6404bb2400bbce6012439600348b800001a 0xd5c0c0c0c0c2c2c2c2c0c0c0c0c2c0b0b0b130b00c0c0c0c0c0c0c0ea070707070b070303038703070303070707070701c1c1c0707073b070707130707030307070b0707070b0707070b070b07070707070b070707070703030333171737030303030b0b0b0b0b0b0b42c7c2d0707070707070741c7c1d0380e0380e80e87030ba030b030380e0303a0303a0380e00000030303030b030000000c0c1c1c0c0c0c0c00000000000000c0c0c0c2c2c2c2c8c7c8d231f23400000e0380e0380c0e80c0e8000e0380000000000c000c2c2c0c07002000000000b00033f330307c0042c2c2c2c00000e0380f0020b82e06c006e1b84c0c4c0c4c131313130b00c0c5c5c5c5c0c0c3c2c3c2c0c2c3c0d69542c4c2c4c0c5c2c0c2c23070b08c1c2c2c2c2d55545d545455551384e0380e550f0f560f86e0b9544c0c4c0c3c2c3c2c0c2c3c0c4c0b1313130b00c0c2c5c5c5c0c0ea0b130b1303170b030b0b0b0b0b02c1c2c0b0744d8755551755555555513503545d50b543d50b42d551b55507542d551384e0380e83e870f0fa0f0f0f1b82e555646d40313002c2c4c2c00c0cdc8cdc8c0c0c0b0f00c2c3c0c2914003700c10c1c10c1c0b02c51555555550484c0380e540f0f060f0f0f86c25500c4c02c3c030b0f0300b131313003030b1b1b230303a8003700c0b02c02c1c02c1c551361d55555555041f50314dc50b42c50f43c50b42c411b44007102c5521300e03a0fa1c3c3e83c3c3c6c2551646c40c0c0c0d0c171317134300c0c0c0c0c0c0c0c3c2c3c2c0c0c0c0d69542c5c2cbc0c0c0c0c2c2f070b0bc1c2c2c2c2d55555555555540e0380e039540c0d580e0380e55030303030f0b0f0b030303031b230b1317130b1b0303030303030303a82c5c2cbc0c0c0c0c2c2c2c2c2c6c2c1c2cfc2c1d545d40d87555555546d1f5554ed513540d42d50f542d0b5546d5541d50b5540e0380e03a03a1c0c3e80c3c0c0e039655590352f032f034310c4d0c4d0c03032f232f2303030b0b0b0b030b0b035a5507070707030707030701c1c1c0707070707075555545455551b86e0380e550f0f560b0b0b81e07954bc0cbc0c2c2c2c2c0c2c2c0c2c0b0b0b130b00c0c2c2c2cbc0c0ea0707070703070703070707070701c1c1c070755555555555541d874ed513540d52f542d50b542d0b5542d5541d546e1b80e03a0ba1c2c2e82c2c3c1e07955591b503030f0b0f0b030b0f031b3b0b131b130b1b03030b1b1b0303a82c2c0c2c0c2c2c2c2c2c6c2c1c2c2c1ccccc0ccc0c2c3c3c2c2c6c6d1b1f0b4cc2c2c6e1b80e03a0fa1c3c3e83c3c3c6e0b86e1b8070700c0c00c0c0c0c0c0302c2c02c2c2c2c2c0b0303030304c1e1c0b01c0b0b00c0301c0704c4c02c2d0b1f1030303030b0b0b0b07007282aa2aa82e87aa82aa0a84c022aa0b89c2203a80ea0ba0700a9a87e6a00c0c02c3c0303030304c1e1c0701c030300c0c0701c0b0700c0c0c03030302c1c1c0f070701c1c131300c0c0c0c2c3c3c2c1c01c1c1c41f074a2aa0ba1eaa0a88aaa82a13080ea03a83e81c02a0781c2022aa6a1f9a8070300b0b02c2c2c2c000300c0701c131305c5c5c5c2c2c2c2c1c01ca2aa0ba1eaa0aa82a13085ea17a82e81c02a6a1f9a80707030b0300c030303030300c0c0b0b0b0f02c0b0b0b0b2702c2c0303030302c2c0b01c13078700c0c030301c070b1f102c2d04c4c030303030b0b0b0b07007a22a28aa82e87aa82aa82e270808aa0a84c203a80ea0ba0700a9a87e6a00c0c02c3c0303030301c0704c1e1c0300c0701c0b07030300c0c0c03070b01c1c3c0701c1c131300c0c0c0c2c3c3c2c1c01c070741c7c4a2aa0ba1eaa08aaa0786caa82a13080ea03a83e81c02822aa0789c226a1f9a8500c0c00c0c0c0c0c0303c3c03c3c2c3c3c0b030303030002c0702c0700c0303c0f44d87131311313130340d0f43d1f04a0aa8aaa0fa1eaa09a42a13008aa87e270880ea03a83e81c0296a1f5a80c0c0c0c3c3c3c3c0c0c0c0c4c4c4c4c0c0c0c0c3c3c3c3d1361d55540d555544d40d503542d50f541d50b556aaaa0fa1eaaa95559962a13880ea03a83e81e2295555556962755a950303030303030303030303030f0f0f0b0f0f0f0b0f0f0f0f03030303130b1307130b130713131313030303030f0f0f0f13131f1313544d870340c0c0d0f43d1f47daaaaaaaa83e87aaaa6984e27aa84e13aa8a84e203a80ea0fa0788a5a87d6a00c0c03c3c030303030000c0303c0f1544d8755554107d40c503142c50f101c40b154a2aa0fa1eaa095456961b10a84c203a80ea0fa0700a5555045a589c12a030303030f0b0f0b03030303070707070303030307070707073b0707071307070303030303030303070b0707070f0707547d1f40d0342d0f50761c1c1d41c1c2eaaaa0ba1eaaaaaaa9a62a13880ea03a83e81e22a0781eaa0789ea96a1f5a8030300b0b00c0c0c0c000300c0701c5155550761c543b104c503140c50b142c40b5528aa82e87aa825516610a84c203a80ea0ba0700a5555045a589c12a00c0c02c2c0303030302c1302c3b00c0c0c03030302c2c2c2c3c0b0b0b0b270000c0301c071447c0340d0b42d0707070707141d8728aa82e87aaa22a82690a84c203a80ea0ba0b89c2022aa0700a5a87d6a030303030f0b0f0b030303030707070703030303070707075555555541d874ed513540d503542d50f541d56aaaa0ba1eaaa95556961b58a84e203a80ea0fa0788a5555555a589d56a0000030303030000000c003002c007000000b00000030303030b0b0b0b07c0040002aaa8800800aa80c0c0c0c3c3c3c3c0c0c0c0c0c0c0c0c3c3c3c3c0c0c0c0c3c3c3c3eaaaa0fa1eaaaaaa3ba84ea03a80ea0fa07aaa6a1f9a8031300b0b00c2c2c0c03c3c3c3c00c0cac8cac8c0c0c282e0b0000700c0701c01c1c01c1c131300cacac0c2c2c2c2dbc7cfd6b1f3f41c01c84c0380e0b82e0b0b00b0b807086e1b8070700c4c02c0c0c2cac0300f130f0f000b02c2c3c2c2c3c3c02c03030f230f0f030302c2c02c2c2c2c2c0b030b0b03a813078702c0702c2c0700c0b007070070f070701c0704c4c02c2d0b1f1032b2b030f1f0f43c3c3d0b0b0b0b0700721300ba0b1b20380e0b0b0b0b0ba82e8707086e1b80313003c4c3c3c00c0c3c5c3c3c0c0c0b0f00c2c3c0ea04c1e1c0701c070705c0c01c1c01c1c0701c0b0700c1c1c17030303c01c1c1c1c0f00707070702c1c1c0f070701c1c131300c5c5c0c3c7c3d0f0f0f42c3c3c2c1c01c1c1c41f07484c0380e0b0b0b0b0ba82e8707081c1c81ba1b86e01c4c00f130f0f00f0f0f170f0f0f1702c2c0b0b0b0ba8000301c01c1c01c1c0701c131305c5c5c5c3c7c3d0f0f0f42c2c2c2c1c01c84c1785e0b0b0b0b0ba82e8707086e1b93f1f87 26 67108863 11 2047
def hc_60_9 : Nat → Nat := unpackHintV5 0xa40852282b1ae9ad8baa5cd1d291bcaf23821da8884b0a1381d27f90aa1f091b67718a19cb921a6cacc71a501b663fca897c826e5c8853163c1cc5320ba12e03d04488df0f6437c37dcb68cfb1f82ccce409ce2ca1e591c06272de1170e583342500594e780002ca 0x303030317171717030303031717171703030303272b2b27555555550380e0380c0c0e0380e0380e5517171717030303030380c0c5c5c5c5c7c7c7c7c0c0c0c0cac0c5c5c5c5c7c7c7c7c0c0c0c0c9cacac9c0e0380e0380e0380e0380e0380c0c0c0c0c5c0c0c0c4c0c0ea17171717030303032b030303032b030f0303171717170303030303030307032f0303272b2b2717171717030303030303030340c0c7c0d272b2b272f2f2f2f0380e80e870303a0303030380e0380e0380e00c0c02c3c030303030aa00300c0c0c0c02c2eaa8000300c0b02c08c1c08c1c131300c0c0c0c2c3c3c2c8c7c8d231f2348c08ca2aaaa82a2a0aa8030300f0b130f130f870303030303c3c0c0c03030300c2c4c4c000300c0b02c2301c3f01c131300c0c0c0c2c3c3c2c1f2348c7c48c08ca84c80e87aaaa2aa88e1b28288ea82a13080e82ea0fa08aa88e0881c02a6a1f9a82a80030300c0c0c0303002c4c230f0b0b230f0b0b03030303000a0a00c0301c0704c4c231f2348c7c8d030303030b23230b07007280a8aaaaa82aa01c1c03030030303030300c0b1300f0b270b0f08c0c0c0c0c13078704c0704c4c0300c0701c131301f2348c7c40c0c0c0c2c8c8c2c1c01ca84c2aa88e1b280e87aaaa8288ea82a13008aa88e0880e82ea0fa81c02a6a1f9a8030300b0f00c0c0c0c05c4c5c4c00c0303030300707aaa0000c0301c070a0a05c5c030303030b0f0f0b331f374cc7cdd0700728aaaaa0a8a82aa00c0c02c3c0303030308c1304c23030300c0c0c030707070000c03070f078703c1c1c0f0f05c5c030303030b0f0f0b07c9d271f1070072a17203a1eaaa8aa8a0a27aa0a84c203a0ba83e822aa278220700a9a87e6a0aa000c0c03030300c0c0131308c3c8c2c8c3c8c2c0c0c0c0c0008c1c08c1c0300c2b0bc44ca5131350340d1f47d1f04a02a2aaaaa09a4500c0c00c0c0c0c0c0304c4c03c7c9c7c3c1f030303030007c070fc0700c030ac2f44d87131311313130340d1f47d1f04a84c2aa87e1b280e87aaaa825a50a84c022aa1f82203a33a83ea0700a5a87d6a030303030f0b0f0b030303032305c4c5c4c8c03030303030303035aa90b170b23030303030b0b0b0b0b08c1c2c23071f45d0340d90f6943c3d47d0b6aaaaaaaaaaaa9a40c0c0c0c3c2c3c2c0c0c0c0c7c8c2c4c5c4c2c7c0c0c0c0c0c0c0c0d50b170b23030303030b0b0b0b0b1f0b070b3f0b071f45d0340d43d870f0f50f0f0f1f42daa17a03a1eaaaaaaa1f86eaa969623a84ea03a0ba83ea0b82eaa1faaa07a82e96a1f5a8030300b1700c0c0c0c05c4c5c4c000c0c0c0c0c0b0b230f230f0b0b0000c0301c070a0a11700d0342d1f41c1d6941c128aaaa8a0a826900c0c02c5c0303030307c1304c2300c0c0c03030307c2c3c0f0b270000c0301c071445c0340d0b47d0707070707141d872a17203a1eaaaa1f86c8aaa096942a13080e82ea0fa87e0808aa81e07008a59a87e1f5a80c0c0c0c2c2c2c2c0c0c0c0c0c0c2c0b0b0b130b00c0c0c0c0c0c0c0ea0b0b0b0b030303030b0b0b0b0b02c1c2c0b0733171733030303030b0b0b0b0b0b0b42c7c2d0b0b0b0baaaaaaaaaaaaaaa0000030303030000000c003002c00b000030000000030303030b0b0b0b07c0042f0000aaaa2002002aa030303032b17170303030317172f030303032b2b2f171737030303032b2b372f372faa17a03a1eaaaaaa37aa8eea13a80eaa0fa81eaa9a87e6a0f0f0f0f03030303030ba030303a0f0f170f0f0f0303030303030b0303030387231717230f0f0f0f030303030f0f0f0f231717230f0f0f0f030303031b030f0f0f0f2337232f0380c0c5e030fa0380e870303030380e0380e031b80e0301c1c00c0c0c4c000c03030303031b031b003003030030303030300ea02c4c03c2c9c2c3c230303030b030f030303030303230304c1e1c1301c1313003070030300c0301c0704c4c07c8d231f103030340c6c0d030303030b23230b07007203031300380e80c6c0c6c80c0c0c0c0ea03a1c0e0380c2031b80e031400c0c0c4c000c03030303031b031b003003030030303030300ea04c4c03c7c9c7c3c1f0303031b030f03030303030323030007c071dc07003070030300c030ac2744d871313113131303035031b50340d1f47d1f0480c0c4c00e03a031b031b20303030303a80e870380e03096035003030313000c0ca80b1700c0c0c2c0c3c0c0c0c0c0c0c8c0c1f04c1308c03003031b1b00c00c0c0c0c03030300c0c0c1f0b0f03c2c9c0000c1c00c0c0300c0701c511700c0d40c6d40d0342d1f41c1c1c1c1c50761c80c0c5c0303030303a80e870380e031b031b200e03a03096035031b03030313030303030303a8ac5c5c9c0c0c0c6c0c3c0c0c0c0c0c0c0c5c5cbc0c0c0c1c0c6c0c0c0c0c0c0c9cacac9c5c5cdc0c0c0d031b0340c0c0c0c9cacac9cbcdcbc0e03031780c0c0c0c0ea03a1c0e0380e0380c6e0380c0c0c0c0c5c5c5c5c0c0c0c0c5c5c5c5c0c0c0c0cacacacac5c5c5c5c0c0c0c0cacacacacbcbcbcbeaaaa03a1eaaaaaa17a84ea03a2ba83ea07a8bea6a1f9a8030303030387031300c0c4c0c0b0f00f0b0b0f0f02c0c0c0c0c02c4c4c4c006c0b170b0b1717171700b00c0c0c0c0c0c0c0ea0002c0702c0700d5c030302c0b00b0700b0704c4c07c5d17171030303030b0f0f0b0b1b1b46c7c2d2f02f203003a030320380e80e87030fa030f0303080e0380c0c2c03030300c03030300c0c0c0c0c0c0c0c0e0f0fa030b0f0b030303030b0bc1c2c2f070b130b13030303030b0b0b0b331f374cc7cdd13131313030303030b0f0f0b2f0b0b2f0303a0303a0380e0380e0380e0380e0380e03030303130303130303030303870f0f0b0b0f0f0b0b0f0b0f0b0303030313131b0b130b0b131313130b130b0b1302c4c4c4c2c0303030303030303a82c2c4c1c2c2c4c1c2c4c2c4c0c0c0c0c2c2c2c2c2c0b070b02c1c4c7c4d13131344c4c4c4c0c0c0c0c2c3c3c2c2c6c6d1b1f0b4bc2c2cbc0c4c0c6e80c0e03a0380e0380e80e87030fa030f030380e0380e2305c4c5c4c8c03030303030b030f0b0f0b0303a03030380c0c2c0c0c0c2c5c2c8c2c23070b0bc1c0c0c0c0c2c2c2c2c8c5c5c8c8c7c8d231f2340c0c0c0ccc0c2c3c3c2c8c2c2cbc0e0380c0e80c0e80c0e030380e0380e0380e038031300b0b00c2c2c0c02c2c2c4c00c0c2c2c2c5c0c0ea02c1e1c0701c070702c0c0701c01c1c01c1c0b0700c1c1c17030302c1c1c0b070702c01c1c1c1c0b00707070701c1c131300c5c5c0c2c2c2c2c2c2c2d0b1f0b41c01c1c1c41f07484c0380e82e870b0ba0b0b0f07081c1c81ba1b86e00c4c00b0b0b0b003032f232f23030302c2c030b0b030a0701e0001c03007070070701c0704c4c032f2f03331f434cc7d0d0b0b0b0b0700721300e0381c1e03c3c01e0b0b0b81c21b86e00c4c02c2c030b0b0300b0b0b13003030b0b0b230303a80701c0b078701c0301c07007070070702c1c0c0c07072f00c1c2c1c2c07070b070f01c1c2c1c2c070070b0701c0070704c4c032f2f030b0b0b0b0b0b0b42c7c2d0700701c1d071f121300e03a0ba1c2c2e82c2c3c1c201e81c6c86e1b80c0c0c0d0c171317134300c0c0c0300c0c2c2c2c2c0c0c0c0c1c1e80c0c0e07070707030303030700c0c0c0303070703073317173703030303331f374cc7cdd0b0b0b0b070707070380e0380e0303a0303a0380e0380e0380e 26 67108863 11 2047
def hc_60_10 : Nat → Nat := unpackHintV5 0xf140137374a5b5a88259d91f6c0e9bc5d9c5b2cb443564e018abb8d7513095a6e236d2262968709453f088f9dea334de42226838dd2f08a295883f89ef1aa44c9561fd0528e4834062b1f22ba8b611a88587702c82ef1920f410705344d81482a4000148 0x1d8c47e1b130313030f0f0f0f030f0f030f283e0f00c0c5c5c5c5c0c0c3c2d43d0f0b13131313031717030f0f0f0f18c1d8c071344d0345d0f0f43d0f1f0b5130b51f47d131383e130385c0c5e0f83e1b283ca1b86e61b6a1317030313130303130313030f0f0f0f0f130f130f0f0f0f0f130f0f03c4c3c3c3c03030f170f0f03030f0f0f0b0f0f0f0b0f0f0f0f030f0f03544c2c4c1c4c2c4c1c4c4c4c4c0c5c5c0c3c0f070f03c1c3c3c3c3c4c7d44c4d44d1340d1743c3c7c3c3d50f61c7d1f44c4c6c4c4ea13a1c0e17031783c6e83c3e83e0f86e1b986d0a0780031305c5c0c0c5c5c0c0c13130fc3c9c2cfc3c9c2c0c5c5c0c0001d0501c0301c071130144c50345d1f47d070481c0a07280e17031786e1b81c261b6a131703031313030300c4c130f130b130f130b04c4c0317170300707007070001c0301c070713070707070707130713070707070070707130030307070717030307270707070f0707544c4c7c7d44c4d13511300d1747d1f4187050000a0a1c0e17031786e1b81c20707a071ba61b40000005c5c0c0c5c5c0c0c010c3c2c2d0c3c2c2c0c2c5c0c000000000001555555540000000000e0382e1b801548131703031313030300130f0b0b130f0b0b00030b170300000000005555005555061c00130001304c00000003005c027003c0010002021c0e17031782e1b80154081b00b0f0b0000030b1703000000000003031717171703030b0b0f630f0b0b0000000345d0b47d00007075130750000385c0c5e0b86e00000061b48131703031313030300130f0b0b130f0b0b00030b17030004c130004c0000005c003003c0270000000000004c7d44c4d4000d1742d1f401c0018700080870385c0c5e0b86e06c0080186d0a5000c4c171703031717030304c4c430f270b430f270b0317170300007070070701c0301c071454505555412405450380e1b86e070956a131703031313030300c4c130f130b130f130b04c4c0317170300707007070001c0301c0744d1f555514555550061d135551344d541513040d517549d50f541d0000a0a1c0e17031786e1b81c25555a51b1b5a84c5c0c0c4c4c0c0c4c0c4c0c4c3c4c4c4c3c4c4c4c4c4c0c5c5c0c4c4c1c4c4c4c1c4c4c4c4c0c5c5c0c9c9c4c7c4d13131344c4c4c4c0c5c5c0c9c9c4c4c6c4c4ea13a1c0e17031786e1b86e1b86e1b800000c0c0c0c0000087001c00000c0c0c0c0c0c0c0c000700030303030b0f0f0b0007070741c7c1d000a1eaaa802aaaaa8000c003002c00f0001c000b001c070001c0b001007c080000030303030000001c087000000c0c0c0c0c0c0c0c00000000000c0c0c0c2c3c3c2c00cc7cfd331f3f4002872aaa802aaaaa800000c0c0c0c0000007021c00000c0c0c0c0c0c0c0c000700030303030b0f0f0b0007070741c7c1d000a1eaaa802aaaaa8000c003002c00f0000001c070001c001007c0800c0c02c3c0303030300b0b130b0030303030303030350890000c0302c0b023070230711300d03643c3c3da40f0f01f04a2aaaaaaaa09a4030300b0f00c0c0c0c02c4c4c4c00c0c0c0c0c0c0c0d50000c0302c0b00b0700b0711300d0350f61c3c3d43c3c3c7c12a84e87aaaaaaaa826906e80ca03282e0b283e0f282e0b2087e2001c80b25287c6a00c0c03c3c030303030000c0303c0f145543d8755410544c103540d50f50700554aa13a1eaaaa095559941ba03280ca0b283c807202c954561f1551058cc42a00c0c00f0f0f0f0030303030303030303c3c0303030350980000c03023070230703c0f11300d0347c2c2903d91f04a2aaaaaaaa09a40303003c4c3c3c00c0c0c0c0c0c0c0c0f0f00c0c0c0d50000c0300f0700f0703c0f11300d0343c3c7c3c3d50f61c7c12a84e87aa83e1baaaaaa826906e80ca03283e2083e0f2082e33283e0f201c80b259287e1f1a8131300b0f00c2c0c0c002308c0b02c51555504aa13a1eaaaa09541ba23288ca0b283c807202c94546a00c0c02c3c030303030000c0302c0b14555543d8750415400c0c0c0c0c0c0c0c2c2c228fc1c00fc1d4114aa13a1caaaa82555a5500c0c02c3c030303030000c0302c0b14555543d87410544c10340d503551f50700554aa13a1eaaaa095559941ba03280ca0b283c807202c945455441610a800000c0c0c0c00000000000c0c0c0c0c0c0c0c8c2c8c3c8c3c8c2c0000000d0347d1f4000000002aaa802aaa9a400000c0c0c0c00000000000c0c0c0c0c0c0c0c1c9c1c1c1c3c1c1c1000340d1f47d021c040000a1eaaa802aaa9a4000c003002c00f0001c00001c070001c001007c0800000303030300000000555510021c000003030303030303033f0b3f0f3f0f3f0b00000000000aaaa00555a5500000303030300000000555510021c000103540d527543d410000287aaaa005556650003000c00b003c0000040404400400200303002c2c00c0c0c0c0c0c02c2c2c3c00c0c0c0c0c0c0c0c00000c0300b00b00b0700b0704c4c030303030b0b0b0b330b0b0b0b42c7c2d0b00b28aaaaaaaaa82aa000003030303000000000030303030303070707070b07007000340d0b42d0010002aaa802aa9a400000c0c0c0c0000003000c00b002c00000c000b00000030303030b0b0b0b07c0040000aaaa2002002aa00c0c04c4c030303030000c03004c4c0303030302a84e87aaaa82aa06e80ca0328a0f201c829287c6a 25 33554431 11 2047
def hc_60_11 : Nat → Nat := unpackHintV5 0xf422acede98ee689d8dee9e8d40ab8cb8a20bfdaecb6da40ae322aa282ec9c119c94b1d88b6a528469c07ab26e7571506f019c68f98261f9c05b999853d1f24a1a6e45293c3ee1923382d82da9761e73ce1e081a1661ea0c6280004b06000012 0xc0c02c3c030303030000c0303c870070700707071300303030303030303001c1c1c131300c0c0c0c2c3c3c2c1c01c1c1c1d071f074287a0aa03aaa0aaaaaaa13a03a80ea0ba83ea0700a81e07aa81e0baa9a87e40000000030303030303030300030303030707aaa000000000000030303033f1f3f4fc7cfd0b0f0f0b00000aa0380002a802a8000000003000c000c0c0c0c01c000000003c87000303030307c0042c3c3c2c0008720aa038800aa802a8280ea03a0800002a0ba83e800026a1f900030300b0f00c0c0c0c000300c072007071313003030303030303030aa8070700a04c4c030303030b0f0f0b07007331f3f4cc7cfd2a8aa03aaa0a82a2a8030300b0f00c0c0c0c000300c01c1c0f21c01c1c1c4c00c0c0c0c0c0c0c0c007070704c4c030303030b0f0f0b0700707070741c7c1d0a1e82a80eaa82aaa81e1baaa84e80ea03a82ea0fa81c02a0781eaa07aaa6a1f9000c0c0c0c3c2c3c2c0c0c0c0c4c131313130b00c0c0c0c0c0c0c0d6aa42c4c2c4c0c0c0c0c2c2c2c2c2c43070b10c1c4d1340d03643da50f0f51f42daaaa03aaaa2a2a9a40c0c0c0c3c2c3c2c0c0c0c0c4c0b1313130b00c0c0c0c0c0c0c0d50b130b13030303030b0b0b0b0b02c1c2c0b071344d0340d43d870f0f50f0f0f1f42d84e87aaaa03aaaaaaaa9a613a03a80ea0ba83ea0b82eaa1faaa07a82e96a1f5a80c0c0c0c3c3c3c3c0c0c0c0c4c4c4c4c0c0c0c0c3c3c3c3d55550f61d55551513440d503543d41d115584e87aaaa03aaaa955599613a03a80ea0ba83ea07a82e95555556963355a80c0c0c0c3c13130f0f0f00c0c0c0c0c0c0c0c3c3c3c3c0c0c0c0d6a684c4c4c4c0c0c0c0cfc43073f10c1c3c3c3c3c4d1340d0347c2d6943d91f47d84eaaa80ea8a8aaaa69030303030f03c4c3c3c3c03030303030303030f0f0f0f03030303544c4c4c4c0c0c0c0c3c0f070f03c1c3c3c3c3c4d1340d0343c3c7c3c3d50f61c7d1f613a1eaaa80eaaaaaaaa6984e80ea03a83eaa83e0faa82ea0fa81ea0ba5a87d6a131313130f0b0f0b030b03030b130b130b230b370b0b0b0b5555555584e87aaaa23aaaa95613a37a88ea0ba83ea07a82e95556a030303030f0b0f0b030303030b130b13030303030b0b0b0b55555555451313403030303030303030b0baaa3f070b02c3f075555a6aaaaaaa555854030303030f0b0f0b030303030b130b13030303030b0b0b0b55555543d87554544d10340d503551f5074455613a1eaaa80eaaaa5555a586d613a03a80ea0ba83ea07a82e955555569655a803030131300c0c0c0c000300c0701c01c1c4c4c00c0c0c0c0c0c0c0ccc2cfc3cfc3ccc2d402444c0340d1f47d81850528aa03aaa0a82a1a403030131300c0c0c0c000300c0701c01c1c1c4c00c0c0c0c0c0c0c0c1c9c1c1c1c3c1c1d511300d0347d1f41870500287a0aa03aaa0aaaa9a613a03a80ea0ba83ea0700a81e07aa81eaa5a87d4000000303030300000000555500000003030303030303030b0b3f0f3f0f0b0b0000555500aaaa00550000000003030303000000005555061c00000003000c027003c001008720aa03aa801540880280ea03a82ea0fa00005555000a08000000003030303000003030303030303030b0b3f0f3f0f0b0b0000000000000340d0b47d07075a500000aa03aa8000001a400000c0c0c0c0000003000c00f009c0000000000340d0b47d00700061c08720aa03aa8800801a4280ea03a82ea0fa0800002800016a1f50003030131300c0c0c0c000300c0701c51555504144c4c00c0c0c0c0c0c0c0cfc2cfc3cfc3cfc2c1c1c028155062aaaa0955415003030131300c0c0c0c000300c0701c515555401870544c103540d527543d507400a1e82a80eaa825555a586d613a03a80ea0ba83ea0700a5555555a59540030303030b0b0b0b130b030303030b02c2c2c4c2c0303030303030303a82c2c2c2c0c0c0c0c2c2c2c2c2c0b070b02c1c4c4c4c4c0c0c0c0c2c2c2c2c2c2c2d0b1f0b42c2c2c2eaaaaaaaaaa2aaa800000c0c0c0c0000003000c00b002c0000000000030303030b0b0b0b07c0040002aaa8800800aa80c0c0c0c4c4c4c4c0c0c0c0c4c4c4c4c0c0c0c0c4c4c4c4c0c0c0c0e13a1eaaa80eaaaaaa84e80ea03aaa0fa81eaa9a87e6a130313030b0b0b0b130b030b0b030b282e0b00c0c2c2c2c5c0c0c2c2c2c2c2c2c2c0c2c2c0c2c2c2c2c2c2c2c0b070b02c1c4c4c4c4c0c5c5c0c2c2c2c2c2c2c2d0b1f0b42c2c2c2c4e1380e0382c2e0b1b82ca0b1ba0b82e1b86e000000000c17000002c0b0030b0b030000000000b000107c00c5c5c0c2c2c2c2c0000081b00380e0b82e06c006e1baa131703031313030300c4c0f0f0f0f0b0b0f0f0b130b0b02c3c030b0f0300707007070001c0303c87007070713070b070707070713070b0707070700707071300303070707170303001c1c1c4c7c4d1313134131300c5c5c0c2c3c3c2c1c01c1c1c1d071f07400a0a1c0e17031782e0f81c20707a071ba1b86e61cfc7c00000c2c3c0c00000c0c5c5c5c5c0c0c2c2c1c1c3c1c2c2c00000003c87000000031717030b0f0f0b1f3f5fc7cfd000000385c0c5e0b83e0000001b86e204c5c0c0c4c4c0c0c00001304c001300000017000c3c3c2c2c3c3c2c2c000c2c3c0c01c0000000000003c87131f1344c4c4d000317170307c0042c3c3c2c00002021c0e17031781b0020b83e001b86ea84c5c0c0c4c4c0c0c4c0c4c0c3c3c3c2c3c3c3c2c3c3c3c3c0c3c3c0c4c2c4c1c4c2c4c1c4c4c4c4c0c5c5c0c3c3c3c3d555555550f61d5555134cd551344d551513440d517543d41d115513131b1313a84e870385c0c5e0f83e1b86e555646d41d8c 24 16777215 10 1023
def hc_60_12 : Nat → Nat := unpackHintV5 0x84fced3f88bd9ef134cf051ce748ce737d09d9b20320cfca4e62f13d2f3a8f96754a0ab4a184df1ed25267491e02cc8921784128da1e1c9e0dd84d867e9b62ee94313f8df08c64d83e0a0a1865a80a9467842748c1b59780a40db03587200ec3000001d8 0xb0b050171717031717170304c4c054502d03c2c3c2c01c1c01c1c000701c0701d5140515555050c6d0e431b438131305c5c5c5c2c3c3c2c1c01d542c2c2c3c5c3c0c3c3c3c0c13130000b0b00b870f0b170f0f0b03c07070070707070001c0701c0743d1f555514555550061d0f5550f43d5413b544d13040d517542d543d0f541d003c6c3e0f0f0f8131305c5c5c5c2c3c3c2c1c01d55591b5000000b8702c2c2c2c00005c0c8c8c8c8c5c0c2c2d55400000000000155540000400870005c8c8c5c2c2c2c2c9c6d0e271b4380154000002e1c2c2c2c2c000c02f002c0000000000005555011010021c000103548d50b542d4001410004000172323170b0b0b0b0206c00155591b50b0b0b0f0f0f0f04c4c0b0f0b00b0b402e1c2c2c2c2c5c2c070701c1c000701c0701d554515551043c3c3c3c131305c5c5c5c2c2c2c2c1c01d54bcacbcac2c2c2c2c2c2c2c2c2c2c0b0b0b130b02c0c2c2c2cbc2c0d507070707070707070707070707070701c1c1c0707555555555545527272727272727270b0b0b0b0b0b0b82c6c2e07070707552f2f2f2f2f2f2f2f0707070707070707070707075555555541d874ed513540d52f5550f541d54bcbcbcbc1c1c1c1d55591b503030030300000c0c0ac3c8c2c8c3c9c2c131300c0c0c0c08c1c0bc1c000300c2b09c8c7c8d231f234131300c0c0c0c8cac8c9c8c0bc0c0e80c0e880c0c4c030380c0e0380e03080e03800c0c3c3c00303031300c2c0c030b00c0c00c0c0c03030b0303030000b0700b0700c2c030302c0b04c4c231f2348c7c8d0303030323030b0b0b0b0b00b20300c0e80c0e80c0e030380e0380c20380e00c4c00b0b0030b0b0b0300b0b0b0f003030b0b0b030300000b00c0b02c02c1c02c1c131300ccccc0c2c2c2c2c2c2c2d0b1f0b42c02c84c0380e0b0b82c6e0b0ba0b13a0b086e1b80303000c0c3c3c000c0c0c0c0c00c3c03030303030300303030000300c08c1c08c1c0f03c131300c0c0c0c8c7c8d231f2343c3c3c3c8c08c80c030380c0e0303a0303a0380e03080e03800c3c0030300c2c0c03030b0f02c3c2c0c0c0c0c0c0c000b02c0300c0b02c131303c3c3c3c0c0c0c0c8c0c2c2c2c2c2c02c80c030380c0e030380c0e0380e03080e038a00f130f0f000f03c6c3c3c3c3c3c03c00c0c00c0c0c0c0c03030f0303c4c3c3c03c3c6c2c3c3c3c3c0b0303030303030f030303870002c0702c0700f0700f0700c0303c0f04c4c06c6d1b1f10f1f0f43c3c3d0303030323030f0f0f0f2302380e8703132031303030f031ba030380e80c0e030380e0380c20380e000000000002c2c2c2c2c2c2c2c0c0c0c0c2c0c00000000000008c7c8d231f2340c0c0c0c8c0c2c2c2c2c00000c0e80c0e80e80e80e038000e03800000000c000b0002c000c2c2c0c0000000001f00100033f7b030b0b0b0b0004c008000e0382e0b81b001b86e0000000c00000000c0c0c0c01c0000070707070000030303030b0b0b0b0707070700000380e0380e030380c0e0380e00000000000230f230b230f230b00030303030000000000231f2348c7c8d000303030323232323000303a0303a000380e0380e000380e0000000300c00000b03c00c0c0c0c0000007000087000c0000000001c1c01c00007270707070f0707003000107c00c0c0c0c8c8c8c8c001c1c1d071f074287000030380e0380e000303a0303a0380e00000030ac00000b03c00c2c3c0c00000000087001c00000001c1c01c2c000c0c1c1c1c8c0c0c0007000107c00cacac0c2c3c3c2c001c1c1d071f074287000130380e0b83e000707a071ba1b86e505003030300c0c0030308c3c8c2c8c3c8c2c131300c0c0c0c08c1c08c1c000300c2b09c151451555505540c0d480c0380e0380e030954a00c0c00c0c0c0c0c0304c4c03c6ccc6c3c1b030303030006c070fc0700c030ac27151305551b47c50361d55550415130045546d0440d49d50f541c015580e87031320313030380e0380e0309655590352804c4c4c4c006c1b1b1f371b1b1f1f01b003030030303030300d504c4c03c6ccc6c3c1b1f0f1f1f1f0f1f270303030323030006c071ec0701f0701f0700c030ac27113131301b46d46c6c7c7c40c0c0c0c0d50361c7d1f47c180e87031320313030303a0303a0380e0380e0309a03628031301b03031b2b00c0f0f00f0f0b0f0f02c0c3c3c0c000b01c0b01c2300c0f03c505545550f61d550415130045546d330440d523543d41c015584e87131321313130380e0f83e1b0955591b500c4c03c3c030f0f0300f0f0f0f00303232323230303050f43c0008c0303c0f023070230711300d1f43d0f47c2c06c2d07c121300e0383e0f84c4e83c3e86c261b4a00c4c06c0c0c6c8c0300f130f0f000f03c6c3c3c3c3c3c03c03030f230f0f030303c3c03c3c2c3c3c0b030f0f0354000b01c0b01c2300c03c1c03c1c0f03c44c06d46c7c40d1f43c3c7c3c3d50f61c7c184e87131321313130380e0f0f1b1ba0f0f83e83e0f86c261b400008c8c0c0c8c8c0c0c008c3c8c2c8c3c8c2c000c8c8c0c00000000000000000d1f47d1f4001c1e84c4e8000e0386e1b80186d000000308c00000b03c00c8c8c0c000000000000000001c1c01c000c0c1c1c1c8c0c0c1c9c1c1c1c3c1c1c1000107c00d1f47d1f40870100287000130380e1b86e000707a071ba61b400008c8c0c0c8c8c0c0c010c3c9c2d0c3c9c2c000c8c8c0c0000000000000001555401544c4d40000e0386e1b80154000000c2f000002c0f0032323030000000000000110555510021c0000001410040d523549d50f50400a1c0004c0e0386e1b80155591b528031301b03031b00c131300f1b1b0f06c0c9c0c001b01c01c00c09c131301b1b46c7c40c0c9c9c213a1c4c4c84c4c4c0e0386e1b86c21b86e000003030303000003030303030303030707aaa000000000000030303030b0f0f0b331f3f4cc7cfd0000aaaa000000aa000003030303000000c003001c000003c870000000c0c0c0c2c3c3c2c041f000021c82a80eaa022000aa0a03a80ea0ba83e8002820000009a87e40 25 33554431 10 1023
def hc_60_13 : Nat → Nat := unpackHintV5 0xf6c1f2f1c140ec8150e551ccde31c8d47270cbaa32bcabc0b18ac8a78282a1a178988a4690e1ea8b41688471b47ae2647a781a7998387289c468ba745f7a50507bc04772423ef220350a7a2bc2522481d01e71841701dc0f59ea0462be000118 0x131300b0b02c2c2c2c0701c0b078701c0701c0702c1c1c8c07072301c1c2c07070b01c070714555541155104c4c232323230b0b0b0b0700701c1e071b255373737370f0b0f0b0f0b0f0b0b0b0b370b370b0b0b0b555555552727273727370b0f0f0b270b0b5500000b0b0b0b000000dc003001c00b000000002c00055551001001002737272b0b0b0b0b06c008270055372b372b0f0b0f0b0f0b0f0b0b0b0b370b2b0b0b0b0b55555543d87554ed513540d54dd547d41d55549c9c9cdc9cac2c3c3c2c9c2c2d55591b5000000232317032323170300070707070f0f07070f0b0f0b00000000000000001747d0b43d0000231b2388c6c8e172323170b0f0f0b0047c7d000000308c002e1c0003c3c2c3c2c000000000000000001c1c01c001c0c1c1c1c8c1c0c1c2c1c1c1c3c1c1c1000107c05d1f42d0f4087010000081b0172323170b0f0f0b0007070781c6c1e47c7d0b0b007070171717031717170304c4c007070701c1c0b0703c2c3c2c01d050001c0701c07050f1444c1745d0b43d07114fc6cfe3f1b3f8131305c5c5c5c2c3c3c2c1c01d1f1f42c2c2c3c5c3c0c3c3c3c0c13130000b0b00b870f0b170f0f0b00707007070001c0701c07070f0707070707070f070f0707070700707071300703070707170703070b0707070f0707543c3c7c7d43c3d0f511305d1742d0f418705003c6c3e0f0f0f8131305c5c5c5c2c3c3c2c1c01c1c1c1e071b0791f1f4bcacbcac2c2c2c2c2c2c2c2c2c0b0b0b130b02c0c2c2c2cbc2c0c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c0741c51f47d1f47d0b0b42c7d0b142c7d41d0749c9c9c9c9c9c9c9c2c2c2c2c2c2c2e0b1b0b81c1c1c1d1f1f4bcbcbcbcccccbcbcbcbc1c1c1c1c1c1c1c1c1c1c1c1c1cec1c1c1c4c1c1c1c0c1c1c1cbc1c0c1c1c1c1c3c1c1d51f47d1f47d1f47d41d870707507071f2f2f2f2f33330707070707070781c6c1e47c7d00001717170317171703000000000b0b0b0b00000000005555005555000431b4390c6d0e00171717170b0b0b0b005502c0f170f030f0f0f03000000b021c2c2c2c2c3c2c00000f01c00000155540155541870003c0003c0f00000000c017002c00b00040f1b0f83c3c3e00171717170b0b0b0b00550206c02b3700b0b02c2c2c2c02c2c2c4c02c0c2c2c2cdc2c0c00001c070070070070700707145555555554109c9c272727270b0b0b0b0b0b0b82c6c2e07007550bcdc02c2f0b370b0001c0701c0714555541d87150ec413140c5371450f107d540bcdcdcbc2c2c1c01d54591b100000030b1703000000000000000b0b230f230f0b0b0000000345d0b47d00070751307500030303030b032b0300231b0388c6c0e40c7d00c00003021c4c3c2c2c4c3c2c2c000c2c5c0c001304c001300000017000c00f014c00000000000131f513135000345d0b47d00700061c4c6c0e1313038000c0c0c0c2c0cac0c1b0020040c7da1d0c6c3c01e871f46d0c000002c2c2c2c3c2c00000000005c0c5c5c5c5c5c0c00000000005d1742d0b400061c1c1d43c1d4005c5c5c5c2c2c2c2c006d0e1b4391f1f40b03c5c3c0c3c3c3c0c000002c0870b0b0b0b0f0b0003c0f0003c0000005c003002c00b0000000000003c7d43c3d4005d1742d0b401c001870f1b0f83c3c3e00171717170b0b0b0b06c008011f1f4031700b0b00c2c2c0c000700c0701c05c4c5c4c002c2c2c2c0c003030b030b01c1c001c1c45c031f47c7d0b42d07041c1d43c1d4031700c0c0c0c2c0c2c0c1c00c8c6c0e231b039031f403c4c3c3c0031702c2c2c0b0b0b0f00c0c0c0c0c2c2c0c0c2e1c0b04c0b08c0b00b0f0b0f02c02c3c2c030b2302c0c0c0b0b0b0b0f02c2c2c2c0001c1c01c1c0700c0701c511703c7d43c3d40c7d1f1f42d0b41c1c1c1c1c50761c031703c6c0e0f0f0380cac0c0c8c0c2c0c2c0c2c6c80b0381c00d031f400c5c00b1700c2c8c0c0001c00c0701c05c4c5c4c000b0b230f2b0f0b0b030300070311700c7d1f1f42d1f41c1070751f07500c5c030303030b032b0307003231b0395c6c0e40c7d00f0f000c5c0b0b0b0000700701c0302c2c2c4c0b0f0b03030b0b03030700711703c7d0f0f40c7d1f1f41c10742d00c5c0f0383c0e032703032303070030b030b0340c7d017131713000c8c5c8c0b0b0b02c2c030300b030b00c2c2c2c0c2c0001c1c01c1c070700c1c0701c45c1f1f51f1f5031f47c7d0b42d0704031708c6c0e231b0380c9c0c0c8c0c2c0c2c0c1c00d031f42b53002c2c02c2c2c2c2c000701c01c01c02c2c2c4c02c0c2c2c2c2c0c0070700070711f07d1f42c2d0b1f41c1070750b07509c9c272727270b0b270b0b0b070070b0b0b82c6c2e47c7d0bc02c2f0b0b07c1304c3b00c7c1f1f0307c2c3c0f0b0001c0701c071447c1f47d0b47d0707070707141d8702f2f0b0b1f1b206c7e0700747c7d0000002323170323231703000550f0f50f0b0f0b000000000000000055550000431b4390c6d0e172323170b0f0f0b005500000030ac002e1c0003c3c2c3c2c0000000000000441555440087000044c0001410040d523542d50f5040000206c05c8c8c5c2c3c3c2c0155591b504c4c02d0b0b02c2c2c2c143c3c05c0c5c5c5c5c5c0c1550000701c0701c01c1c01c1c515555415104131305c5c5c5c2c2c2c2c9c6d0e271b4381c01d541313002e1c2c2c02c2c2c2c5c2c2c3c2c2c0c2c2c2c5c2c0c00001c0701c070070700707145555555550061c1513040d517542d0b542d0f542d0b5542d5541d00131305c5c5c5c2c2c2c2c2c2c2e0b1b0b81c01d55591b500000000000b0b0b0b021c10005555040010355550b400000171717170b0b0b0b55595 24 16777215 10 1023
def hc_60_14 : Nat → Nat := unpackHintV5 0x98d4b7a46a3968d0894217339e8038b29dd347673d06f9c421646c249c99b82a2617cac979918c5890ba94c92b650a050936019049009010743983aa4e58d9222e3614068c4b27429e0e989582401dbcf486b117c160098841a2cc0c208901b52a604045a0000202 0x2305c4c5c4c8c170317030b0b0b0f0b0f0b030350f030b40c2c2c3c0c2c2c5c2c8c2c23070b0bc1c0c8c2c0c2c2c2c2c7d1747c3d43c3d40c7d1f1f42d0f47d0b48c0c5c0c9c6c0e231b0380c9c0c0c9c0c2c0c3c0c9c0c2c0d031f4131300b0b02c2c2c2c02c2c2c4c02c0c2c2c2c5c2c0d502c1e1c0701c070702c1c0701c01c1c01c1c0b0700c1c1c17070302c1c1c0b070702c01c1c1c1c0b00707070701c1c44c1745d42d870b0b50b0b0f07041c1c41f504c4c171717170b0b0b0b0b0b0b82c6c2e070070707206c1e47c7d04c4c00b0b0b0b0170323232323170302c2c0b0b0b0b050701d0001c07007070070701c0711305d1f41c1d03c3c01d0b0b0b41c104c4c17232317231b2388c6c8e0b0b0b0b0700747c7d04c4c02c2c0b0b0b0b00b0b0b1300b030b0b0b230b03540701c0b078701c0701c07007070070702c1c1c0c07072300c1c2c1c2c07070b070f01c1c2c1c2c070070b0701c0070711305d1f50b61c2c2d42c2c3c1c101d41c7c4131305c8c8c5c2c2c2c2c2c2c2e0b1b0b81c01c070781c6c91f1f45c0c5c0c8c171317132300c0c2c0b00c0c2c2c2c2c0c2c2c0c1c1d41c1c1d07070707030707030700c0c1c0703070707071f45d0347d070750f0f50742d0741d2303170303030303231b0388c6c0e0b030b030703070340c7d1723031703230b0b0b0b030b0b030b02c2c2c4c2c03030b0b0b230303541c1c1c1c2c1c0c0c1e1c1c1c0c0c1c1c1c1c1c07070701c1c1c8c1c1c1c4c1c1c1c2c1c1c2c1c1c1c2c1c1c1c2c1c2c1c1c1c1c1c2c1c1c1c1c1c0c0c0c7d1740d1f50b61c2c2d42c2c3c1d0741c1d41c7d48c0c5c0c0c0c0c0c2c0c2c0c2c2c0e0b1b0381c0c1c0c1c1c0e071b039031f4000000c2c2c2c2c0c000000b0b07070b070b0b00000000000000347d0b42d1f1f51f1f50000030303030b030b03231b0388c6c0e0040c7d00000000003000b0b0b0b01c004000000002c007d1f40f0010b42d07c00009cfc9cac1b0020b0b0b0b0047c7d2b2b0f0b0f0b0f0b0f0b1f3b0b131f130b1f1f030b1f1f0b03542c2c2c2cac2c2c2c2c2c7c2c1c2c2c1c7d1f47d1f50f61c3c3d43c3c3c7d0b49c9c9c9cac2c3c3c2c2c6c7e1f1b0b89c2c2d1f1f4070704c4c02c2c0c2cac0302c2c02c2c2c2c2c0b0b0b0b0b04c1e1c0b01c0b0b01c0701c071415515542d8755410544c011550b4cc1103548d50b50700554131300b0b82c6c85c8c8c5c2c2c2c2c1c01d55591b504c4c02c3c0f0b0f0b04c1e1c0701c070705c1c0701c0b0700c1c1c17070302c1c1c0f070701c1c51550b61d550544541513040d517543d41c0150741c101155504c4c171717170b0f0f0b070070707206c1e555646d4071300b0b02c2c2c2c000701c0701c51550b61d55041513045d517542d41c015504c4c171717170b0b0b0b07007555646d407070b0b1700c0b0b0b032b04c4c0b0b0b0f02c0b0b0b0b3302c2c0b0b0b0b02c2c0b01c13078701c5c0b0701c075115145542d87554142d330404550544c103545d50b507005542c6c80b0b8131305c5c5c5c2c2c2c2c1c01d55591b504c4c02c3c0f0b0f0b01c0704c1e1c0701c0701c0b07070301c1cac03070b01c1c3c0701c1c51550b61d55045550747c41513040d523543d41c0141155074cc11504c4c172323170b0f0f0b0700701c1e071b2555646d400002c2c2c2c000002b000c00b001c000002c000015554400400400acacacac2c2c2c2c1b00200552b2b2b2b0f0f0f0f0f0f0f0f2b2b2b2b0f0f0f0f555543d8755554ed513540d52b543d41d5554acacacac3c3c3c3d55591b504c4c02c2c0b0b0b0b00f0f0f0f01703232323231703050b42c0001c0701c07007070070711305d1f42d0b42c2c02c2d01c104c4c172323170b0b0b0b231b2388c6c8e0700747c7d01c1c131300b0b030b2300c03c4c3c3c002c0b0b0f0b0b0f0f00b03c0c3c8c3c3c3c0c0b0b00b0b0b0b0b02c2c2c2c2d504c1e1c0b01c0b0b01c0702c01c1c01c3c1c1c0701c44c02d42c7c45d1f42c2c2c2c2d50b61c1c104c4c02c2e0b1b2172323170f1b0f83c3c3e0b0b0b0b0700747c7d04c4c00f130f0f00f030f170f0f0f0302c3c0f0b0f0b5413078701c0701c1c1707007070070701c0702c1c03070705c1c0c0f00707070703c01c1c1c1c0b070703c1c1c070711305d1742c2c2c2c2d50b61c1c10707107d4131305c5c5c5c3c6c3e0f0f0f82c3c3c2c1c01c1c1c81b0791f1f40713003c4c3c3c03c3c3c5c3c3c3c5c0b0b02c2c2c2d50001c07007070070701c0711305d1742c2c2c2c2d50b61c1c104c4c171717170f1b0f83c3c3e0b0b0b0b0700747c7da1cfc6c131300b0b02c2c2c2c01c1c3c1c05c0c5c5c5c5c5c0c142d0b00b004c071702c1c0701c01c1c01c1c44c1745d0b0b50b42d870b0b00b0b40704131305c5c5c5c2c2c2c2c6cfe731b3f81c01d1f1f407070b0b1700c0b0b0b032b04c4c0b0b0f0f00b002c0b0b0f00f130f0f00f030f170f0f0f030b0b02c0b0b0b02c2c0b0b0b0b540b0b02c0704c1e1c071702c1c01c1c01c1c0701c2c7c40b511305d1742c2c2c2c2d50b61c1c10b1b202c2e04c4c171717170f1b0f83c3c3e0b0b0b0b0700747c7d04c4c02c3c0f0b0f0b00f0f0f0f01703232323231703050741c0001c0701c07007070070711305d1f42d0742c2c01c1d01c104c4c172323170b0f0f0b231b2388c6c8e0700747c7d04c4c00f130f0f00f030f230f0f0f0302c3c0f0b0f0b540701c13078701c0703c01c1c01c1c1c1c0701c0b07070301c1c8c03070f0701c01c3c1c3c070070b073301c1c3c1c3c0701c1c44c1747d0b0b0b0b0b542d8707040741d41c1c7c7c4131305c8c8c5c3c6c3e0f0f0f82c3c3c2c1c01c070781c6c91f1f400002c2c2c2c00000300ac00701000002b0002c000007d1f42d0b4041f007c0000acacacac2c2c2c2c081b00011f1f4acacacac3c3c3c4c3c3c3cec3c0c3cac3c3c3c0c3c3c3c3c3c3c3c3d52b2b2b2b0f0f070f0f0f070f0f0f0f1f47d1f47d0f0f1f0f0f543d871f47d2b2b2b2b0f1b0f83c3c3e0f0f0f0f47c7d04c4c02c2c0b0b0b0b02c1e1c0701c070702c1c0701c0b0700c1c1c17070302c1c1c0b070701c1c5155550b61d0544541513040d17545d542d41d07004541d0704045554131305c5c5c5c2c2c2c2c1c01c1c1c81b07955591b504c4c02c2c0b0b0b0b01c0702c1e1c01c0701c07055017032323232317030b0b00701c1c1c1c0145155550b61d41054504c4c172323170b0b0b0b07007271b3f89c6cfe5504c4c02c2c0b0b0b0b01c0702c1e1c0701c0701c0b07070301c1cbc03070b01c1c2c0701c1c5155550b61d0455441513040d17548d542d41c014115507411504c4c172323170b0b0b0b0700701c1e071b2555646d40c0c0c0c3c2c3c2c0c0c0c0c2c5c2c5c0c0c0c0c2c2c2c2d555555540c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d54131300b0b02c2c2c2c0b078701c0701c1c0b0701c0702c1c37070708c1c1c0b070702c1c1c070714555541511504c4c272323370b0b0b0b070070707206c1e55 26 67108863 11 2047
def hc_60_15 : Nat → Nat := unpackHintV5 0x8ca4b6226e176821cf3a07a01a7e147a9e452807400a29be123e6c50669a0322263f08398531525ebc52170b14858d06b94bf2ea4f587492782bc462c76902a2c23d04748ded2a832d89b8c1014c2ca87309b62e81f38f406612da15947e039d39008e0b28000470 0x4c4c4c4c2c2c2c2c4c2c2c2c2c2c2c50b42c0b030b0b0b170b030b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b02c1c2c0b071344d1745d0b0b42c7d0b142c7d42d0b44c4c4c4c5c5c5c5c2c2c2c2c2c2c2e0b1b0b82c2c2c2d1f1f400000000305c00000b02c02c2c2c2c0000000002c00041f01745d0b42d07c0000081b0171717170b0b0b0b0047c7d544c5c4c0c4c4c4c0c131303c3c3c3c2c2c3c3c2c4c2c2c0b0f03c2c3c2c01c1c01c1c000701c0f21c01c1c1c4c1c2c1c1c1c1c1c4c1c2c1c1c1c1c01c1c1c4c01c0c1c1c1c5c1c0c007070700141871745c5c5d0b43d07041c1d41c7d44c6c4e1313138131305c5c5c5c2c3c3c2c1c01c1c1c1e071b0791f1f6873f1b00000f0b0f0b000017031717171717030b0b07070f070b0b00000000f21c00000005d17171742d0f4000000005c5c5c5c2c3c3c2c6cfe831b3f8011f1f441317130313131303000004c130004c0000005c0030f0f0b0b0f0f0b0b000f0b0f0b0070000000000000f21c001021c5d17171741f0010b43d00131b1384c4c4e001717171706c0082c3c3c2c011f1f55131713031313130313131313130f1313130f131313131317171717131307131313071313131317171717333313131f1313544d871745c5c5d1f47d1f47d131b1384c4c4e1313131317171717333347c7d00000f0b0f0b0000021c007000007030707072307030001c001875555005555000300ac00b003c00070002c00701c000702c00400172b2b170b0f0f0b0007070781c6c1e550206c000003c2c3c2c0000007021c000017032f232f2317030000000000061c555500555500172f27170b0f0f0b00271b3f89c6cfe5500000f0b0f0b0000001c087000007030707072307030001c001875555005555000300bc00b003c000000701c0007000400172f27170b0f0f0b0007070781c6c1e550206c01313002c2c02c2c2c2cdc2c02c2c2c3c02c0c2c2c2cdc2c0c00002c0b00b00b00b0700b07145555555554104c4c172727170b0b0b0b270b0b0b0b82c6c2e0b00b5500000b0b0b0b000000dc003002c00b0000370002c0000155544004004005cdcdc5c2c2c2c2c1b0020015413130131305cdcdc5c003705c0551361d5555041f50314dc5143c407105504c4c173737170551646c40c0c0c0c5c5c5c5c0c0c0c0c5c5c5c5c0c0c0c0cacacacac5d1740d03030347d1f47d1f6aaa6aaa9a40c0c0c0c0c0c0c0d03030317171717030303032b0303030303171717170303030303030303272b2b271745d0340d0340d1f47d1f47d030303030317030303130303545c5c5c5c0c0c0c0cac0c0c0c0cac0c3c0c0c5c5c5c5c0c0c0c0c0c0c0c1c0cbc0c0cacacacac5d1750361c0c0d40c0c7c7d1f47d1f40c0c0c0c0c0c0c0c0c0c0c0e0303030380c0c0c0c0c0c0c0d03034031300b0f00c2c3c0c15400c1717171700b0b5550005c0302c0b0230702307145555505454100c4c030303030b030f03231b0388c6c0e270035500c4c03c2c4c3c4c3e1c0c2c3c0c0f0f030305c5c5c030b13130005c0302c0b08c070fc07151310361d55545552347c5041513045d42d50f5045548d0441c015500c4c030303030b030f0306c0e231b22700350355591b5055000c4c17170305c5c00b1308c3c2c2c8c3c2c2c0c2c5c0c0014140700c0701c501515555504031308c6c0e231b0380c0c0c0c2c0cac0c1c00d54070700c4c05c0c0c5c5c0302c4c03c2ccc2c3c23030b170304c1e1c1301c131301c0301c07151305552347c50361d55550415130045548d0445d42d50f541c015500c4c06c0e231b2030303030b032b030700350355591b500c5c02c3c030b0f030171317130030ac7c7c7c01c1d554000700c0701c14145155554151504031700c0c0c0c2c0c3c0c9c6c0e271b0381c00d54031700b0f00c2c3c0c2304c1308c0c0c232b2300c1c1c1c000700c1c3c1e1c0f070703c3c545c40d8755551551410544c11f50b543d41155334110700554031700c0c0c0c2c0c3c0c1b0389c6c81c00d40d55646d45c0c5c0c2c2c2c2c0c2c2c2cac0c2c0b0b0b130b00c0c2c2c2c7c0c0d50b0b0b0b030b0b030b0b0b0b0b02c1c2c0b07555555555555527031703030303030b030b030b0b0382c6c0e0b030b03550000030b0b030000007c003002c00b0002f00000005555100100100030303030b030b0306c0082f0055170317032b1717032b2b0317172f032f2f032b2b2f551750361d5555553b544d51f5543d507555503170303030303032b032f030350355591b50f0f0f0f1f17171f0f0b50f0f0f50f0f170f0f0f0303030f0f0f0b0f0f1f0b87231717230f0f0f0f1f1f1f1f0f0f0f0f1f45c5c5d0f0f50f43d870303030f43d1f47d230317030f030f031f1b031f1b030f030f032f03570340c0c7d0301c1c04c4c4c4c007c1f231f371f1f1f1f01f003130170303171700d502c4c03c2ccc2c3c231f0f0b0b1f0f0b0b03170b17230304c1e1c1301c1313007070070701c0301c07113131301f48d47c7c7c7c40c0c0c0c0d50361c2d1f41c100c4c06c0e231b21f1b0387c6c0e030303030b032b030700340c0c7d031f1f171317131f371703170354ac5c5ccc7c3c7c7c7c3c7cdc0cdcacac0c5c5cbc7cdc7c1c7c7c7c1c0cbcbc0cccacacbc7d17171740c0c0c0c0d50361c7d1f47d1f40c5c0c7c6c0e1f1b0380c0c0c0ccc0cac0cbc0c0d03031f40c0c0c0c0c5c5c5c5c0c0c0c0c5c5c5c5c0c0c0c0cacacacad55550361d555517544d50352b543d50754bd5503030303030303030303030303030303555640d4030303130387131300c4c4c4c0b0f00f0b0b0f0f02c0c2c3c0c02c4c4c4c007c0b170b0b1717171700b00c0c2c5c5c5c0c0d50002c0702c0705c8c031702c0b00b0700b0711301f5171710345d43d870f0f50f0f0f1f04031301b0385c5c80c0c0c0c2c0c3c0c2c6c0e1f1b0389c00d031f40c0c2c13031305c03031700c0c4c0c4c0c3c3c2d0f0f50f0b0f0b030b0f030b08c1c2c23070b130b1303170b030b0b0b0b0f0f5130f51344d0345d0b43d1f42d231b0388c6c0e13031303030303030b030f0327030b0340c7d03030313131713130303031303870f0f0b0b0f0f0b0b0f0b0f0b030b0f0313131f0b130b0b131313130b130b0b1302c4c4c4c2c03030b1717170303542c2c4c1c2c2c4c1c2c4c2c4c0c5c2c0c2c2c2c2c2c0b070b02c1c4c4c7c7d44c4d1351344d0345d43d870f0f50f0f0f1f42d131b0384c4c0e13031303030303030b030f030b1b0387c6c0e27030b0340c7d 26 67108863 11 2047
def hc_60_16 : Nat → Nat := unpackHintV5 0x834d544044589ecd554ebf29e71c10e3628ae1a06438ca19865f3d742d5093956b4f4a2623e4c9128243086102b7b47a11d23a3cb31ba65e0cf93685dea782a1d3613467208e33003fb9d81a85560bb46384ee3b01fd1e80a795c02ce9b80c9278000192 0x300000c0870f0f0b0b0f0f0b0b00030b0f0304c0004c1300000000c017001c000004c07000003c8700004c7c4d1313134000c5c5c0c2c3c3c2c041f000131b0384c4c0e00030303030b030f030206c0009c0c9c0c00000c2c2c0c00002b00b0000000000032323030b0b0b0b0107c000000c0c0c0c2c0c2c0c081b00027032303000000000000c0c1c1c2c2c2c1c0c2c2c2c0c2c00000300c03000001c00000000002c87000000cc7ccd331f3340cacacaccc0c2c2c2c2c03308c000009c6c0e271b0380c9c0c0c9c0c2c0c2c0c00309c0009c0c9c0c05c4c5c4c000c5c0002c3c030307070f030b07030b0b0f030b00007030030300700301c0705c5c231f2348c7c8d032b232333030b0f0f0b0700700c5c271b0388c6c0e0327030327030b030f0307003270323030ac02c3c0f0b0f0b0ec1304c3b2b030030707070001c07070f078703c1c1c0f0f0cc2b332b0b0f0f0b07ccd331f10700709c27272b0b0f0f0b06c9e271b2070072733272b2b2b2b0f0b0f0b0f0b0f0b0707070707070707070f078707070707073b07070713070707030707072b0703070f070707072b2b2b2b0b0f0f0b0707070707070741c7c1d2b2b2b2b0b0f0f0b0707070707070781c6c1e0acac03c1303c3b00c3cac0f0f0302c3c0f0b0f0b0707070001c0703c0f0707070f078702b2b2b2b0f1f103c3d0b0f0f0b0700702b2b2b2b0f1b203c3e0b0f0f0b0700700000b0b0b0b000000c02b001c000001c87000000acacacac2c2c2c2c041f00000272727270b0b0b0b0206c0009c9c9c9cbcacbcac3c2c3c2c3c2c3c2c1c1c1c1c1c1c1c1c1c1c1c1c1c3c1e1c1cec1c1c1c4c1c1c1c0c1c1c1cbc1c0c1c1c1c1c1cccccacbcbcac2c3c3c2c1c1c1c1c1c1c1d071f0749c9c9cbc9cac2c3c3c2c1c1c1c1c1c1c1e071b0789ccc9c0c0c04c0c000031302b0f230b230f330b04c4c031717030230702f070005c030ac2f1713513135113131300c5d171f47d1f47c1571b0388c6c0e00c4c0303030333032b032f00340c7d0130f0f0f000c4c4c4c0b0b0b02c2c030300b030b00c2c2c2c0c2c0002c1c02c1c0b0b00c2c0b02c44c1717517175031745c7d0b42d0b04031308c6c0e231b0380c5c0c0c8c0c2c0c2c0c2c00d031f41313002c2c02c2c2c2c2c02c2c2c3c02c0c2c2c2c2c0c00002c0b02c0b00b0700b0711305d1f42c2d0b1f42c2d42c4d42c104c4c172727170b0b0b0b0b0b0b82c6c2e0b00b47c7d00c4c00f0f0f0f00170b170b0300f0f00c3c3c0c0c0c03c0c3c0005c03023070230703c0f11300c5d171f44c4d43c3d43d0f47c100c4c03030303231b0388c6c0e0f030f032f00340c7d00f0f000c4c0b0b0b02c2c2c3c0b0f0b03030b0b03030002c0b02c0302c0b11303c7d0f0f40c5d171f42d0b42c100c4c0f030f030317030323030b030b030b00340c7d1403c4c3c3c003c0f1f0f0f0f0f0f00f003130170303171700c3c3c5c0f130f0f00f0f1f0b0f0f0f0f02c0c0c0c0c0c3c3c0c0c3e1c000b01c0b01c03c1c03c1c1700c0f03d1361c4c4c44c4c4c3c3c7c7d43c3d0f5031745c7d0f43d1f04031301b0387c6c83c6c0e0f0f0380c5c0c0c8c0c3c0c3c0cbc00d031f400000000000b0b0b0b0b0b0b0b030b0b0b0b03000000000000017175171750351750b42d0000231b0388c6c0e0317030323030b030b030040c7d0000000030002c000b000b0b0b0b00000000004c004005d1f42d0b41f0006c008005cfddc5c2c2c2c2c011f1f400000030000000030b0b03007000001c1c1c1c00000d1742d0b41c1d071f400000c0c0c0c2c0c2c0c1c0c1c0d031f4000000000008c3c8c2c8c3c8c2c000c5c5c0c00000000001c1d44c4d4000d1747d1f4008c6c0e231b038000c0c0c0ccc0cac0c01031f40000000c17000002c0f0031717030000001c00021c003000000000070700700001ccc1c1c1c3c1c1c00c187000130345d1f47d0007075071f5000206c00c0c0c0ccc0cac0c001c1c0e071b039031f4000000c2b000002c0f00f0b0f0b00000000021c007000000007070070b0007030707072307030001c187000131747d0b43d0007075071f5000206c05cacac5c2c3c3c2c001c1c1e071b0791f1f4504c4c07c5c0c7c0304c4c03c7c7c3c1f1733170007c0700701703344d87131311313131747d1f47d1f04131301b1f87c6c85c5ccccc11f1f400003c2c3c2c00005c0c5c5c5c5c5c0c1c1d5540000000000015554000000005c5c5c5c2c3c3c2c8c6c8e231b238015400003c2c3c2c000003005c007000000f21c000021c41545d550110000503545d50b543d40014100000000005c5c5c5c2c3c3c2c081b000555646d4131300b0f03c2c3c2c000701c0f21c01c1c01c1c1c4c01c0c1c1c1c5c1c0c0070707061d41545d5541555544d40d517542d50f541c0150741d550742d54004c4c171717170b0f0f0b0700707070781c6c1e555646d40000005c0c5c5c5c5c5c0c003c2c3c2c1c1d5540000000000001545d000055000017171717231b2388c6c8e0b0f0f0b0055000000005c003000f0b0f0b007000000000f21c087105517440055400140d5175040000150b543d400000001717171706c0082c3c3c2c0155591b504c4c02c3c0f0b0f0b0001c0701c401c1c4c4c05c0c5c5c5c5c5c0c15501c1c014551545d5541505404c4c171717170b0f0f0b07007231b2388c6c8e5504c4c02c3c0f0b0f0b0001c070070703c8700707071300703070707170703001c1c1c187505517555055550747d513503545d50b543d50700541d075541d5500131305c5c5c5c2c3c3c2c1c01c1c1c1e071b07955591b5131313130b0b0b0b130b0b0b0b0b0b02c2c2c4c2c0b030b0b0b170b03542c2c2c2c2c2c2c2c2c2c2c2c2c0b070b02c1d55555555551544c4c4c4c5c5c5c5c2c2c2c2c2c2c2e0b1b0b82c2c2c2d5400002c2c2c2c0000017000c00b002c00000000005555100100100171717170b0b0b0b06c00801544c4c4c4c4c4c4c4c5c5c5c5c4c4c4c4c5c5c5c5d1361d55545d555544d40d5175550f541d55544c4c4c4c5c5c5c5d55591b5 25 33554431 10 1023
def hc_60_17 : Nat → Nat := unpackHintV5 0x945867a40422489a0ce20d8320802c669e8b30073fcc61bc027e6994ad992e26e5fc09f16cc24852e10a13bf1f24bf46111f421245804a10a41783d5ca68e362423384aa8be02022ab89909f117a24347208191e81b14aa05343220ee0be028626403c8ca00001e4 0x2c2c2c2c00000000c007002c000000002c000173f33170b0b0b0b07c004330000173f27170b0b0b0b06c00827002733273f04c4c03c2c4c3c4c3e1c3c2c3c2c0f0f17030ecec030b13130001702c0b0ec0700704c4c1733170b0f0f0b07ccd331f133004c4c1727170b0f0f0b06c9e271b22702733270303030303170303031303030303030f0f0f0f03030f870303030303030f171717170303030303030307032f03030f0f0f0f1717171703030303370303030340c7c0d0f0f0f0f2f2f2f2f0303030303030303030303030380c0c0e030303030303030303030303170317030f0b170f170b03030f870f0f03032b2b0b1317130b3b0f0f0f0303030b170b2f032b0b030b0b0b0b0b0b070b2b0b0733171737032b2b030b0f0f0b0b1f2b4ac7c2d2f0b0b2f27031703030303030b030f030b1b0389c6c0e27030b0327032703000000000c2b000001c030030b0b03000000ac000b0000041f0032b2b030b0b0b0b00000206c00c0c0c0c2c0c2c0c00dc0cfc0c3c3c3c4c3c3c3cec5c0c5c0c3c3cac3c3c5c3c3c3c0c0c0c0c0c3c3c0c0c3e1c5c5cbc3c3c1c3c3c3c1c0cacac0c3c3c3c3c5c5cdc3c7c3d0f0f0f40cacacac0c3c3c3c3cbcdcbc0c5c0c3c6c0e0f0f0380cac0c0c0c3c0c3c0cbc0c0cdc0c0c0c0c0c0c3c2c3c2c0c0c0c0c0c0c3e1c0c5c0c0c0c4c0c0c0c0c0c0cac0c2c5c2c5c0c0c0c0c2c2c2c2c0c0c0c1c0cbc0c0c5c5c5c5c0c0c0c0c2c3c3c2c0c0c0d031f034bc2c2cbc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e03030380c0c0c0c0c0c0c0c0c0c04c0c000031302b0f0b0b230f0b0b02c4c030b1703007030030301304c00700301c07231f2348c7c8d04c4c031717030b2b230b07007571b0388c6c0e00c4c030303030b032b0307003370323030130f0f0f000c4c4c4c0b0b0b02c2c030300b030b00c2c2c2c0c2c0001c1c01c1c070700c1c0701c131308c7c8d231f2340c5c5c5c8c0c2c2c2c2c1c01c031308c6c0e231b0380c5c0c0c8c0c2c0c2c0c1c00c8c0c8c0c1313002c2c02c2c2c2c2c02c2c2c3c02c0c2c2c2c2c0c00001c07007007007070070704c4c173333170b0b0b0b0b0b0b42c7c2d0700704c4c172727170b0b0b0b0b0b0b82c6c2e070072727272700c4c00f0f0f0f000b0b0b0b0300b0b00c2c2c0c0c0c02c0c2c0001c03007070070701c0704c4c03171703231f2348c7c8d0b0b0b0b0700700c4c03030303231b0388c6c0e0b030b03070032303230300f0f000c4c0b0b0b02c2c2c3c0b0f0b03030b0b03030000700701c0301c0704c4c0f0f0f0f0317171723030b0b0b0b0700700c4c0f030f030317030323030b030b03070032303230301c1c03c4c3c3c002c0b0b0f0b0b0f0f00b0031300b03030b1700c2c2c2c0b0b0b0f00b0b0b0b0b0b0b0f02c0c0c0c0c0c2c2c0c0c2e1c13078702c0702c2c0b007070070f070701c0301c0704c4c02c2d0b1f10f1f0f43c3c3d0317171723030b0b0b0b0700700c4c02c0e0b1b20f1b0383c3c0e0317030323030b030b03070032303230301c1c131303b17033b00c0b1300f0b0b0f0ec5c2c2c13078704c0704c4c0701c0701c131301f3b4ec7c45c5c2c2c1c01c131301b3b8ec6c85c5c2c2c1c01c000002c2c2c2c000003005c007000000000000005c5c5c5c2c2c2c2c041f00000171717170b0b0b0b0206c0009c9c9c9c13130131305c5c5c5c13078701c0701c1c170701c0704c1c03070705c1c0c070703c1c1c070704c4c17171717070070707107c1d04c4c17171717070070707206c1e01c4c02c4c170b170b0001c0701c0704c4c171717170b0b0700704c4c171717170b0b0700700c0c02c4c030303030000c0c030301c0704c4c030303030b2b2b0b0700700c0c0303030303030303030030303030304c4c02c2c2c4c0b0b0b0b007070b0700b030b0b0b170b0300000701c01c01c01c1c01c1c131305c5c5c5c2c2ccc2c2c2c2c2c2d0b1f0b41c01c131305c5c5c5c2c2c9c2c2c2c2c2c2e0b1b0b81c01c9c9c9c9c070713131700c1313130304c4c0b0f04c0f0b02c4c170b170b04cec1301c13078701c5c170701c07131f104c4d04c4c171717170b0b07007131b204c4e04c4c171717170b0b0700704c4c00b0b00b0b0b0b2f0b00b0b0b0f00b030b0b0b2f0b0300000701c070701c1c01c1c01c1c131305cbcbc5c2c2c2c2ccc2c2c2c2d0b1f0b41c01c131305c9c9c5c2c2c2c2c9c2c2c2c2e0b1b0b81c01c9c9c9c9c13130131305cbcbc5c0701c13078701c0701c070ec1c1c0c07072f00c1c07070f01c070704c4c172f2f170700701c1d071f104c4c172f2f170700701c1e071b200c0c05c0304c0303030302c5c0303030300c0cac0c3c03000303078700c0c0c032f01c0705c5c0303030300c0d031f10b2b2b0b0700700c0c0303030300c0e03032030303030300303030303000000000000870000001e1c000071301c1c1c1c00c00008cac8cdc001c1c1c1c00015c0cac0c001c0c1c0cdc0c8c0c000000c2c2c0c000000300000001c2c1c1c1c1c01c000c5c5c0c2c2c2c2c001c1c1c1c7c1c000c0c0c0c2c0c2c0c001c1c0c1c6c0c8c0c8c0c000000c2c2c0c000000002c2c1c1c1c1c1c1c00000000000000c5c5c0c2c2c2c2c8c7c8d231f23400000c0c0c0c2c0c2c0c8c6c0e231b038008c0c8c0c0000002e1c0c2c2c0c000c017002c000021c003000001c000000001c2c1c1c1c2c1c1c0001c1c01c0000c000c5c5c0c2c2c2c2c041f00007070741c7c1d00030303030b030b030206c0001c1c0e071b0388c0c8c0c5c0c5c0c2c2c2c2c0c2c2c2cac0c2c0b0b0b130b00c0c2c0b2b030307070707070707030707030707070707070701c0c1c030333171733032b2b030b0b0b0b0b0b0b42c7c2d0707070727031703030303030b030b030b0b0382c6c0e0703070327032703170317032f2b1717032b2b03070707071707030307870707030307070707073b070707130707072f07070707070f0707030303171737032f2f032b2b370707070707070741c7c1d03170303030303032b030703070307070381c6c0e3703030ec1304c2f00c5c07070702c5c0b0f00f0b2f030b2b0301705c00c0c0307070303078701c0705c5c2f1f107cbd032f2f030b2b2b0b0700700c5c2f1b206c0e030303030b032b03070033703030317030303031717171703030303070707070303030303030787070707070317030303130303030303032b0303030f030303070317171717030303032b2b2b2b0707070703030340c7c0d0303030303030303030303030303030303030380c0c0e03030303000000000000f0f0b070f0f070700030b0f030000000000331f374cc7cdd00031717030b0f0f0b00271b0389c6c0e00030303030b030f030027032703 26 67108863 11 2047
def hc_60_18 : Nat → Nat := unpackHintV5 0xa4e2549883188bfb2285919a7a32d87491686ef1686951686371785f510859b1685591084ff1684522b43eb99a364a1c30099023eb081d719e1272c007baae0001ee 0xc0c0c4c0e1c4c4c0313131304c4c03c5c5c5c3c3b03171703000ec0705c0705c03170ac2f04c4c07c5d17171031717032b2b372f02f00c4c06c0e1717203030303032b032f003370303031303870303030303130303030313131313030303030303032b030f0303131313130303030303030307032f03032b2b2b2b131313130303030303030340c7c0d2b2b2b2b2f2f2f2f030303030303030303030380c0c0e030303030303030303030303130313030b0b0b0b130b030b0b0b17030b00c0c2c0c2c03030b02c5c0c0c2c2c2c2c2c2c2c0c2c2c0c2c2c2c2c2c0b070b02c1c4c4c4c4c0c5c5c0c2c2c2c2c2c2c2d0b1f0b42c2c2c2c4c0c4c0c0c0c0c0c2c0c2c0c2c2c0e0b1b0382c0c2c0c9c0c9c0c000000305c00000b02c0000c2c2c0c000001700000b0107c0000c5c5c0c2c2c2c2c00081b000030303030b030b030037033f030303031313171313030303130387130f1313130f1313131313031717031313071313130713131313031717032b2b2f131f1344c4c4d13131313031717032b2b372f372f131b0384c4c0e1303130303030303032b032f030337030300c0c02c4c030303030000c0302c0b04c4c030303030b2b2b0b2f02f00c0c0303030303030303030030303030300c0c03c3c030303030000c0303c0f04c4c030303030f0f0f0f2f02f00c0c0303030303030303030030303030300c0c04c4c030303030000c0301c0704c4c030303032b2b2b2b0700700c0c0303030303030303030030303030300c0c0000cbc030302c4c030303030b00b04c4c030303032f02f0b2b2b0b00c0c0303030303003030303030303030300c0c04c4c030303030000c030ac2b1455554100c0c0303030303030303030035500c0c04c4c0303030304c4c030303031f1f1f1f0000c0307c1f0ac2b00c0c0303030303030303030303030300300c0c04c4c030303030000c030ac2b04c4c030303032b2b2b2b2f02f28aaaa82aa00c0c00c0c0303030304c4c03030303030303030000c0300c030ac2704c4c0303030303030303272b2b272f02f00c0c0c0c4c0e1c170303030304c4c0303030300c0c0cac0c0c3c030000cbc030300c030700cbc030ac2b04c4c0303030300c0c0d03031f12b2b2b2b2f02f00c0c0303030300c0c0e03030320303030303003030303030000000ac00030002c00070b0b0b0b000000ac000b00001f001172b2b170b0b0b0b000006c0085cacac5c2c2c2c2c00fcfcfcfc3b0f04c4c03c3c0c3cac030f130f870f0f03c3c3c3c3c3c3c3c000f01c01c2b05c0f03c131300f0f43c7c45cacac5c3c3c3c3c0131300f0f83c6c85cacac5c3c3c3c3c000002c2c2c2c0000017000c007002c00000000b00005c5c5c5c2c2c2c2c1f0010000171717170b0b0b0b06c008009ccc9cfc4c4c4c4c3c4c3e1c3c3c2c4c3c2c5c3c5c2c3c3c3c4c0c2c4c4c5c2c0c2cec4c2c4c2c4c2c5c2c5c2c2c2c2c2c4c2c1c2c2c1c4c4c4c4c5c5c5c5c2c3c3c2c2c4c4d131f0b4cc2c2c4c4c4c4c5c5c5c5c2c3c3c2c2c4c4e131b0b89c2c2c9ccc9c000000305c00000702c0002c2c2c2c00000005c02c00107c0005c5c5c5c2c2c2c2c000206c0005c5c5c5c2c2c2c2c003f3f3f3f0f0f130f170f030f0f0f03131313130f0f0f0f0f0f0f0f130f870f0f170f0f0f0f0f070f0f0f0713131313171717170f0f0f0f0f1f0f43c3c3d13131313171717170f0f0f0f0f1b0f83c3c3e13131313171717170f0f0f0f0030313030003130000b130f1300c0c2c2c3c0c2c2c0c2c2c3c0c2c0008c1c0bc1c05c00c0b02c131308c7c8d231f2340c5c5c5ccc0c2c3c3c2c8c0bc031309c6c0e231b0380c5c0c0c9c0c2c0c3c0c9c00c9c0c8c0c000000c2c2c2c2c0c000000b0b07070b070b0b0000000000000031717030b0b0b0b231f2348c7c8d0000030303030b030b03231b0388c6c0e0023032303 24 16777215 10 1023
def nh_60 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_60_18 (Nat.sub p 576)) (hc_60_17 (Nat.sub p 544)) (Nat.blt p 576)) (hc_60_16 (Nat.sub p 512)) (Nat.blt p 544)) (Bool.rec (hc_60_15 (Nat.sub p 480)) (hc_60_14 (Nat.sub p 448)) (Nat.blt p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (Bool.rec (hc_60_13 (Nat.sub p 416)) (hc_60_12 (Nat.sub p 384)) (Nat.blt p 416)) (hc_60_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_60_10 (Nat.sub p 320)) (hc_60_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 448)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_60_8 (Nat.sub p 256)) (hc_60_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_60_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (hc_60_5 (Nat.sub p 160)) (hc_60_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (hc_60_3 (Nat.sub p 96)) (hc_60_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_60_1 (Nat.sub p 32)) (hc_60_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def f_60 : Nat → Nat × Nat := unpackForestF 0xc5f0062dca2d86514da00c57921a4490d124849124244920a4490512480912404400629c8c954016bf22235005adc849b4016af1f3568fdad47c8d4016a600b4f005a5c749740168e00b438ca2ac6cd5a326b319d688cdb4464d1c014bf1824e0052dc591b22c8c1163610052bc54938014a600a4f88eb744ad122548911c6388d2700292c0148e00a4387dbe43759e1b6b50db5786dab0028fc0147600a3785d270028ce0a8ab0a356829acc235a2116d10534783e36c149560c6c90626482925c148ec012bf04144801a7c00d2e052b90034780c9a400d0e0029d00136004adbf2d85f94dafca3b7ec1fbf51c1f946e009577cda5bec4d1f3686f994e7cc9b00254df0090f8044004a7bdc511e78c6f616479db7bd4511e769ef394e79c9b00252de468af226f004a380250dd7adef037c75eb3baed59d74d6ee24475d31bb4911d74b6ec45a75d1a8024fdd06dee836b74ebe3a0d9dd06c6e81360049db9d1a1c54dee2a6b726be3940fdc98e0e2a6771d2e38a98dc549a009376f1b5b844d1bc6c6de15c6f92db7c94dbc2a8de13600499b74991b68dedc27c6da33b6c9380125eda17c6ca33b6453801256d8370696b3b5a0bdad04ed637069633b54d81a58aed2b5a69a2b34c959a56840092768cb23331bda1288ccc6b679be33c5f1998cece14466631b351999929c0092360a2ab2cd59826b2c9d6864db4304d1d918dac1255639b231c99182496c123b62cb230452d8228ec113b61e343044dd854c8c112f60cb230448c010bec00445a1a7ad0d2d7d0b8b43475ec1a2d0d0d79088b424f5a125aec1716848eb9a645cc122d090d71068b423f5bc122d08ed6d098b42375ac122d08cd6809cb40360042daa6d85534daa9a3b58c9fac51c15346ea993b5791fabc8cd5d8e0a993756d3e2a64bd592f8a992b55d25aacdc15324eaa17c54c9180215d40696a8034501a1a9c1114049ea024b52c2e28091d484c8a402450121a8c0d14047ea202450119a801394125aa003600429a7a5213d2880084f4ec2225d18d390c89736f4dc2225cd3d350c89726f4cc2225c93d31098972374b82725c0d80109694b454a537a525bd2924e0084700421a295bd256f88a567451ab2289ad214888a26347d2222896d1d8b48a23546ca22285ad192888a16345ca222856d152888a1230041fa0adbd056d68857c415b3a0ad8d054de82a6b41533a0a98d0547e82a3b4151ba0a8cd0506c0083b40e341cc9bce64d67f57c3fc9f9fd1c0e64ce7e25c399319cc934f98d07316f3dcae1cc5acf447e7a2333ce381cc59cf12b8731633bd2e1cc4bced2b87312b3ad359d4d40e624e73b5c39cae1cc48c0106e6a36b38c1a1a8d8ce10486a26b37c121a898cdd0486a2333502e1ac96cd64a66b15b358a99ac48cd40a86a036004199a4990c28de6827c30a33984938cd4c86116f32c9a1845acc94f861167318a218c4d0c22c66114b30d2e18451c0105e6007c2de3397c090b74d65e07c2dd3396e92cb90b85ba472dc270020acb56e04f5672c89796449cb16e04f4672bdb013d15c9e6b455c562ad2b13cd08a92984f16b29d2594cdc09e2ce5214c278ad93c55c9e2965026b27da813c51c0104e4e06420637934110818d64bb7c25c3e10319c9508840c6324c321029bc9104840a6b23c3e10299c8d04840a6322c2210293c8149643b5c21c2e10291c844c842024205219051988109c008231fcb20df1bc7d2f837c671ecb20dedbc6f6d63bd7c1dcbe0ded9c7526837b631bda58e45706f68e3794e1bc9b00207c6d0c82ec6f1ac3e0bb19c690c82eb6f175b58cb5f0650f82eb6718c1a0bad8c5d6963005c175a38ba1385d06c0081b0feb78b49c03face2c2680fe378ac9c03f8ce2a2600fe2b8a49a03f6de1fb6b13abe09c9c03f6ce262380fdb18948e03f6b61fb570fda588c9403f68e1fa5a108ab0845503f484201560fd1d00205c3d0c80146f0ec220051ac390f8014670d91d86c8cc35088014630cc32004dbc026d617d7c0bc3e004d9c2749e1635c09d2584e91c294981435409d2184c0d0026c612044009a7804d2c210b80134705d3783cdf0174d60e57c05d338349b0186e80c26405d3182c0d0026860335f04cb000cd5c064be0325b03a3601c580064ae0593b02c9b814090064a60323b01ca000c8dc0224802466008270040d8010260003f 10 11
def ch_60 : Nat → Bool := dagCheckNodeV5 fullMask g_60 ep_60 6 63 bds_60 597 (dagTraceF fullMask rootStock 11 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 fullMask g_60 ep_60 6 63 597 bds_60 (dagTraceF fullMask rootStock 11 f_60) (cur_60 0) (nh_60 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 64 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_2 : treeBlockF 64 96 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_3 : treeBlockF 96 128 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_4 : treeBlockF 128 160 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_5 : treeBlockF 160 192 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_6 : treeBlockF 192 224 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_7 : treeBlockF 224 256 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_8 : treeBlockF 256 288 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_9 : treeBlockF 288 320 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_10 : treeBlockF 320 352 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_11 : treeBlockF 352 384 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_12 : treeBlockF 384 416 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_13 : treeBlockF 416 448 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_14 : treeBlockF 448 480 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_15 : treeBlockF 480 512 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_16 : treeBlockF 512 544 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_17 : treeBlockF 544 576 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_18 : treeBlockF 576 597 ch_60 = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 64 → ch_60 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nj_60_2 : ∀ i, 0 ≤ i → i < 96 → ch_60 i = true := block_join nj_60_1 (fun _ h1 h2 => treeBlockF_at nb_60_2 h1 h2)
theorem nj_60_3 : ∀ i, 0 ≤ i → i < 128 → ch_60 i = true := block_join nj_60_2 (fun _ h1 h2 => treeBlockF_at nb_60_3 h1 h2)
theorem nj_60_4 : ∀ i, 0 ≤ i → i < 160 → ch_60 i = true := block_join nj_60_3 (fun _ h1 h2 => treeBlockF_at nb_60_4 h1 h2)
theorem nj_60_5 : ∀ i, 0 ≤ i → i < 192 → ch_60 i = true := block_join nj_60_4 (fun _ h1 h2 => treeBlockF_at nb_60_5 h1 h2)
theorem nj_60_6 : ∀ i, 0 ≤ i → i < 224 → ch_60 i = true := block_join nj_60_5 (fun _ h1 h2 => treeBlockF_at nb_60_6 h1 h2)
theorem nj_60_7 : ∀ i, 0 ≤ i → i < 256 → ch_60 i = true := block_join nj_60_6 (fun _ h1 h2 => treeBlockF_at nb_60_7 h1 h2)
theorem nj_60_8 : ∀ i, 0 ≤ i → i < 288 → ch_60 i = true := block_join nj_60_7 (fun _ h1 h2 => treeBlockF_at nb_60_8 h1 h2)
theorem nj_60_9 : ∀ i, 0 ≤ i → i < 320 → ch_60 i = true := block_join nj_60_8 (fun _ h1 h2 => treeBlockF_at nb_60_9 h1 h2)
theorem nj_60_10 : ∀ i, 0 ≤ i → i < 352 → ch_60 i = true := block_join nj_60_9 (fun _ h1 h2 => treeBlockF_at nb_60_10 h1 h2)
theorem nj_60_11 : ∀ i, 0 ≤ i → i < 384 → ch_60 i = true := block_join nj_60_10 (fun _ h1 h2 => treeBlockF_at nb_60_11 h1 h2)
theorem nj_60_12 : ∀ i, 0 ≤ i → i < 416 → ch_60 i = true := block_join nj_60_11 (fun _ h1 h2 => treeBlockF_at nb_60_12 h1 h2)
theorem nj_60_13 : ∀ i, 0 ≤ i → i < 448 → ch_60 i = true := block_join nj_60_12 (fun _ h1 h2 => treeBlockF_at nb_60_13 h1 h2)
theorem nj_60_14 : ∀ i, 0 ≤ i → i < 480 → ch_60 i = true := block_join nj_60_13 (fun _ h1 h2 => treeBlockF_at nb_60_14 h1 h2)
theorem nj_60_15 : ∀ i, 0 ≤ i → i < 512 → ch_60 i = true := block_join nj_60_14 (fun _ h1 h2 => treeBlockF_at nb_60_15 h1 h2)
theorem nj_60_16 : ∀ i, 0 ≤ i → i < 544 → ch_60 i = true := block_join nj_60_15 (fun _ h1 h2 => treeBlockF_at nb_60_16 h1 h2)
theorem nj_60_17 : ∀ i, 0 ≤ i → i < 576 → ch_60 i = true := block_join nj_60_16 (fun _ h1 h2 => treeBlockF_at nb_60_17 h1 h2)
theorem nj_60_18 : ∀ i, 0 ≤ i → i < 597 → ch_60 i = true := block_join nj_60_17 (fun _ h1 h2 => treeBlockF_at nb_60_18 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 597 → ch_60 i = true := nj_60_18
theorem lb_60 : LowerBin fullMask rootStock g_60 12 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_59 (kn_cons lb_57 (kn_cons lb_25 (kn_cons lb_52 (kn_cons lb_40 (kn_cons lb_53 (kn_cons lb_54 (kn_cons lb_44 (kn_cons lb_58 (kn_cons lb_56 (kn_cons lb_7 (kn_cons lb_37 (kn_cons lb_50 (kn_cons lb_32 (kn_cons lb_28 (kn_cons lb_26 (kn_cons lb_55 (kn_cons lb_10 (kn_cons lb_12 (kn_cons lb_41 (kn_cons lb_24 (kn_cons lb_34 (kn_cons lb_49 (kn_cons lb_38 (kn_cons lb_36 (kn_cons lb_42 (kn_cons lb_46 (kn_cons lb_9 (kn_cons lb_21 (kn_cons lb_51 (kn_cons lb_19 (kn_cons lb_5 (kn_cons lb_13 (kn_cons lb_47 (kn_cons lb_43 (kn_nil))))))))))))))))))))))))))))))))))))) rc_60 nc_60 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3936395392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241824 * 2 ^ 32 + 3936395392)) (13 - 1) := by
  rw [show canon fullMask (4008241824 * 2 ^ 32 + 3936395392) = g_60 by decide]
  exact lb_60

end PEqualNP.Outside.L_meta_48184

theorem PEqualNP.Outside.L_meta_48184 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241824 * 2 ^ 32 + 3936395392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3936395392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48184.table2_from_lowerBin (4008241824 * 2 ^ 32 + 3936395392) 13 PEqualNP.Outside.L_meta_48184.root_lb PEqualNP.Outside.L_meta_48184.wg 18 rfl PEqualNP.Outside.L_meta_48184.wfits PEqualNP.Outside.L_meta_48184.weval
