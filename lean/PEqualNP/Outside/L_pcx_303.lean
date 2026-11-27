import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_303

open PEqualNP.ProofComplexity PEqualNP.MetaComplexity

abbrev Lit (W : Type) := PEqualNP.ProofComplexity.Literal W
abbrev Cl (W : Type) := PEqualNP.ProofComplexity.Clause W
abbrev LN (V : Type) := Lit (Sum V ℕ)
abbrev CN (V : Type) := Cl (Sum V ℕ)

def negL {W : Type} (l : Lit W) : Lit W := PEqualNP.Search.negLit l

def fLt {W : Type} (l : Lit W) (b : Bool) : Lit W :=
 if b then l else negL l

def upS {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : Set (Lit W) :=
 S ∪ {l | ∃ D ∈ F, l ∈ D ∧ ∀ other ∈ D, other ≠ l → negL other ∈ S}

def sd {V M : Type} (ρ : V → Option Bool) : Set (Lit (Sum V M)) :=
 {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}

lemma negL_negL {W : Type} (l : Lit W) : negL (negL l) = l := by
 cases l with
 | mk v b => cases b <;> rfl

lemma negL_fst {W : Type} (l : Lit W) : (negL l).1 = l.1 := rfl

lemma negL_snd {W : Type} (l : Lit W) : (negL l).2 = !l.2 := rfl

lemma flipLit_true {W : Type} (l : Lit W) : fLt l true = l := rfl

lemma flipLit_false {W : Type} (l : Lit W) : fLt l false = negL l := rfl

lemma negL_flipLit {W : Type} (l : Lit W) (b : Bool) : negL (fLt l b) = fLt l (!b) := by
 cases b
 · simp [fLt, negL_negL]
 · simp [fLt]

lemma eval_negL {W : Type} (α : W → Bool) (l : Lit W) :
   (α (negL l).1 = (negL l).2) ↔ (α l.1 ≠ l.2) := by
 cases l with
 | mk v b =>
   cases b <;> simp [negL, PEqualNP.Search.negLit]

lemma eval_flipLit {W : Type} (α : W → Bool) (l : Lit W) (b : Bool) :
   (α (fLt l b).1 = (fLt l b).2) ↔ ((α l.1 == l.2) = b) := by
 cases l with
 | mk v c =>
   cases b <;> cases c <;> simp [fLt, negL, PEqualNP.Search.negLit]

lemma subset_upStep {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : S ⊆ upS F S :=
 Set.subset_union_left

lemma upStep_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
   (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : upS F1 S1 ⊆ upS F2 S2 := by
 intro l hl
 rcases hl with hl | ⟨D, hD, hlD, hother⟩
 · exact Or.inl (hS hl)
 · exact Or.inr ⟨D, hF hD, hlD, fun o ho hne => hS (hother o ho hne)⟩

lemma upStep_iter_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
   (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : ∀ k : ℕ, (upS F1)^[k] S1 ⊆ (upS F2)^[k] S2
 | 0 => hS
 | k + 1 => by
   rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
   exact upStep_mono hF (upStep_iter_mono hF hS k)

lemma upStep_iter_le {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) {k1 k2 : ℕ}
   (h : k1 ≤ k2) : (upS F)^[k1] S ⊆ (upS F)^[k2] S := by
 induction h with
 | refl => exact Set.Subset.rfl
 | @step m _ ih =>
   rw [Function.iterate_succ_apply']
   exact Set.Subset.trans ih (subset_upStep F _)

lemma upStep_sound {W : Type} {F : Finset (Cl W)} {α : W → Bool}
   (hF : Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
   (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ l ∈ upS F S, α l.1 = l.2 := by
 intro l hl
 rcases hl with hl | ⟨D, hD, hlD, hother⟩
 · exact hS l hl
 · obtain ⟨u, huD, hu⟩ := hF D hD
   by_cases hEq : u = l
   · simpa [hEq] using hu
   · have hneg := hS (negL u) (hother u huD hEq)
     simp only [negL_fst, negL_snd] at hneg
     rw [hu] at hneg
     cases u.2 <;> simp at hneg

lemma upStep_iter_sound {W : Type} {F : Finset (Cl W)} {α : W → Bool}
   (hF : Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
   (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ k : ℕ, ∀ l ∈ (upS F)^[k] S, α l.1 = l.2
 | 0 => hS
 | k + 1 => by
   rw [Function.iterate_succ_apply']
   exact upStep_sound hF (upStep_iter_sound hF hS k)

lemma seedOf_sound {V M : Type} {ρ : V → Option Bool} {a : V → Bool} {aux : M → Bool}
   (hρ : ∀ (v : V) (b : Bool), ρ v = some b → a v = b) :
   ∀ l ∈ (sd ρ : Set (Lit (Sum V M))), Sum.elim a aux l.1 = l.2 := by
 intro l ⟨v, hv, hrv⟩
 rw [hv]
 exact hρ v l.2 hrv

lemma upStep_unit1 {W : Type} {F : Finset (Cl W)} {S : Set (Lit W)} {l : Lit W}
   (hC : ({l} : Cl W) ∈ F) : l ∈ upS F S := by
 refine Or.inr ⟨{l}, hC, Finset.mem_singleton_self l, ?_⟩
 intro o ho hne
 rw [Finset.mem_singleton] at ho
 exact absurd ho hne

lemma upStep_unit2 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)} {a b : Lit W}
   (hC : ({a, b} : Cl W) ∈ F) (ha : negL a ∈ S) : b ∈ upS F S := by
 refine Or.inr ⟨{a, b}, hC, by simp, ?_⟩
 intro o ho hne
 simp only [Finset.mem_insert, Finset.mem_singleton] at ho
 rcases ho with rfl | rfl
 · exact ha
 · exact absurd rfl hne

lemma upStep_unit3 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)} {a b c : Lit W}
   (hC : ({a, b, c} : Cl W) ∈ F) (ha : negL a ∈ S) (hb : negL b ∈ S) : c ∈ upS F S := by
 refine Or.inr ⟨{a, b, c}, hC, by simp, ?_⟩
 intro o ho hne
 simp only [Finset.mem_insert, Finset.mem_singleton] at ho
 rcases ho with rfl | rfl | rfl
 · exact ha
 · exact hb
 · exact absurd rfl hne

abbrev St (V : Type) := ℕ × List (CN V)

def VC {V : Type} (m : ℕ) (C : CN V) : Prop :=
 ∀ l ∈ C, ∀ k : ℕ, l.1 = Sum.inr k → k < m

def VS {V : Type} (st : St V) : Prop :=
 ∀ C ∈ st.2, C.card ≤ 3 ∧ VC st.1 C

lemma VC.mono {V : Type} {m1 m2 : ℕ} (h : m1 ≤ m2) {C : CN V}
   (hV : VC m1 C) : VC m2 C :=
 fun l hl k hk => Nat.lt_of_lt_of_le (hV l hl k hk) h

def fv {V : Type} (st : St V) : LN V × St V :=
 ((Sum.inr st.1, true), (st.1 + 1, st.2))

def addCl {V : Type} (C : CN V) (st : St V) : St V :=
 (st.1, C :: st.2)

def eu {V : Type} [DecidableEq V] (a : LN V) (st : St V) : St V :=
 addCl {a} st

def ei2 {V : Type} [DecidableEq V] (a b : LN V) (st : St V) : St V :=
 addCl {negL a, b} st

def ei3 {V : Type} [DecidableEq V] (a b c : LN V) (st : St V) : St V :=
 addCl {negL a, negL b, c} st

def ec3 {V : Type} [DecidableEq V] (a b c : LN V) (st : St V) : St V :=
 addCl {a, b, c} st

def ea {V : Type} [DecidableEq V] (a b z : LN V) (st : St V) : St V :=
 ei2 z b (ei2 z a (ei3 a b z st))

def eo {V : Type} [DecidableEq V] (a b z : LN V) (st : St V) : St V :=
 ec3 a b (negL z) (ei2 b z (ei2 a z st))

def edg {V : Type} [DecidableEq V] (op : Bool → Bool → Bool)
   (a b z : LN V × LN V) (st : St V) : St V :=
 let c00 := ei3 a.2 b.2 (if op false false then z.1 else z.2) st
 let c01 := ei3 a.2 b.1 (if op false true then z.1 else z.2) c00
 let c10 := ei3 a.1 b.2 (if op true false then z.1 else z.2) c01
 ei3 a.1 b.1 (if op true true then z.1 else z.2) c10

def exr {V : Type} [DecidableEq V] (a b z : LN V) (st : St V) : St V :=
 edg Bool.xor (a, negL a) (b, negL b) (z, negL z) st

def VL {V : Type} (m : ℕ) (l : LN V) : Prop :=
 ∀ k : ℕ, l.1 = Sum.inr k → k < m

lemma VL.mono {V : Type} {m1 m2 : ℕ} (h : m1 ≤ m2) {l : LN V}
   (hl : VL m1 l) : VL m2 l :=
 fun k hk => Nat.lt_of_lt_of_le (hl k hk) h

lemma validLit_negL {V : Type} {m : ℕ} {l : LN V} :
   VL m (negL l) ↔ VL m l := Iff.rfl

lemma validLit_inl {V : Type} (m : ℕ) (v : V) (b : Bool) : VL m (Sum.inl v, b) :=
 fun _ h => by simp at h

lemma validLit_fresh {V : Type} (st : St V) : VL (st.1 + 1) (fv st).1 :=
 fun k hk => by
   simp only [fv, Sum.inr.injEq] at hk
   omega

lemma validSt_fresh {V : Type} {st : St V} (hst : VS st) : VS (fv st).2 :=
 fun C hC => ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_succ st.1)⟩

lemma validSt_addCl {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {C : CN V} (hc : C.card ≤ 3) (hv : VC st.1 C) : VS (addCl C st) := by
 intro D hD
 rcases List.mem_cons.1 hD with rfl | hD
 · exact ⟨hc, hv⟩
 · exact hst D hD

lemma card_singleton_le3 {α : Type} [DecidableEq α] (a : α) : ({a} : Finset α).card ≤ 3 := by
 simp

lemma card_pair_le3 {α : Type} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 3 :=
 (Finset.card_insert_le _ _).trans (by simp)

lemma card_triple_le3 {α : Type} [DecidableEq α] (a b c : α) : ({a, b, c} : Finset α).card ≤ 3 :=
 (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)

lemma validCl_singleton {V : Type} [DecidableEq V] {m : ℕ} {a : LN V}
   (ha : VL m a) : VC m ({a} : CN V) := by
 intro l hl k hk
 rw [Finset.mem_singleton] at hl
 subst hl
 exact ha k hk

lemma validCl_pair {V : Type} [DecidableEq V] {m : ℕ} {a b : LN V}
   (ha : VL m a) (hb : VL m b) : VC m ({a, b} : CN V) := by
 intro l hl k hk
 simp only [Finset.mem_insert, Finset.mem_singleton] at hl
 rcases hl with rfl | rfl
 · exact ha k hk
 · exact hb k hk

lemma validCl_triple {V : Type} [DecidableEq V] {m : ℕ} {a b c : LN V}
   (ha : VL m a) (hb : VL m b) (hc : VL m c) :
   VC m ({a, b, c} : CN V) := by
 intro l hl k hk
 simp only [Finset.mem_insert, Finset.mem_singleton] at hl
 rcases hl with rfl | rfl | rfl
 · exact ha k hk
 · exact hb k hk
 · exact hc k hk

lemma validSt_emitUnit {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a : LN V} (ha : VL st.1 a) : VS (eu a st) :=
 validSt_addCl hst (card_singleton_le3 a) (validCl_singleton ha)

lemma validSt_emitImp2 {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a b : LN V} (ha : VL st.1 a) (hb : VL st.1 b) :
   VS (ei2 a b st) :=
 validSt_addCl hst (card_pair_le3 _ _) (validCl_pair (validLit_negL.2 ha) hb)

lemma validSt_emitImp3 {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a b c : LN V} (ha : VL st.1 a) (hb : VL st.1 b) (hc : VL st.1 c) :
   VS (ei3 a b c st) :=
 validSt_addCl hst (card_triple_le3 _ _ _)
   (validCl_triple (validLit_negL.2 ha) (validLit_negL.2 hb) hc)

lemma validSt_emitCl3 {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a b c : LN V} (ha : VL st.1 a) (hb : VL st.1 b) (hc : VL st.1 c) :
   VS (ec3 a b c st) :=
 validSt_addCl hst (card_triple_le3 _ _ _) (validCl_triple ha hb hc)

lemma validSt_emitAnd {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a b z : LN V} (ha : VL st.1 a) (hb : VL st.1 b) (hz : VL st.1 z) :
   VS (ea a b z st) :=
 validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp3 hst ha hb hz) hz ha) hz hb

lemma validSt_emitOr {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a b z : LN V} (ha : VL st.1 a) (hb : VL st.1 b) (hz : VL st.1 z) :
   VS (eo a b z st) :=
 validSt_emitCl3 (validSt_emitImp2 (validSt_emitImp2 hst ha hz) hb hz) ha hb (validLit_negL.2 hz)

lemma validSt_emitDualGate {V : Type} [DecidableEq V] (op : Bool → Bool → Bool)
   {st : St V} (hst : VS st) {a b z : LN V × LN V}
   (ha1 : VL st.1 a.1) (ha2 : VL st.1 a.2)
   (hb1 : VL st.1 b.1) (hb2 : VL st.1 b.2)
   (hz1 : VL st.1 z.1) (hz2 : VL st.1 z.2) :
   VS (edg op a b z st) := by
 have h1 : VS (ei3 a.2 b.2 (if op false false then z.1 else z.2) st) :=
   validSt_emitImp3 hst ha2 hb2 (by split_ifs <;> assumption)
 have h2 : VS (ei3 a.2 b.1 (if op false true then z.1 else z.2) _) :=
   validSt_emitImp3 h1 ha2 hb1 (by split_ifs <;> assumption)
 have h3 : VS (ei3 a.1 b.2 (if op true false then z.1 else z.2) _) :=
   validSt_emitImp3 h2 ha1 hb2 (by split_ifs <;> assumption)
 exact validSt_emitImp3 h3 ha1 hb1 (by split_ifs <;> assumption)

lemma validSt_emitXor {V : Type} [DecidableEq V] {st : St V} (hst : VS st)
   {a b z : LN V} (ha : VL st.1 a) (hb : VL st.1 b) (hz : VL st.1 z) :
   VS (exr a b z st) :=
 validSt_emitDualGate Bool.xor hst ha (validLit_negL.2 ha) hb (validLit_negL.2 hb)
   hz (validLit_negL.2 hz)

def lEv {W : Type} (α : W → Bool) (l : Lit W) : Bool :=
 α l.1 == l.2

lemma litEval_negL {W : Type} (α : W → Bool) (l : Lit W) :
   lEv α (negL l) = !(lEv α l) := by
 cases l with
 | mk v b =>
   cases h : α v <;> cases b <;> simp [lEv, negL, PEqualNP.Search.negLit, h]

lemma clauseSat_iff {W : Type} (α : W → Bool) (C : Cl W) :
   ClauseSat α C ↔ ∃ l ∈ C, lEv α l = true := by
 simp [ClauseSat, lEv]

lemma clauseSat_singleton {W : Type} [DecidableEq W] (α : W → Bool) (a : Lit W) :
   ClauseSat α {a} ↔ lEv α a = true := by
 simp [ClauseSat, lEv]

lemma clauseSat_pair {W : Type} [DecidableEq W] (α : W → Bool) (a b : Lit W) :
   ClauseSat α {a, b} ↔ lEv α a = true ∨ lEv α b = true := by
 simp [ClauseSat, lEv]

lemma clauseSat_triple {W : Type} [DecidableEq W] (α : W → Bool) (a b c : Lit W) :
   ClauseSat α {a, b, c} ↔ lEv α a = true ∨ lEv α b = true ∨ lEv α c = true := by
 simp [ClauseSat, lEv, or_assoc]

lemma clauseSat_imp2 {W : Type} [DecidableEq W] (α : W → Bool) (a b : Lit W) :
   ClauseSat α {negL a, b} ↔ (lEv α a = true → lEv α b = true) := by
 rw [clauseSat_pair, litEval_negL]
 cases lEv α a <;> cases lEv α b <;> simp

lemma clauseSat_imp3 {W : Type} [DecidableEq W] (α : W → Bool) (a b c : Lit W) :
   ClauseSat α {negL a, negL b, c} ↔ (lEv α a = true → lEv α b = true → lEv α c = true) := by
 rw [clauseSat_triple, litEval_negL, litEval_negL]
 cases lEv α a <;> cases lEv α b <;> cases lEv α c <;> simp

lemma emitAnd_sat_iff {V : Type} [DecidableEq V] (α : Sum V ℕ → Bool)
   (a b z : LN V) (st : St V) :
   (∀ C ∈ (ea a b z st).2, ClauseSat α C) ↔
     (lEv α z = (lEv α a && lEv α b)) ∧ ∀ C ∈ st.2, ClauseSat α C := by
 simp only [ea, ei2, ei3, addCl, List.mem_cons, forall_eq_or_imp,
   clauseSat_imp2, clauseSat_imp3]
 cases lEv α a <;> cases lEv α b <;> cases lEv α z <;> simp <;> tauto

lemma emitOr_sat_iff {V : Type} [DecidableEq V] (α : Sum V ℕ → Bool)
   (a b z : LN V) (st : St V) :
   (∀ C ∈ (eo a b z st).2, ClauseSat α C) ↔
     (lEv α z = (lEv α a || lEv α b)) ∧ ∀ C ∈ st.2, ClauseSat α C := by
 simp only [eo, ec3, ei2, addCl, List.mem_cons, forall_eq_or_imp,
   clauseSat_triple, clauseSat_imp2, litEval_negL]
 cases lEv α a <;> cases lEv α b <;> cases lEv α z <;> simp <;> tauto

lemma emitDualGate_sat_of_both {V : Type} [DecidableEq V] (op : Bool → Bool → Bool)
   (α : Sum V ℕ → Bool) (a b z : LN V × LN V) (st : St V)
   (hz1 : lEv α z.1 = true) (hz2 : lEv α z.2 = true)
   (hst : ∀ C ∈ st.2, ClauseSat α C) :
   ∀ C ∈ (edg op a b z st).2, ClauseSat α C := by
 simp only [edg, ei3, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp3]
 refine ⟨?_, ?_, ?_, ?_, hst⟩ <;> intros <;> split_ifs <;> assumption

lemma emitDualGate_sat_of_exact {V : Type} [DecidableEq V] (op : Bool → Bool → Bool)
   (α : Sum V ℕ → Bool) (a b z : LN V × LN V) (st : St V)
   (va vb : Bool)
   (ha1 : lEv α a.1 = va) (ha2 : lEv α a.2 = !va)
   (hb1 : lEv α b.1 = vb) (hb2 : lEv α b.2 = !vb)
   (hz1 : lEv α z.1 = op va vb) (hz2 : lEv α z.2 = !(op va vb))
   (hst : ∀ C ∈ st.2, ClauseSat α C) :
   ∀ C ∈ (edg op a b z st).2, ClauseSat α C := by
 simp only [edg, ei3, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp3]
 refine ⟨?_, ?_, ?_, ?_, hst⟩ <;>
   (intro h1 h2; cases va <;> cases vb <;> cases hop : op _ _ <;> simp_all)

lemma emitDualGate_sat_to_exact {V : Type} [DecidableEq V] (op : Bool → Bool → Bool)
   (α : Sum V ℕ → Bool) (a b z : LN V × LN V) (st : St V)
   (va vb : Bool)
   (ha1 : lEv α a.1 = va) (ha2 : lEv α a.2 = !va)
   (hb1 : lEv α b.1 = vb) (hb2 : lEv α b.2 = !vb)
   (hnot : ¬ (lEv α z.1 = true ∧ lEv α z.2 = true))
   (hclauses : ∀ C ∈ (edg op a b z st).2, ClauseSat α C) :
   lEv α z.1 = op va vb ∧ lEv α z.2 = !(op va vb) := by
 simp only [edg, ei3, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp3] at hclauses
 rcases hclauses with ⟨h00, h01, h10, h11, _⟩
 cases va <;> cases vb <;> cases hzv : op _ _ <;> cases hz1 : lEv α z.1 <;>
   cases hz2 : lEv α z.2 <;> simp_all

lemma emitXor_sat_iff {V : Type} [DecidableEq V] (α : Sum V ℕ → Bool)
   (a b z : LN V) (st : St V) :
   (∀ C ∈ (exr a b z st).2, ClauseSat α C) ↔
     (lEv α z = (lEv α a ^^ lEv α b)) ∧ ∀ C ∈ st.2, ClauseSat α C := by
 simp only [exr, edg, ei3, addCl, List.mem_cons, forall_eq_or_imp,
   clauseSat_imp3, litEval_negL]
 cases ha : lEv α a <;> cases hb : lEv α b <;> cases hz : lEv α z <;>
   simp [ha, hb, hz, litEval_negL] <;> tauto

inductive BTree (α : Type) where
 | leaf (a : α) : BTree α
 | node (l r : BTree α) : BTree α

def BTree.depth {α : Type} : BTree α → ℕ
 | .leaf _ => 0
 | .node l r => max l.depth r.depth + 1

def BTree.nodes {α : Type} : BTree α → ℕ
 | .leaf _ => 1
 | .node l r => 1 + l.nodes + r.nodes

def BTree.leaves {α : Type} : BTree α → List α
 | .leaf a => [a]
 | .node l r => l.leaves ++ r.leaves

lemma BTree.mem_leaves_node_left {α : Type} {l r : BTree α} {x : α} (hx : x ∈ l.leaves) :
   x ∈ (BTree.node l r).leaves :=
 List.mem_append_left _ hx

lemma BTree.mem_leaves_node_right {α : Type} {l r : BTree α} {x : α} (hx : x ∈ r.leaves) :
   x ∈ (BTree.node l r).leaves :=
 List.mem_append_right _ hx

def BTree.ofList {α : Type} (L : List α) (hL : L ≠ []) : BTree α :=
 if h1 : L.length ≤ 1 then
   match L, hL with
   | a :: _, _ => BTree.leaf a
 else
   let mid := L.length / 2
   have hm0 : 0 < mid := by omega
   have hm1 : mid < L.length := by omega
   have hL1 : L.take mid ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_take_of_le (by omega), List.length_nil] at this
     omega
   have hL2 : L.drop mid ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_drop, List.length_nil] at this
     omega
   BTree.node (BTree.ofList (L.take mid) hL1) (BTree.ofList (L.drop mid) hL2)
termination_by L.length
decreasing_by
 · rw [List.length_take_of_le (by omega)]; omega
 · rw [List.length_drop]; omega

lemma BTree.leaves_ofList {α : Type} : ∀ (L : List α) (hL : L ≠ []),
   (BTree.ofList L hL).leaves = L
 | [], hL => absurd rfl hL
 | [a], _ => by
   rw [BTree.ofList]
   simp [BTree.leaves]
 | a :: b :: rest, hL => by
   have h1 : ¬ ((a :: b :: rest).length ≤ 1) := by simp
   rw [BTree.ofList]
   simp only [h1, ↓reduceDIte]
   have hL1 : (a :: b :: rest).take ((a :: b :: rest).length / 2) ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_take_of_le (Nat.div_le_self _ _)] at this
     simp at this
   have hL2 : (a :: b :: rest).drop ((a :: b :: rest).length / 2) ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_drop] at this
     simp at this
     omega
   change (BTree.ofList ((a :: b :: rest).take ((a :: b :: rest).length / 2)) hL1).leaves ++
     (BTree.ofList ((a :: b :: rest).drop ((a :: b :: rest).length / 2)) hL2).leaves = a :: b :: rest
   rw [BTree.leaves_ofList _ hL1, BTree.leaves_ofList _ hL2, List.take_append_drop]
termination_by L => L.length
decreasing_by
 · rw [List.length_take_of_le (Nat.div_le_self _ _)]; simp; omega
 · rw [List.length_drop]; simp; omega

lemma BTree.nodes_ofList {α : Type} : ∀ (L : List α) (hL : L ≠ []),
   (BTree.ofList L hL).nodes + 1 ≤ 2 * L.length
 | [], hL => absurd rfl hL
 | [a], _ => by
   rw [BTree.ofList]
   simp [BTree.nodes]
 | a :: b :: rest, hL => by
   have h1 : ¬ ((a :: b :: rest).length ≤ 1) := by simp
   rw [BTree.ofList]
   simp only [h1, ↓reduceDIte]
   have hL1 : (a :: b :: rest).take ((a :: b :: rest).length / 2) ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_take_of_le (Nat.div_le_self _ _)] at this
     simp at this
   have hL2 : (a :: b :: rest).drop ((a :: b :: rest).length / 2) ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_drop] at this
     simp at this
     omega
   have ih1 := BTree.nodes_ofList ((a :: b :: rest).take ((a :: b :: rest).length / 2)) hL1
   have ih2 := BTree.nodes_ofList ((a :: b :: rest).drop ((a :: b :: rest).length / 2)) hL2
   have hlen1 : ((a :: b :: rest).take ((a :: b :: rest).length / 2)).length = (a :: b :: rest).length / 2 :=
     List.length_take_of_le (Nat.div_le_self _ _)
   have hlen2 : ((a :: b :: rest).drop ((a :: b :: rest).length / 2)).length =
       (a :: b :: rest).length - (a :: b :: rest).length / 2 :=
     List.length_drop
   change 1 + (BTree.ofList _ hL1).nodes + (BTree.ofList _ hL2).nodes + 1 ≤ 2 * (a :: b :: rest).length
   omega
termination_by L => L.length
decreasing_by
 · rw [List.length_take_of_le (Nat.div_le_self _ _)]; simp; omega
 · rw [List.length_drop]; simp; omega

lemma clog2_half_le {m : ℕ} (hm : 2 ≤ m) :
   Nat.clog 2 (m / 2) + 1 ≤ Nat.clog 2 m ∧ Nat.clog 2 (m - m / 2) + 1 ≤ Nat.clog 2 m := by
 set d := Nat.clog 2 m
 have hd : 1 ≤ d := by
   have h1 : Nat.clog 2 2 ≤ d := Nat.clog_mono_right 2 hm
   have h2 : Nat.clog 2 2 = 1 := by decide
   omega
 have hpow : m ≤ 2 ^ d := (Nat.clog_le_iff_le_pow (by omega)).1 le_rfl
 have hpow2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
   have : d = (d - 1) + 1 := by omega
   conv_lhs => rw [this, pow_succ']
 have h1 : m / 2 ≤ 2 ^ (d - 1) := by omega
 have h2 : m - m / 2 ≤ 2 ^ (d - 1) := by omega
 have hc1 : Nat.clog 2 (m / 2) ≤ d - 1 := (Nat.clog_le_iff_le_pow (by omega)).2 h1
 have hc2 : Nat.clog 2 (m - m / 2) ≤ d - 1 := (Nat.clog_le_iff_le_pow (by omega)).2 h2
 omega

lemma BTree.depth_ofList {α : Type} : ∀ (L : List α) (hL : L ≠ []),
   (BTree.ofList L hL).depth ≤ Nat.clog 2 L.length
 | [], hL => absurd rfl hL
 | [a], _ => by
   rw [BTree.ofList]
   simp [BTree.depth]
 | a :: b :: rest, hL => by
   have h1 : ¬ ((a :: b :: rest).length ≤ 1) := by simp
   rw [BTree.ofList]
   simp only [h1, ↓reduceDIte]
   have hm : 2 ≤ (a :: b :: rest).length := by simp
   have hL1 : (a :: b :: rest).take ((a :: b :: rest).length / 2) ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_take_of_le (Nat.div_le_self _ _)] at this
     simp at this
   have hL2 : (a :: b :: rest).drop ((a :: b :: rest).length / 2) ≠ [] := by
     intro h
     have := congrArg List.length h
     rw [List.length_drop] at this
     simp at this
     omega
   have ih1 := BTree.depth_ofList ((a :: b :: rest).take ((a :: b :: rest).length / 2)) hL1
   have ih2 := BTree.depth_ofList ((a :: b :: rest).drop ((a :: b :: rest).length / 2)) hL2
   have hlen1 : ((a :: b :: rest).take ((a :: b :: rest).length / 2)).length = (a :: b :: rest).length / 2 :=
     List.length_take_of_le (Nat.div_le_self _ _)
   have hlen2 : ((a :: b :: rest).drop ((a :: b :: rest).length / 2)).length =
       (a :: b :: rest).length - (a :: b :: rest).length / 2 :=
     List.length_drop
   rw [hlen1] at ih1
   rw [hlen2] at ih2
   obtain ⟨hc1, hc2⟩ := clog2_half_le hm
   change max (BTree.ofList _ hL1).depth (BTree.ofList _ hL2).depth + 1 ≤ Nat.clog 2 (a :: b :: rest).length
   omega
termination_by L => L.length
decreasing_by
 · rw [List.length_take_of_le (Nat.div_le_self _ _)]; simp; omega
 · rw [List.length_drop]; simp; omega

def wv (n : ℕ) (x : Fin n → Bool) (gs : List BinaryGate) : ℕ → Bool
 | u =>
   if h : u < n then x ⟨u, h⟩
   else if h2 : u < n + gs.length then
     let g := gs[u - n]'(by omega)
     let lv := if g.left < u then wv n x gs g.left else false
     let rv := if g.right < u then wv n x gs g.right else false
     g.op lv rv
   else false

def dv (n : ℕ) (gs : List BinaryGate) : ℕ → ℕ
 | u =>
   if h1 : u < n then 0
   else if h2 : u < n + gs.length then
     let g := gs[u - n]'(by omega)
     let ld := if g.left < u then dv n gs g.left else 0
     let rd := if g.right < u then dv n gs g.right else 0
     max ld rd + 1
   else 0

lemma wireValAux_snoc (n : ℕ) (x : Fin n → Bool) (gs : List BinaryGate)
   (g : BinaryGate) :
   ∀ u : ℕ, u < n + gs.length → wv n x (gs ++ [g]) u = wv n x gs u := by
 intro u
 induction u using Nat.strong_induction_on with
 | ind u ih =>
   intro hu
   rw [wv, wv]
   by_cases h1 : u < n
   · simp [h1]
   · have hu' : u < n + (gs ++ [g]).length := by simp; omega
     simp only [h1, ↓reduceDIte, hu, hu']
     have hk : u - n < gs.length := by omega
     have hget : (gs ++ [g])[u - n]'(by simp; omega) = gs[u - n]'hk :=
       List.getElem_append_left hk
     simp only [hget]
     congr 1
     · split_ifs with hl
       · exact ih _ hl (by omega)
       · rfl
     · split_ifs with hr
       · exact ih _ hr (by omega)
       · rfl

lemma depthValAux_snoc (n : ℕ) (gs : List BinaryGate)
   (g : BinaryGate) :
   ∀ u : ℕ, u < n + gs.length → dv n (gs ++ [g]) u = dv n gs u := by
 intro u
 induction u using Nat.strong_induction_on with
 | ind u ih =>
   intro hu
   rw [dv, dv]
   by_cases h1 : u < n
   · simp [h1]
   · have hu' : u < n + (gs ++ [g]).length := by simp; omega
     simp only [h1, ↓reduceDIte, hu, hu']
     have hk : u - n < gs.length := by omega
     have hget : (gs ++ [g])[u - n]'(by simp; omega) = gs[u - n]'hk :=
       List.getElem_append_left hk
     simp only [hget]
     congr 1
     congr 1
     · split_ifs with hl
       · exact ih _ hl (by omega)
       · rfl
     · split_ifs with hr
       · exact ih _ hr (by omega)
       · rfl

lemma wires_length_and_getD (n : ℕ) (x : Fin n → Bool) (gs : List BinaryGate) :
   let ws := (⟨gs, 0⟩ : BinaryCircuit).wires (List.ofFn x)
   ws.length = n + gs.length ∧ ∀ u : ℕ, ws.getD u false = wv n x gs u := by
 induction gs using List.reverseRecOn with
 | nil =>
   simp only [BinaryCircuit.wires, List.foldl_nil, List.length_ofFn,
     List.length_nil, add_zero, true_and]
   intro u
   rw [wv]
   by_cases hu : u < n
   · simp [hu, List.getD_eq_getElem?_getD]
   · simp [hu, List.getD_eq_getElem?_getD]
 | append_singleton gs g ih =>
   rcases ih with ⟨hlen, hget⟩
   have hfold : (⟨gs ++ [g], 0⟩ : BinaryCircuit).wires (List.ofFn x) =
       let prev := (⟨gs, 0⟩ : BinaryCircuit).wires (List.ofFn x)
       prev ++ [g.op (prev.getD g.left false) (prev.getD g.right false)] := by
     simp [BinaryCircuit.wires]
   rw [hfold]
   set prev := (⟨gs, 0⟩ : BinaryCircuit).wires (List.ofFn x)
   refine ⟨by simp [hlen]; omega, fun u => ?_⟩
   by_cases hu : u < n + gs.length
   · have h1 : prev.getD u false = (prev ++ [g.op (prev.getD g.left false) (prev.getD g.right false)]).getD u false := by
       simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < prev.length)]
     rw [← h1, hget u, wireValAux_snoc n x gs g u hu]
   · by_cases heq : u = n + gs.length
     · subst heq
       have hlen' : prev.length = n + gs.length := hlen
       have h1 : (prev ++ [g.op (prev.getD g.left false) (prev.getD g.right false)]).getD (n + gs.length) false =
           g.op (prev.getD g.left false) (prev.getD g.right false) := by
         simp [List.getD_eq_getElem?_getD, hlen']
       rw [h1, wv]
       have hnotn : ¬ (n + gs.length < n) := by omega
       have hlt : n + gs.length < n + (gs ++ [g]).length := by simp
       simp only [hnotn, ↓reduceDIte, hlt, Nat.add_sub_cancel_left]
       have hgetg : (gs ++ [g])[gs.length]'(by simp) = g := by simp
       simp only [hgetg]
       congr 1
       · by_cases hl : g.left < n + gs.length
         · rw [hget g.left, wireValAux_snoc n x gs g g.left hl]
           simp [hl]
         · simp only [hl, ↓reduceIte]
           simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : prev.length ≤ g.left)]
       · by_cases hr : g.right < n + gs.length
         · rw [hget g.right, wireValAux_snoc n x gs g g.right hr]
           simp [hr]
         · simp only [hr, ↓reduceIte]
           simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : prev.length ≤ g.right)]
     · have hge : (prev ++ [g.op (prev.getD g.left false) (prev.getD g.right false)]).length ≤ u := by
         simp; omega
       rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
       rw [wv]
       have h1 : ¬ (u < n) := by omega
       have h2 : ¬ (u < n + (gs ++ [g]).length) := by simp; omega
       simp only [h1, ↓reduceDIte, h2, Option.getD_none]

lemma depths_length_and_getD (n : ℕ) (gs : List BinaryGate) :
   let ds := gs.foldl (fun (w : List ℕ) g =>
     w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
   ds.length = n + gs.length ∧ ∀ u : ℕ, ds.getD u 0 = dv n gs u := by
 induction gs using List.reverseRecOn with
 | nil =>
   simp only [List.foldl_nil, List.length_replicate, List.length_nil, add_zero, true_and]
   intro u
   rw [dv]
   by_cases hu : u < n
   · simp [hu, List.getD_eq_getElem?_getD]
   · simp [hu, List.getD_eq_getElem?_getD]
 | append_singleton gs g ih =>
   rcases ih with ⟨hlen, hget⟩
   have hfold : (gs ++ [g]).foldl (fun (w : List ℕ) g =>
       w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0) =
       let prev := gs.foldl (fun (w : List ℕ) g =>
         w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
       prev ++ [max (prev.getD g.left 0) (prev.getD g.right 0) + 1] := by
     rw [List.foldl_concat]
   rw [hfold]
   set prev := gs.foldl (fun (w : List ℕ) g =>
     w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
   refine ⟨by simp [hlen]; omega, fun u => ?_⟩
   by_cases hu : u < n + gs.length
   · have h1 : prev.getD u 0 = (prev ++ [max (prev.getD g.left 0) (prev.getD g.right 0) + 1]).getD u 0 := by
       simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < prev.length)]
     rw [← h1, hget u, depthValAux_snoc n gs g u hu]
   · by_cases heq : u = n + gs.length
     · subst heq
       have h1 : (prev ++ [max (prev.getD g.left 0) (prev.getD g.right 0) + 1]).getD (n + gs.length) 0 =
           max (prev.getD g.left 0) (prev.getD g.right 0) + 1 := by
         simp [List.getD_eq_getElem?_getD, hlen]
       rw [h1, dv]
       have hnotn : ¬ (n + gs.length < n) := by omega
       have hlt : n + gs.length < n + (gs ++ [g]).length := by simp
       simp only [hnotn, ↓reduceDIte, hlt, Nat.add_sub_cancel_left]
       have hgetg : (gs ++ [g])[gs.length]'(by simp) = g := by simp
       simp only [hgetg]
       congr 1
       congr 1
       · by_cases hl : g.left < n + gs.length
         · rw [hget g.left, depthValAux_snoc n gs g g.left hl]
           simp [hl]
         · simp only [hl, ↓reduceIte]
           simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : prev.length ≤ g.left)]
       · by_cases hr : g.right < n + gs.length
         · rw [hget g.right, depthValAux_snoc n gs g g.right hr]
           simp [hr]
         · simp only [hr, ↓reduceIte]
           simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : prev.length ≤ g.right)]
     · have hge : (prev ++ [max (prev.getD g.left 0) (prev.getD g.right 0) + 1]).length ≤ u := by
         simp; omega
       rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
       rw [dv]
       have h1 : ¬ (u < n) := by omega
       have h2 : ¬ (u < n + (gs ++ [g]).length) := by simp; omega
       simp only [h1, ↓reduceDIte, h2, Option.getD_none]

def mapVar {V : Type} (m : ℕ) (hm : 0 < m) : Sum V ℕ → Sum V (Fin m)
 | Sum.inl v => Sum.inl v
 | Sum.inr k => Sum.inr (if h : k < m then ⟨k, h⟩ else ⟨0, hm⟩)

def mapLit {V : Type} (m : ℕ) (hm : 0 < m) (l : LN V) : Lit (Sum V (Fin m)) :=
 (mapVar m hm l.1, l.2)

def mapCl {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (C : CN V) : Cl (Sum V (Fin m)) :=
 C.image (mapLit m hm)

lemma mapLit_negL {V : Type} (m : ℕ) (hm : 0 < m) (l : LN V) :
   mapLit m hm (negL l) = negL (mapLit m hm l) := rfl

lemma mapCl_card_le {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (C : CN V) :
   (mapCl m hm C).card ≤ C.card := Finset.card_image_le

lemma mapCl_sat_of_nat {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (a : V → Bool)
   (aux : ℕ → Bool) {C : CN V} (hV : VC m C)
   (hsat : ClauseSat (Sum.elim a aux) C) :
   ClauseSat (Sum.elim a (fun k : Fin m => aux k.val)) (mapCl m hm C) := by
 obtain ⟨l, hlC, hl⟩ := hsat
 refine ⟨mapLit m hm l, Finset.mem_image.2 ⟨l, hlC, rfl⟩, ?_⟩
 cases hx : l.1 with
 | inl v => simpa [mapLit, mapVar, hx] using hl
 | inr k =>
   have hk : k < m := hV l hlC k hx
   simpa [mapLit, mapVar, hx, hk] using hl

lemma mapCl_sat_to_nat {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (a : V → Bool)
   (aux : Fin m → Bool) {C : CN V} (hV : VC m C)
   (hsat : ClauseSat (Sum.elim a aux) (mapCl m hm C)) :
   ClauseSat (Sum.elim a (fun k => if h : k < m then aux ⟨k, h⟩ else false)) C := by
 obtain ⟨l', hl'C, hl'⟩ := hsat
 rcases Finset.mem_image.1 hl'C with ⟨l, hlC, rfl⟩
 refine ⟨l, hlC, ?_⟩
 cases hx : l.1 with
 | inl v => simpa [mapLit, mapVar, hx] using hl'
 | inr k =>
   have hk : k < m := hV l hlC k hx
   simpa [mapLit, mapVar, hx, hk] using hl'

lemma upStep_map_transport {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m)
   (Fnat : Finset (CN V)) (Ffin : Finset (Cl (Sum V (Fin m))))
   (himg : ∀ C ∈ Fnat, mapCl m hm C ∈ Ffin)
   (ρ : V → Option Bool) :
   ∀ k : ℕ, ∀ l ∈ (upS Fnat)^[k] (sd ρ),
     mapLit m hm l ∈ (upS Ffin)^[k] (sd ρ)
 | 0, l, hl => by
   rcases hl with ⟨v, hv, hrv⟩
   refine ⟨v, ?_, hrv⟩
   simp [mapLit, mapVar, hv]
 | k + 1, l, hl => by
   rw [Function.iterate_succ_apply'] at hl ⊢
   rcases hl with hl | ⟨D, hD, hlD, hother⟩
   · exact Or.inl (upStep_map_transport m hm Fnat Ffin himg ρ k l hl)
   · refine Or.inr ⟨mapCl m hm D, himg D hD, Finset.mem_image.2 ⟨l, hlD, rfl⟩, ?_⟩
     intro o' ho' hne'
     rcases Finset.mem_image.1 ho' with ⟨o, hoD, rfl⟩
     have hne : o ≠ l := fun h => hne' (by rw [h])
     have hprev := hother o hoD hne
     rw [← mapLit_negL m hm o]
     exact upStep_map_transport m hm Fnat Ffin himg ρ k (negL o) hprev

lemma sum_toFinset_card_le {α : Type} [DecidableEq α] (L : List (Finset α)) :
   (∑ D ∈ L.toFinset, D.card) ≤ (L.map Finset.card).sum := by
 induction L with
 | nil => simp
 | cons a rest ih =>
   simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
   by_cases ha : a ∈ rest.toFinset
   · rw [Finset.insert_eq_of_mem ha]
     omega
   · rw [Finset.sum_insert ha]
     omega

lemma sum_map_card_le {α : Type} (L : List (Finset α)) (b : ℕ)
   (hb : ∀ D ∈ L, D.card ≤ b) : (L.map Finset.card).sum ≤ b * L.length := by
 induction L with
 | nil => simp
 | cons a rest ih =>
   simp only [List.map_cons, List.sum_cons, List.length_cons]
   have ha := hb a (List.mem_cons_self ..)
   have hr := ih (fun D hD => hb D (List.mem_cons_of_mem a hD))
   nlinarith

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_xor (a b : Bool) : b2z (a ^^ b) = b2z a + b2z b := by
 cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
 cases a <;> cases b <;> decide

lemma b2z_injective : Function.Injective b2z := by
 intro a b h
 cases a <;> cases b <;> simp_all [b2z]

def xl : List Bool → Bool
 | [] => false
 | b :: rest => b ^^ xl rest

lemma b2z_xorList (L : List Bool) : b2z (xl L) = (L.map b2z).sum := by
 induction L with
 | nil => simp [xl, b2z]
 | cons a rest ih =>
   simp only [xl, b2z_xor, ih, List.map_cons, List.sum_cons]

lemma b2z_xorFin : ∀ {k : ℕ} (f : Fin k → Bool),
   b2z (xl (List.ofFn f)) = ∑ q : Fin k, b2z (f q)
 | 0, f => by simp [xl, b2z]
 | k + 1, f => by
   rw [List.ofFn_succ, xl, b2z_xor, b2z_xorFin (fun i => f i.succ), Fin.sum_univ_succ]

abbrev Mat (h' n : ℕ) := Fin h' → Fin n → ZMod 2

def linOfMat {h' n : ℕ} (U : Finset (Fin n)) (M : Mat h' n) :
   (U → ZMod 2) →ₗ[ZMod 2] (Fin h' → ZMod 2) where
 toFun x q := ∑ i : U, M q i.1 * x i
 map_add' x y := by
   ext q
   simp [mul_add, Finset.sum_add_distrib]
 map_smul' c x := by
   ext q
   simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
   refine Finset.sum_congr rfl fun i _ => ?_
   ring

def GoodMat {h' n : ℕ} (U : Finset (Fin n)) (M : Mat h' n) : Prop :=
 Function.Injective (linOfMat U M)

lemma goodMat_mono {h' n : ℕ} {U' U : Finset (Fin n)} {M : Mat h' n}
   (hsub : U' ⊆ U) (hgood : GoodMat U M) : GoodMat U' M := by
 classical
 intro x y hxy
 let extX : U → ZMod 2 := fun i => if hi : i.1 ∈ U' then x ⟨i.1, hi⟩ else 0
 let extY : U → ZMod 2 := fun i => if hi : i.1 ∈ U' then y ⟨i.1, hi⟩ else 0
 have hlinX : linOfMat U M extX = linOfMat U' M x := by
   ext q
   simp only [linOfMat, LinearMap.coe_mk, AddHom.coe_mk]
   have h1 : (∑ i : U, M q i.1 * extX i) = ∑ i ∈ U.attach, M q i.1 * extX i := rfl
   rw [h1, Finset.sum_attach U (fun i => M q i * if hi : i ∈ U' then x ⟨i, hi⟩ else 0)]
   have hsum1 : (∑ i ∈ U, M q i * (if hi : i ∈ U' then x ⟨i, hi⟩ else 0)) =
       ∑ i ∈ U', M q i * (if hi : i ∈ U' then x ⟨i, hi⟩ else 0) := by
     refine (Finset.sum_subset hsub ?_).symm
     intro i _ hiU'
     simp [hiU']
   rw [hsum1]
   have h2 : (∑ i : U', M q i.1 * x i) =
       ∑ i ∈ U', M q i * (if hi : i ∈ U' then x ⟨i, hi⟩ else 0) := by
     rw [← Finset.sum_attach U' (fun i => M q i * (if hi : i ∈ U' then x ⟨i, hi⟩ else 0))]
     refine Finset.sum_congr rfl fun i _ => ?_
     simp [i.2]
   exact h2.symm
 have hlinY : linOfMat U M extY = linOfMat U' M y := by
   ext q
   simp only [linOfMat, LinearMap.coe_mk, AddHom.coe_mk]
   have h1 : (∑ i : U, M q i.1 * extY i) = ∑ i ∈ U.attach, M q i.1 * extY i := rfl
   rw [h1, Finset.sum_attach U (fun i => M q i * if hi : i ∈ U' then y ⟨i, hi⟩ else 0)]
   have hsum1 : (∑ i ∈ U, M q i * (if hi : i ∈ U' then y ⟨i, hi⟩ else 0)) =
       ∑ i ∈ U', M q i * (if hi : i ∈ U' then y ⟨i, hi⟩ else 0) := by
     refine (Finset.sum_subset hsub ?_).symm
     intro i _ hiU'
     simp [hiU']
   rw [hsum1]
   have h2 : (∑ i : U', M q i.1 * y i) =
       ∑ i ∈ U', M q i * (if hi : i ∈ U' then y ⟨i, hi⟩ else 0) := by
     rw [← Finset.sum_attach U' (fun i => M q i * (if hi : i ∈ U' then y ⟨i, hi⟩ else 0))]
     refine Finset.sum_congr rfl fun i _ => ?_
     simp [i.2]
   exact h2.symm
 have heq : extX = extY := hgood (hlinX.trans (hxy.trans hlinY.symm))
 ext i
 have := congrFun heq ⟨i.1, hsub i.2⟩
 simpa [extX, extY, i.2] using this

lemma goodMat_dual_vec {h' n : ℕ} {U' : Finset (Fin n)} {M : Mat h' n}
   (hgood : GoodMat U' M) {i : Fin n} (hi : i ∈ U') :
   ∃ c : Fin h' → Bool, ∀ j ∈ U',
     xl (List.ofFn (fun q : Fin h' => c q && decide (M q j = 1))) = decide (j = i) := by
 classical
 let f := linOfMat U' M
 have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.2 hgood
 obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hker
 let iU : U' := ⟨i, hi⟩
 let cz : Fin h' → ZMod 2 := fun q => (g (Pi.single q 1)) iU
 let c : Fin h' → Bool := fun q => decide (cz q = 1)
 refine ⟨c, fun j hj => ?_⟩
 apply b2z_injective
 rw [b2z_xorFin]
 have hsingle : ∀ z : ZMod 2, b2z (decide (z = 1)) = z := by
   intro z
   fin_cases z <;> rfl
 have hcalc : (∑ q : Fin h', b2z (c q && decide (M q j = 1))) = ∑ q : Fin h', cz q * M q j := by
   refine Finset.sum_congr rfl fun q _ => ?_
   rw [b2z_and, hsingle (cz q), hsingle (M q j)]
 rw [hcalc]
 let jU : U' := ⟨j, hj⟩
 have hfj : f (Pi.single jU 1) = ∑ q : Fin h', M q j • (Pi.single q 1 : Fin h' → ZMod 2) := by
   ext q
   simp only [f, linOfMat, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
     smul_eq_mul, Pi.single_apply]
   have hL : (∑ x : U', M q x.1 * (if x = jU then (1 : ZMod 2) else 0)) = M q j := by
     rw [Finset.sum_eq_single jU]
     · simp [jU]
     · intro x _ hx; simp [hx]
     · intro h; exact absurd (Finset.mem_univ jU) h
   have hR : (∑ x : Fin h', M x j * (if q = x then (1 : ZMod 2) else 0)) = M q j := by
     rw [Finset.sum_eq_single q]
     · simp
     · intro x _ hx; simp [hx.symm]
     · intro h; exact absurd (Finset.mem_univ q) h
   rw [hL, hR]
 have hgf : g (f (Pi.single jU 1)) = Pi.single jU 1 := LinearMap.congr_fun hg (Pi.single jU 1)
 have hev := congrFun hgf iU
 rw [hfj, map_sum] at hev
 simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hev
 have hcomm : (∑ q : Fin h', cz q * M q j) = ∑ q : Fin h', M q j * cz q := by
   refine Finset.sum_congr rfl fun q _ => mul_comm _ _
 rw [hcomm, hev]
 by_cases hji : j = i
 · have hjei : jU = iU := Subtype.ext hji
   simp [hji, hjei, b2z]
 · have hjei : jU ≠ iU := fun h => hji (congrArg Subtype.val h)
   have hne : iU ≠ jU := hjei.symm
   simp [hji, hne, b2z]

lemma linearIndependent_snoc_iff {h' k : ℕ} (A : Fin k → (Fin h' → ZMod 2))
   (v : Fin h' → ZMod 2) :
   LinearIndependent (ZMod 2) (Fin.snoc A v) ↔
     LinearIndependent (ZMod 2) A ∧ v ∉ Submodule.span (ZMod 2) (Set.range A) := by
 constructor
 · intro hli
   constructor
   · rw [Fintype.linearIndependent_iff] at hli ⊢
     intro g hg i
     let g' : Fin (k + 1) → ZMod 2 := Fin.snoc g 0
     have hg' : ∑ j : Fin (k + 1), g' j • Fin.snoc (α := fun _ => Fin h' → ZMod 2) A v j = 0 := by
       rw [Fin.sum_univ_castSucc]
       have h1 : (∑ j : Fin k, g' j.castSucc • Fin.snoc (α := fun _ => Fin h' → ZMod 2) A v j.castSucc) =
           ∑ j : Fin k, g j • A j := by
         refine Finset.sum_congr rfl fun j _ => ?_
         simp [g', Fin.snoc_castSucc]
       have h2 : g' (Fin.last k) • Fin.snoc (α := fun _ => Fin h' → ZMod 2) A v (Fin.last k) = 0 := by
         simp [g', Fin.snoc_last]
       rw [h1, h2, hg, add_zero]
     have hres := hli g' hg' i.castSucc
     simpa [g', Fin.snoc_castSucc] using hres
   · intro hv
     rw [Submodule.mem_span_range_iff_exists_fun] at hv
     obtain ⟨c, hc⟩ := hv
     let g : Fin (k + 1) → ZMod 2 := Fin.snoc c 1
     have hg : ∑ j : Fin (k + 1), g j • Fin.snoc (α := fun _ => Fin h' → ZMod 2) A v j = 0 := by
       rw [Fin.sum_univ_castSucc]
       have h1 : (∑ j : Fin k, g j.castSucc • Fin.snoc (α := fun _ => Fin h' → ZMod 2) A v j.castSucc) =
           ∑ j : Fin k, c j • A j := by
         refine Finset.sum_congr rfl fun j _ => ?_
         simp [g, Fin.snoc_castSucc]
       have h2 : g (Fin.last k) • Fin.snoc (α := fun _ => Fin h' → ZMod 2) A v (Fin.last k) = v := by
         simp [g, Fin.snoc_last]
       rw [h1, h2, hc]
       ext q
       have htwo : ∀ a : ZMod 2, a + a = 0 := fun a => by fin_cases a <;> rfl
       exact htwo (v q)
     rw [Fintype.linearIndependent_iff] at hli
     have hlast := hli g hg (Fin.last k)
     simp [g, Fin.snoc_last] at hlast
 · rintro ⟨hA, hv⟩
   rw [Fintype.linearIndependent_iff] at hA ⊢
   intro g hg j
   have hg' : (∑ i : Fin k, g i.castSucc • A i) + g (Fin.last k) • v = 0 := by
     rw [Fin.sum_univ_castSucc] at hg
     simpa [Fin.snoc_castSucc, Fin.snoc_last] using hg
   have hglast : g (Fin.last k) = 0 := by
     by_contra hne
     have h1 : g (Fin.last k) = 1 := by
       generalize hgx : g (Fin.last k) = xg at hne ⊢
       fin_cases xg
       · exact absurd rfl hne
       · rfl
     rw [h1, one_smul] at hg'
     have hvmem : v = ∑ i : Fin k, g i.castSucc • A i := by
       ext q
       have hq := congrFun hg' q
       simp only [Pi.add_apply, Pi.zero_apply] at hq
       have hz2 : ∀ a b : ZMod 2, a + b = 0 → b = a := fun a b hab => by
         fin_cases a <;> fin_cases b <;> cases hab <;> rfl
       exact hz2 _ _ hq
     apply hv
     rw [Submodule.mem_span_range_iff_exists_fun]
     exact ⟨fun i => g i.castSucc, hvmem.symm⟩
   rw [hglast, zero_smul, add_zero] at hg'
   have hhead := hA (fun i => g i.castSucc) hg'
   refine Fin.lastCases hglast (fun i => hhead i) j

open Classical in
lemma card_span_of_linearIndependent {h' k : ℕ} (A : Fin k → (Fin h' → ZMod 2))
   (hA : LinearIndependent (ZMod 2) A) :
   Fintype.card (Submodule.span (ZMod 2) (Set.range A)) = 2 ^ k := by
 let φ : (Fin k → ZMod 2) → Submodule.span (ZMod 2) (Set.range A) := fun c =>
   ⟨∑ i : Fin k, c i • A i, Submodule.sum_mem _ fun i _ =>
     Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
 have hbij : Function.Bijective φ := by
   constructor
   · intro c1 c2 hc
     have heq : (∑ i : Fin k, (c1 i - c2 i) • A i) = 0 := by
       have hv := congrArg Subtype.val hc
       dsimp only [φ] at hv
       ext q
       have hq := congrFun hv q
       simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
         Finset.sum_sub_distrib, sub_eq_zero]
       simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hq
     rw [Fintype.linearIndependent_iff] at hA
     have hz := hA (fun i => c1 i - c2 i) heq
     ext i
     exact sub_eq_zero.1 (hz i)
   · rintro ⟨w, hw⟩
     rw [Submodule.mem_span_range_iff_exists_fun] at hw
     obtain ⟨c, hc⟩ := hw
     exact ⟨c, Subtype.ext hc⟩
 rw [← Fintype.card_congr (Equiv.ofBijective φ hbij), Fintype.card_fun, Fintype.card_fin, ZMod.card]

open Classical in
lemma card_linearIndependent_fin {h' : ℕ} : ∀ k : ℕ,
   (Finset.univ.filter (fun A : Fin k → (Fin h' → ZMod 2) =>
     LinearIndependent (ZMod 2) A)).card = ∏ j ∈ Finset.range k, (2 ^ h' - 2 ^ j)
 | 0 => by
   simp only [Finset.range_zero, Finset.prod_empty]
   rw [Finset.card_eq_one]
   refine ⟨Fin.elim0, ?_⟩
   ext A
   simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
   constructor
   · intro _; ext i; exact Fin.elim0 i
   · intro h; subst h
     rw [Fintype.linearIndependent_iff]
     intro g _ i; exact Fin.elim0 i
 | k + 1 => by
   classical
   let Sk := Finset.univ.filter (fun A : Fin k → (Fin h' → ZMod 2) => LinearIndependent (ZMod 2) A)
   let Sk1 := Finset.univ.filter (fun A : Fin (k + 1) → (Fin h' → ZMod 2) => LinearIndependent (ZMod 2) A)
   have hbij : Sk1.card = ∑ A ∈ Sk,
       (Finset.univ.filter (fun v : Fin h' → ZMod 2 =>
         v ∉ Submodule.span (ZMod 2) (Set.range A))).card := by
     rw [← Finset.card_sigma]
     refine Finset.card_bij (fun B _ => ⟨Fin.init B, B (Fin.last k)⟩) ?_ ?_ ?_
     · intro B hB
       rw [Finset.mem_filter] at hB
       have hsnoc : Fin.snoc (Fin.init B) (B (Fin.last k)) = B := Fin.snoc_init_self B
       have hli := hB.2
       rw [← hsnoc, linearIndependent_snoc_iff] at hli
       simp only [Finset.mem_sigma, Sk, Finset.mem_filter, Finset.mem_univ, true_and]
       exact hli
     · intro B1 _ B2 _ heq
       have h1 : Fin.init B1 = Fin.init B2 := congrArg Sigma.fst heq
       have h2 : B1 (Fin.last k) = B2 (Fin.last k) := by
         simpa using congrArg Sigma.snd heq
       calc B1 = Fin.snoc (Fin.init B1) (B1 (Fin.last k)) := (Fin.snoc_init_self B1).symm
         _ = Fin.snoc (Fin.init B2) (B2 (Fin.last k)) := by rw [h1, h2]
         _ = B2 := Fin.snoc_init_self B2
     · intro ⟨A, v⟩ hp
       simp only [Finset.mem_sigma, Sk, Finset.mem_filter, Finset.mem_univ, true_and] at hp
       refine ⟨Fin.snoc A v, ?_, ?_⟩
       · simp only [Sk1, Finset.mem_filter, Finset.mem_univ, true_and]
         exact (linearIndependent_snoc_iff A v).2 hp
       · simp [Fin.init_snoc]
   rw [hbij]
   have hconst : ∀ A ∈ Sk,
       (Finset.univ.filter (fun v : Fin h' → ZMod 2 =>
         v ∉ Submodule.span (ZMod 2) (Set.range A))).card = 2 ^ h' - 2 ^ k := by
     intro A hA
     rw [Finset.mem_filter] at hA
     have hcardW : (Finset.univ : Finset (Fin h' → ZMod 2)).card = 2 ^ h' := by
       simp [Fintype.card_fun, ZMod.card]
     have hcardS : (Finset.univ.filter (fun v : Fin h' → ZMod 2 =>
         v ∈ Submodule.span (ZMod 2) (Set.range A))).card = 2 ^ k := by
       have h1 : (Finset.univ.filter (fun v : Fin h' → ZMod 2 =>
           v ∈ Submodule.span (ZMod 2) (Set.range A))).card =
           Fintype.card (Submodule.span (ZMod 2) (Set.range A)) := by
         rw [Fintype.card_subtype]
       rw [h1, card_span_of_linearIndependent A hA.2]
     have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin h' → ZMod 2)))
       (p := fun v => v ∈ Submodule.span (ZMod 2) (Set.range A))
     omega
   rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_linearIndependent_fin k,
     Finset.prod_range_succ, mul_comm]

lemma rat_prod_lower (k : ℕ) (hk : 1 ≤ k) :
   (1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (k + 1) ≤ ∏ j ∈ Finset.range k, (1 - (1 / 2 : ℚ) ^ (j + 1)) := by
 induction k with
 | zero => omega
 | succ k ih =>
   rcases k with _ | k
   · norm_num [Finset.range_one]
   · have ih1 := ih (by omega)
     rw [Finset.prod_range_succ]
     have hpos : (0 : ℚ) ≤ 1 - (1 / 2 : ℚ) ^ (k + 1 + 1) := by
       have : (1 / 2 : ℚ) ^ (k + 1 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
       linarith
     have hmul : ((1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (k + 1 + 1)) * (1 - (1 / 2 : ℚ) ^ (k + 1 + 1)) ≤
         (∏ j ∈ Finset.range (k + 1), (1 - (1 / 2 : ℚ) ^ (j + 1))) * (1 - (1 / 2 : ℚ) ^ (k + 1 + 1)) :=
       mul_le_mul_of_nonneg_right ih1 hpos
     have hpow : (1 / 2 : ℚ) ^ (2 * k + 4) ≤ (1 / 2 : ℚ) ^ (k + 4) := by
       have h1 : (1 / 2 : ℚ) ^ (2 * k + 4) = (1 / 2 : ℚ) ^ (k + 4) * (1 / 2 : ℚ) ^ k := by ring
       rw [h1]
       have hle1 : (1 / 2 : ℚ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
       nlinarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) (k + 4)]
     have hexpand : ((1 / 4 : ℚ) + (1 / 2 : ℚ) ^ (k + 1 + 1)) * (1 - (1 / 2 : ℚ) ^ (k + 1 + 1)) =
         1 / 4 + (1 / 2 : ℚ) ^ (k + 1 + 2) + ((1 / 2 : ℚ) ^ (k + 4) - (1 / 2 : ℚ) ^ (2 * k + 4)) := by
       ring
     linarith

lemma prod_pow_sub_lower (h' : ℕ) :
   2 ^ (h' * h') ≤ 4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j) := by
 by_cases hh : h' = 0
 · subst hh; simp
 have hh1 : 1 ≤ h' := Nat.one_le_iff_ne_zero.2 hh
 have hrat := rat_prod_lower h' hh1
 have hquarter : (1 / 4 : ℚ) ≤ ∏ j ∈ Finset.range h', (1 - (1 / 2 : ℚ) ^ (j + 1)) := by
   have hnn : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ (h' + 1) := pow_nonneg (by norm_num) _
   linarith
 have hrev : (∏ j ∈ Finset.range h', (1 - (1 / 2 : ℚ) ^ (j + 1))) =
     ∏ j ∈ Finset.range h', (1 - (1 / 2 : ℚ) ^ (h' - j)) := by
   rw [← Finset.prod_range_reflect (fun j => 1 - (1 / 2 : ℚ) ^ (j + 1)) h']
   refine Finset.prod_congr rfl fun j hj => ?_
   have hj' : j < h' := Finset.mem_range.1 hj
   have hidx : h' - 1 - j + 1 = h' - j := by omega
   rw [hidx]
 rw [hrev] at hquarter
 have hcast : ((∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j) : ℕ) : ℚ) =
     (2 : ℚ) ^ (h' * h') * ∏ j ∈ Finset.range h', (1 - (1 / 2 : ℚ) ^ (h' - j)) := by
   rw [Nat.cast_prod]
   have h2 : (2 : ℚ) ^ (h' * h') = ∏ _j ∈ Finset.range h', (2 : ℚ) ^ h' := by
     simp [Finset.prod_const, Finset.card_range, ← pow_mul]
   rw [h2, ← Finset.prod_mul_distrib]
   refine Finset.prod_congr rfl fun j hj => ?_
   have hj' : j < h' := Finset.mem_range.1 hj
   have hle : 2 ^ j ≤ 2 ^ h' := Nat.pow_le_pow_right (by omega) (by omega)
   rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
   have hpow : (2 : ℚ) ^ h' * (1 / 2 : ℚ) ^ (h' - j) = (2 : ℚ) ^ j := by
     have hexp : (2 : ℚ) ^ h' = (2 : ℚ) ^ j * (2 : ℚ) ^ (h' - j) := by
       rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hj')]
     rw [hexp, mul_assoc, ← mul_pow]
     norm_num
   linarith
 have hq : ((2 ^ (h' * h') : ℕ) : ℚ) ≤ ((4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j) : ℕ) : ℚ) := by
   rw [Nat.cast_mul, hcast, Nat.cast_pow, Nat.cast_ofNat]
   have hpow2 : (0 : ℚ) ≤ (2 : ℚ) ^ (h' * h') := pow_nonneg (by norm_num) _
   nlinarith
 exact_mod_cast hq

open Classical in
lemma card_goodMat {h' n : ℕ} {U : Finset (Fin n)} (hU : U.card = h') :
   2 ^ (h' * n) ≤ 4 * (Finset.univ.filter (fun M : Mat h' n => GoodMat U M)).card := by
 classical
 let eU : Fin h' ≃ U := (Fintype.equivFinOfCardEq (by simp [hU])).symm
 let eMat : Mat h' n ≃ (Fin h' → (Fin h' → ZMod 2)) × ({ j : Fin n // j ∉ U } → (Fin h' → ZMod 2)) :=
   { toFun := fun M => (fun k q => M q (eU k).1, fun j q => M q j.1)
     invFun := fun p q j => if hj : j ∈ U then p.1 (eU.symm ⟨j, hj⟩) q else p.2 ⟨j, hj⟩ q
     left_inv := fun M => by
       ext q j
       by_cases hj : j ∈ U
       · simp [hj]
       · simp [hj]
     right_inv := fun p => by
       ext1
       · ext k q
         simp [(eU k).2]
       · ext j q
         simp [j.2] }
 have hgood_iff : ∀ M : Mat h' n,
     GoodMat U M ↔ LinearIndependent (ZMod 2) (eMat M).1 := by
   intro M
   constructor
   · intro hgood
     rw [Fintype.linearIndependent_iff]
     intro g hg k
     let x : U → ZMod 2 := fun u => g (eU.symm u)
     have hx0 : linOfMat U M x = 0 := by
       ext q
       simp only [linOfMat, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
       have h1 : (∑ i : U, M q i.1 * x i) = ∑ k' : Fin h', g k' * M q (eU k').1 := by
         rw [← Equiv.sum_comp eU]
         refine Finset.sum_congr rfl fun k' _ => ?_
         simp [x, mul_comm]
       rw [h1]
       have hq := congrFun hg q
       simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eMat] using hq
     have hxzero : x = 0 := hgood (by simpa using hx0)
     have := congrFun hxzero (eU k)
     simpa [x] using this
   · intro hli x y hxy
     have hsub : linOfMat U M (x - y) = 0 := by rw [map_sub, hxy, sub_self]
     rw [Fintype.linearIndependent_iff] at hli
     have hsum : ∑ k : Fin h', (x (eU k) - y (eU k)) • (eMat M).1 k = 0 := by
       ext q
       have hq := congrFun hsub q
       simp only [linOfMat, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.zero_apply] at hq
       rw [← Equiv.sum_comp eU] at hq
       simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eMat, mul_comm] using hq
     have hz := hli (fun k => x (eU k) - y (eU k)) hsum
     ext i
     have := hz (eU.symm i)
     simpa [sub_eq_zero] using this
 have hcard_eq : (Finset.univ.filter (fun M : Mat h' n => GoodMat U M)).card =
     (Finset.univ.filter (fun A : Fin h' → (Fin h' → ZMod 2) => LinearIndependent (ZMod 2) A)).card *
     2 ^ (h' * (n - h')) := by
   have h1 : (Finset.univ.filter (fun M : Mat h' n => GoodMat U M)).card =
       Fintype.card { M : Mat h' n // GoodMat U M } := (Fintype.card_subtype _).symm
   have h2 : Fintype.card { M : Mat h' n // GoodMat U M } =
       Fintype.card ({ A : Fin h' → (Fin h' → ZMod 2) // LinearIndependent (ZMod 2) A } ×
         ({ j : Fin n // j ∉ U } → (Fin h' → ZMod 2))) := by
     refine Fintype.card_congr
       { toFun := fun ⟨M, hM⟩ => (⟨(eMat M).1, (hgood_iff M).1 hM⟩, (eMat M).2)
         invFun := fun ⟨⟨A, hA⟩, B⟩ => ⟨eMat.symm (A, B), (hgood_iff _).2 (by simpa using hA)⟩
         left_inv := fun ⟨M, _⟩ => Subtype.ext (eMat.left_inv M)
         right_inv := fun ⟨⟨A, _⟩, B⟩ => by
           ext1
           · apply Subtype.ext; simp [eMat.right_inv (A, B)]
           · simp [eMat.right_inv (A, B)] }
   rw [h1, h2, Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun, Fintype.card_fun,
     Fintype.card_fin, ZMod.card]
   have hcomp : Fintype.card { j : Fin n // j ∉ U } = n - h' := by
     rw [Fintype.card_subtype]
     have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
       (p := fun j => j ∈ U)
     have hU' : (Finset.univ.filter (fun j : Fin n => j ∈ U)).card = h' := by
       simpa [Finset.filter_mem_eq_inter] using hU
     have htot : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
     omega
   rw [hcomp, ← pow_mul]
 rw [hcard_eq, card_linearIndependent_fin h']
 have hle : h' ≤ n := by
   have := Finset.card_le_univ U
   simp only [Fintype.card_fin] at this
   omega
 have hexp : 2 ^ (h' * n) = 2 ^ (h' * h') * 2 ^ (h' * (n - h')) := by
   rw [← pow_add, ← mul_add, Nat.add_sub_of_le hle]
 rw [hexp]
 have hbase := prod_pow_sub_lower h'
 calc 2 ^ (h' * h') * 2 ^ (h' * (n - h'))
   _ ≤ (4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j)) * 2 ^ (h' * (n - h')) :=
     Nat.mul_le_mul_right _ hbase
   _ = 4 * ((∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j)) * 2 ^ (h' * (n - h'))) := by ring

open Classical in
lemma greedy_cover_step {h' n : ℕ} (S : Finset (Finset (Fin n))) (hS : S.Nonempty)
   (hcard : ∀ U ∈ S, U.card = h') :
   ∃ M : Mat h' n, 4 * (S.filter (fun U => ¬ GoodMat U M)).card ≤ 3 * S.card := by
 let allM : Finset (Mat h' n) := Finset.univ
 have hallM_ne : allM.Nonempty := ⟨fun _ _ => 0, Finset.mem_univ _⟩
 have hallM_card : allM.card = 2 ^ (h' * n) := by
   simp [allM, ZMod.card, ← pow_mul, mul_comm]
 have hsum : S.card * 2 ^ (h' * n) ≤
     4 * ∑ M ∈ allM, (S.filter (fun U => GoodMat U M)).card := by
   have h1 : ∑ M ∈ allM, (S.filter (fun U => GoodMat U M)).card =
       ∑ U ∈ S, (allM.filter (fun M => GoodMat U M)).card := by
     simp_rw [Finset.card_filter]
     exact Finset.sum_comm
   rw [h1, Finset.mul_sum]
   have h2 : S.card * 2 ^ (h' * n) = ∑ _U ∈ S, 2 ^ (h' * n) := by
     simp [Finset.sum_const, smul_eq_mul]
   rw [h2]
   refine Finset.sum_le_sum fun U hU => card_goodMat (hcard U hU)
 by_contra hnone
 push Not at hnone
 have hbad : ∀ M ∈ allM, 4 * (S.filter (fun U => GoodMat U M)).card < S.card := by
   intro M hM
   have hgt := hnone M
   have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun U => GoodMat U M)
   omega
 have hsumlt : 4 * ∑ M ∈ allM, (S.filter (fun U => GoodMat U M)).card <
     allM.card * S.card := by
   rw [Finset.mul_sum]
   have h2 : allM.card * S.card = ∑ _M ∈ allM, S.card := by
     simp [Finset.sum_const, smul_eq_mul]
   rw [h2]
   exact Finset.sum_lt_sum (fun M hM => le_of_lt (hbad M hM))
     ⟨fun _ _ => 0, Finset.mem_univ _, hbad _ (Finset.mem_univ _)⟩
 rw [hallM_card, mul_comm (2 ^ (h' * n)) S.card] at hsumlt
 omega

lemma exists_mat_family (n h' : ℕ) (hh1 : 1 ≤ h') (hhn : h' ≤ n) :
   ∃ (R : ℕ) (H : Fin R → Fin h' → Fin n → Bool),
     1 ≤ R ∧ R ≤ 3 * (h' + 1) * (Nat.clog 2 (n + 1) + 1) ∧
     ∀ U : Finset (Fin n), U.card ≤ h' →
       ∃ r : Fin R, ∀ i ∈ U, ∃ c : Fin h' → Bool, ∀ j ∈ U,
         xl (List.ofFn (fun q : Fin h' => c q && H r q j)) = decide (j = i) := by
 classical
 let L := Nat.clog 2 (n + 1)
 have hL1 : 1 ≤ L := by
   have : Nat.clog 2 2 ≤ L := Nat.clog_mono_right 2 (by omega)
   have h2 : Nat.clog 2 2 = 1 := by decide
   omega
 have hn_lt : n < 2 ^ L := by
   have := (Nat.clog_le_iff_le_pow (by omega)).1 (le_rfl : L ≤ L)
   omega
 let R := 3 * (h' * L) + 1
 have hR1 : 1 ≤ R := by omega
 have hRbd : R ≤ 3 * (h' + 1) * (L + 1) := by dsimp only [R]; nlinarith
 have hstep : ∀ (k : ℕ) (S : Finset (Finset (Fin n))), (∀ U ∈ S, U.card = h') →
     ∃ Ms : Fin k → Mat h' n, 4 ^ k * (S.filter (fun U => ∀ r : Fin k, ¬ GoodMat U (Ms r))).card ≤
       3 ^ k * S.card := by
   intro k
   induction k with
   | zero =>
     intro S _
     refine ⟨Fin.elim0, by simp⟩
   | succ k ih =>
     intro S hSc
     obtain ⟨Ms, hMs⟩ := ih S hSc
     let Srem := S.filter (fun U => ∀ r : Fin k, ¬ GoodMat U (Ms r))
     by_cases hne : Srem.Nonempty
     · obtain ⟨Mnew, hMnew⟩ := greedy_cover_step Srem hne (fun U hU => hSc U (Finset.mem_filter.1 hU).1)
       refine ⟨Fin.snoc (α := fun _ => Mat h' n) Ms Mnew, ?_⟩
       have hsub : S.filter (fun U => ∀ r : Fin (k + 1), ¬ GoodMat U (Fin.snoc (α := fun _ => Mat h' n) Ms Mnew r)) =
           Srem.filter (fun U => ¬ GoodMat U Mnew) := by
         ext U
         simp only [Srem, Finset.mem_filter]
         constructor
         · rintro ⟨hUS, hall⟩
           exact ⟨⟨hUS, fun r => by simpa [Fin.snoc_castSucc] using hall r.castSucc⟩,
             by simpa [Fin.snoc_last] using hall (Fin.last k)⟩
         · rintro ⟨⟨hUS, hall⟩, hlast⟩
           refine ⟨hUS, fun r => Fin.lastCases (by simpa [Fin.snoc_last] using hlast)
             (fun r' => by simpa [Fin.snoc_castSucc] using hall r') r⟩
       rw [hsub]
       calc 4 ^ (k + 1) * (Srem.filter (fun U => ¬ GoodMat U Mnew)).card
         _ = 4 ^ k * (4 * (Srem.filter (fun U => ¬ GoodMat U Mnew)).card) := by ring
         _ ≤ 4 ^ k * (3 * Srem.card) := Nat.mul_le_mul_left _ hMnew
         _ = 3 * (4 ^ k * Srem.card) := by ring
         _ ≤ 3 * (3 ^ k * S.card) := Nat.mul_le_mul_left _ hMs
         _ = 3 ^ (k + 1) * S.card := by ring
     · rw [Finset.not_nonempty_iff_eq_empty] at hne
       refine ⟨Fin.snoc (α := fun _ => Mat h' n) Ms (fun _ _ => 0), ?_⟩
       have hsub : S.filter (fun U => ∀ r : Fin (k + 1), ¬ GoodMat U (Fin.snoc (α := fun _ => Mat h' n) Ms (fun _ _ => 0) r)) = ∅ := by
         rw [Finset.eq_empty_iff_forall_notMem]
         intro U hU
         rw [Finset.mem_filter] at hU
         have hrem : U ∈ Srem := Finset.mem_filter.2 ⟨hU.1, fun r => by simpa [Fin.snoc_castSucc] using hU.2 r.castSucc⟩
         rw [hne] at hrem
         simp at hrem
       rw [hsub, Finset.card_empty, mul_zero]
       exact Nat.zero_le _
 let S0 : Finset (Finset (Fin n)) := Finset.univ.filter (fun U : Finset (Fin n) => U.card = h')
 obtain ⟨Ms, hMs⟩ := hstep R S0 (fun U hU => (Finset.mem_filter.1 hU).2)
 have hS0_lt : S0.card < 2 ^ (h' * L) := by
   have hS0_eq : S0 = Finset.powersetCard h' (Finset.univ : Finset (Fin n)) := by
     ext U; simp [S0, Finset.mem_powersetCard]
   have h1 : S0.card = n.choose h' := by
     rw [hS0_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
   have h2 : n.choose h' ≤ n ^ h' := Nat.choose_le_pow n h'
   have h3 : n ^ h' < (2 ^ L) ^ h' := Nat.pow_lt_pow_left hn_lt (by omega)
   rw [h1]
   exact lt_of_le_of_lt h2 (by simpa [← pow_mul, mul_comm] using h3)
 have hrem_zero : (S0.filter (fun U => ∀ r : Fin R, ¬ GoodMat U (Ms r))).card = 0 := by
   set rem := (S0.filter (fun U => ∀ r : Fin R, ¬ GoodMat U (Ms r))).card
   have hpow_mul : 2 ^ (h' * L) * 3 ^ R ≤ 4 ^ R := by
     have h3 : 3 ^ R = 3 * 3 ^ (3 * (h' * L)) := by simp [R, pow_succ']
     have h4 : 4 ^ R = 4 * 4 ^ (3 * (h' * L)) := by simp [R, pow_succ']
     have h27 : 3 ^ (3 * (h' * L)) = 27 ^ (h' * L) := by rw [pow_mul]; norm_num
     have h64 : 4 ^ (3 * (h' * L)) = 64 ^ (h' * L) := by rw [pow_mul]; norm_num
     have h264 : 2 ^ (h' * L) * 27 ^ (h' * L) ≤ 64 ^ (h' * L) := by
       rw [← mul_pow]
       exact Nat.pow_le_pow_left (by omega) _
     rw [h3, h4, h27, h64]
     calc 2 ^ (h' * L) * (3 * 27 ^ (h' * L))
       _ = 3 * (2 ^ (h' * L) * 27 ^ (h' * L)) := by ring
       _ ≤ 3 * 64 ^ (h' * L) := Nat.mul_le_mul_left 3 h264
       _ ≤ 4 * 64 ^ (h' * L) := by omega
   have hmul_le : 4 ^ R * rem ≤ 3 ^ R * S0.card := hMs
   by_contra hne
   have hrem_pos : 1 ≤ rem := Nat.one_le_iff_ne_zero.2 hne
   have h1 : 4 ^ R ≤ 4 ^ R * rem := Nat.le_mul_of_pos_right _ hrem_pos
   have h2 : 3 ^ R * S0.card < 3 ^ R * 2 ^ (h' * L) := Nat.mul_lt_mul_of_pos_left hS0_lt (pow_pos (by omega) _)
   have hlt : 4 ^ R < 4 ^ R := calc
     4 ^ R ≤ 4 ^ R * rem := h1
     _ ≤ 3 ^ R * S0.card := hmul_le
     _ < 3 ^ R * 2 ^ (h' * L) := h2
     _ = 2 ^ (h' * L) * 3 ^ R := mul_comm _ _
     _ ≤ 4 ^ R := hpow_mul
   exact Nat.lt_irrefl _ hlt
 have hcov_h' : ∀ U : Finset (Fin n), U.card = h' → ∃ r : Fin R, GoodMat U (Ms r) := by
   intro U hU
   by_contra hno
   push Not at hno
   have hmem : U ∈ S0.filter (fun U => ∀ r : Fin R, ¬ GoodMat U (Ms r)) :=
     Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hU⟩, hno⟩
   have hpos : 0 < (S0.filter (fun U => ∀ r : Fin R, ¬ GoodMat U (Ms r))).card :=
     Finset.card_pos.2 ⟨U, hmem⟩
   omega
 refine ⟨R, fun r q j => decide (Ms r q j = 1), hR1, hRbd, fun U' hU' => ?_⟩
 have hcomp_card : h' - U'.card ≤ ((Finset.univ : Finset (Fin n)) \ U').card := by
   rw [Finset.card_sdiff]
   have hsub : U' ⊆ Finset.univ := Finset.subset_univ _
   have hinter : U' ∩ Finset.univ = U' := Finset.inter_univ _
   simp only [hinter, Finset.card_fin]
   omega
 obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hcomp_card
 have hdisj : Disjoint U' E := Finset.disjoint_left.2 fun x hxU hxE =>
   (Finset.mem_sdiff.1 (hEsub hxE)).2 hxU
 have hUE_card : (U' ∪ E).card = h' := by
   rw [Finset.card_union_of_disjoint hdisj, hEcard]
   omega
 obtain ⟨r, hr⟩ := hcov_h' (U' ∪ E) hUE_card
 have hr' : GoodMat U' (Ms r) := goodMat_mono Finset.subset_union_left hr
 refine ⟨r, fun i hi => goodMat_dual_vec hr' hi⟩

def lod {W : Type} (p : Lit W × Lit W) (b : Bool) : Lit W :=
 if b then p.1 else p.2

lemma litEval_litOfDual {W : Type} (α : W → Bool) (p : Lit W × Lit W) (v b : Bool)
   (hp1 : lEv α p.1 = v) (hp2 : lEv α p.2 = !v) :
   lEv α (lod p b) = (v == b) := by
 cases b <;> cases v <;> simp [lod, hp1, hp2]

lemma validLit_litOfDual {V : Type} {m : ℕ} {p : LN V × LN V}
   (h1 : VL m p.1) (h2 : VL m p.2) (b : Bool) : VL m (lod p b) := by
 cases b <;> simp [lod, h1, h2]

def bcg {V : Type} [DecidableEq V] (n D : ℕ) (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) :
   (k : ℕ) → (ℕ → LN V × LN V) → St V →
     (ℕ → LN V × LN V) × St V
 | k, wires, st =>
   if hk : k < gs.length then
     if dv n gs (n + k) ≤ D then
       let (wT, st1) := fv st
       let (wF, st2) := fv st1
       let g := gs[k]
       let inL := if g.left < n + k then wires g.left else fd
       let inR := if g.right < n + k then wires g.right else fd
       let st3 := edg g.op inL inR (wT, wF) st2
       let st4 := match exclOpt with
         | none => ei2 wT (negL wF) st3
         | some ex => ei3 wT wF ex st3
       let wires' : ℕ → LN V × LN V :=
         fun u => if u = n + k then (wT, wF) else wires u
       bcg n D gs fd exclOpt (k + 1) wires' st4
     else
       bcg n D gs fd exclOpt (k + 1) wires st
   else (wires, st)
termination_by k => gs.length - k

lemma bcg_step {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) (k : ℕ) (hk : k < gs.length)
   (wires : ℕ → LN V × LN V) (st : St V) :
   bcg n D gs fd exclOpt k wires st =
     if dv n gs (n + k) ≤ D then
       let wT := (fv st).1
       let st1 := (fv st).2
       let wF := (fv st1).1
       let st2 := (fv st1).2
       let g := gs[k]'hk
       let inL := if g.left < n + k then wires g.left else fd
       let inR := if g.right < n + k then wires g.right else fd
       let st3 := edg g.op inL inR (wT, wF) st2
       let st4 := match exclOpt with
         | none => ei2 wT (negL wF) st3
         | some ex => ei3 wT wF ex st3
       let wires' : ℕ → LN V × LN V :=
         fun u => if u = n + k then (wT, wF) else wires u
       bcg n D gs fd exclOpt (k + 1) wires' st4
     else
       bcg n D gs fd exclOpt (k + 1) wires st := by
 conv_lhs => rw [bcg]
 simp only [hk, ↓reduceDIte]

lemma bcg_pr {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) :
   ∀ (m k : ℕ) (hm : gs.length - k = m)
     (wires : ℕ → LN V × LN V) (st : St V),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ ex, exclOpt = some ex → VL st.1 ex) →
     (∀ u, VL st.1 (wires u).1 ∧ VL st.1 (wires u).2) →
     let res := bcg n D gs fd exclOpt k wires st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + 2 * m ∧
     res.2.2.length ≤ st.2.length + 5 * m ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ u, VL res.2.1 (res.1 u).1 ∧ VL res.2.1 (res.1 u).2) ∧
     (∀ u < n + k, res.1 u = wires u) ∧
     (∀ u ≥ n + gs.length, res.1 u = wires u) := by
 intro m
 induction m with
 | zero =>
   intro k hm wires st hst hf1 hf2 hex hwires
   have hge : ¬ (k < gs.length) := by omega
   unfold bcg
   simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by omega, by omega, fun _ h => h, hwires, fun _ _ => trivial, fun _ _ => trivial⟩
 | succ m ih =>
   intro k hm wires st hst hf1 hf2 hex hwires
   have hk : k < gs.length := by omega
   have hm1 : gs.length - (k + 1) = m := by omega
   rw [bcg_step n D gs fd exclOpt k hk wires st]
   by_cases hdep : dv n gs (n + k) ≤ D
   · simp only [hdep, ↓reduceIte]
     set wT := (fv st).1
     set st1 := (fv st).2
     set wF := (fv st1).1
     set st2 := (fv st1).2
     set g := gs[k]'hk
     set inL := if g.left < n + k then wires g.left else fd
     set inR := if g.right < n + k then wires g.right else fd
     set st3 := edg g.op inL inR (wT, wF) st2
     set st4 := match exclOpt with
       | none => ei2 wT (negL wF) st3
       | some ex => ei3 wT wF ex st3
     let wires' : ℕ → LN V × LN V :=
       fun u => if u = n + k then (wT, wF) else wires u
     have hst1 : VS st1 := validSt_fresh hst
     have hst2 : VS st2 := validSt_fresh hst1
     have hst2_1 : st2.1 = st.1 + 2 := rfl
     have hst2_2 : st2.2 = st.2 := rfl
     have hwT2 : VL st2.1 wT := (validLit_fresh st).mono (by simp [st1, st2, fv])
     have hwF2 : VL st2.1 wF := by
       change VL (st1.1 + 1) wF
       exact validLit_fresh st1
     have hst3 : VS st3 := validSt_emitDualGate g.op hst2
       (by dsimp only [inL]; split_ifs; exact (hwires _).1.mono (by omega); exact hf1.mono (by omega))
       (by dsimp only [inL]; split_ifs; exact (hwires _).2.mono (by omega); exact hf2.mono (by omega))
       (by dsimp only [inR]; split_ifs; exact (hwires _).1.mono (by omega); exact hf1.mono (by omega))
       (by dsimp only [inR]; split_ifs; exact (hwires _).2.mono (by omega); exact hf2.mono (by omega))
       hwT2 hwF2
     have hst3_1 : st3.1 = st.1 + 2 := hst2_1
     have hst4_1 : st4.1 = st.1 + 2 := by
       cases hopt : exclOpt <;> simp [st4, hopt, st3, edg, ei2, ei3, addCl, hst2_1]
     have hlen4 : st4.2.length = st.2.length + 5 := by
       cases hopt : exclOpt <;> simp [st4, hopt, st3, edg, ei2, ei3, addCl, hst2_2]
     have hwT : VL st4.1 wT := hwT2.mono (by omega)
     have hwF : VL st4.1 wF := hwF2.mono (by omega)
     have hst4 : VS st4 := by
       cases hopt : exclOpt with
       | none =>
         simp only [st4, hopt]
         exact validSt_emitImp2 hst3 (hwT2.mono (by omega)) (validLit_negL.2 (hwF2.mono (by omega)))
       | some ex =>
         simp only [st4, hopt]
         exact validSt_emitImp3 hst3 (hwT2.mono (by omega)) (hwF2.mono (by omega))
           ((hex ex hopt).mono (by rw [hst3_1]; omega))
     have hwires' : ∀ u, VL st4.1 (wires' u).1 ∧ VL st4.1 (wires' u).2 := by
       intro u
       dsimp only [wires']
       split_ifs
       · exact ⟨hwT, hwF⟩
       · exact ⟨(hwires u).1.mono (by omega), (hwires u).2.mono (by omega)⟩
     have hsub4 : ∀ C ∈ st.2, C ∈ st4.2 := by
       intro C hC
       have hC3 : C ∈ st3.2 := by
         simp only [st3, edg, ei3, addCl, List.mem_cons]
         exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa [hst2_2] using hC))))
       cases hopt : exclOpt with
       | none =>
         simp only [st4, hopt, ei2, addCl, List.mem_cons]
         exact Or.inr hC3
       | some ex =>
         simp only [st4, hopt, ei3, addCl, List.mem_cons]
         exact Or.inr hC3
     have hex4 : ∀ ex, exclOpt = some ex → VL st4.1 ex := by
       intro ex h; exact (hex ex h).mono (by omega)
     have hind := ih (k + 1) hm1 wires' st4 hst4 (hf1.mono (by omega)) (hf2.mono (by omega)) hex4 hwires'
     rcases hind with ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩
     dsimp only [wires'] at r1 r2 r3 r4 r5 r6 r7 r8 ⊢
     refine ⟨r1, by omega, by omega, by omega, fun C hC => r5 C (hsub4 C hC), r6, ?_, ?_⟩
     · intro u hu
       have hu1 : u < n + (k + 1) := by omega
       rw [r7 u hu1]
       split_ifs with heq
       · omega
       · rfl
     · intro u hu
       rw [r8 u hu]
       split_ifs with heq
       · omega
       · rfl
   · simp only [hdep, ↓reduceIte]
     rcases ih (k + 1) hm1 wires st hst hf1 hf2 hex hwires with ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩
     exact ⟨r1, r2, by omega, by omega, r5, r6, fun u hu => r7 u (by omega), r8⟩

lemma cscl {V : Type} {m : ℕ} {α1 α2 : Sum V ℕ → Bool}
   (hinl : ∀ v : V, α1 (Sum.inl v) = α2 (Sum.inl v))
   (hinr : ∀ w < m, α1 (Sum.inr w) = α2 (Sum.inr w))
   {C : CN V} (hV : VC m C) :
   ClauseSat α1 C ↔ ClauseSat α2 C := by
 have hlit : ∀ l ∈ C, α1 l.1 = α2 l.1 := by
   intro l hlC
   cases hx : l.1 with
   | inl v => exact hinl v
   | inr w => exact hinr w (hV l hlC w hx)
 constructor
 · rintro ⟨l, hlC, hl⟩
   exact ⟨l, hlC, by rw [← hlit l hlC]; exact hl⟩
 · rintro ⟨l, hlC, hl⟩
   exact ⟨l, hlC, by rw [hlit l hlC]; exact hl⟩

lemma lecl {V : Type} {m : ℕ} {α1 α2 : Sum V ℕ → Bool}
   (hinl : ∀ v : V, α1 (Sum.inl v) = α2 (Sum.inl v))
   (hinr : ∀ w < m, α1 (Sum.inr w) = α2 (Sum.inr w))
   {l : LN V} (hl : VL m l) :
   lEv α1 l = lEv α2 l := by
 cases hx : l.1 with
 | inl v => simp [lEv, hx, hinl v]
 | inr w => simp [lEv, hx, hinr w (hl w hx)]

lemma bcg_si {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V) (ex : LN V) :
   ∀ (m k : ℕ) (hm : gs.length - k = m)
     (wires : ℕ → LN V × LN V) (st : St V)
     (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     VL st.1 ex →
     (∀ u, VL st.1 (wires u).1 ∧ VL st.1 (wires u).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α ex = true →
     ∃ α' : Sum V ℕ → Bool,
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ v : V, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ C ∈ (bcg n D gs fd (some ex) k wires st).2.2, ClauseSat α' C) := by
 intro m
 induction m with
 | zero =>
   intro k hm wires st α _ _ _ _ _ hsat _
   have hge : ¬ (k < gs.length) := by omega
   unfold bcg
   simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ _ => rfl, fun _ => rfl, hsat⟩
 | succ m ih =>
   intro k hm wires st α hst hf1 hf2 hexv hwires hsat hex
   have hk : k < gs.length := by omega
   have hm1 : gs.length - (k + 1) = m := by omega
   unfold bcg
   simp only [hk, ↓reduceDIte]
   by_cases hdep : dv n gs (n + k) ≤ D
   · simp only [hdep, ↓reduceIte]
     set wT := (fv st).1
     set st1 := (fv st).2
     set wF := (fv st1).1
     set st2 := (fv st1).2
     set g := gs[k]'hk
     set inL := if g.left < n + k then wires g.left else fd
     set inR := if g.right < n + k then wires g.right else fd
     set st3 := edg g.op inL inR (wT, wF) st2
     set st4 := ei3 wT wF ex st3
     let wires' : ℕ → LN V × LN V :=
       fun u => if u = n + k then (wT, wF) else wires u
     let α1 : Sum V ℕ → Bool := fun z =>
       match z with
       | Sum.inl v => α (Sum.inl v)
       | Sum.inr w => if w = st.1 ∨ w = st.1 + 1 then true else α (Sum.inr w)
     have hα1_lt : ∀ w < st.1, α1 (Sum.inr w) = α (Sum.inr w) := by
       intro w hw; simp [α1, show w ≠ st.1 by omega, show w ≠ st.1 + 1 by omega]
     have hα1_inl : ∀ v : V, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
     have hsat2 : ∀ C ∈ st2.2, ClauseSat α1 C := by
       intro C hC
       have hC0 : C ∈ st.2 := hC
       exact (cscl hα1_inl hα1_lt (hst C hC0).2).2 (hsat C hC0)
     have hwT_val : lEv α1 wT = true := by simp [wT, fv, lEv, α1]
     have hwF_val : lEv α1 wF = true := by simp [wF, st1, fv, lEv, α1]
     have hex1 : lEv α1 ex = true :=
       (lecl hα1_inl hα1_lt hexv).trans hex
     have hsat3 : ∀ C ∈ st3.2, ClauseSat α1 C :=
       emitDualGate_sat_of_both g.op α1 inL inR (wT, wF) st2 hwT_val hwF_val hsat2
     have hsat4 : ∀ C ∈ st4.2, ClauseSat α1 C := by
       intro C hC
       rcases List.mem_cons.1 hC with rfl | hC3
       · rw [clauseSat_imp3]; intro _ _; exact hex1
       · exact hsat3 C hC3
     have hst2 : VS st2 := validSt_fresh (validSt_fresh hst)
     have hst2_1 : st2.1 = st.1 + 2 := rfl
     have hst4_1 : st4.1 = st.1 + 2 := rfl
     have hwT : VL st2.1 wT := (validLit_fresh st).mono (by simp [st1, st2, fv])
     have hwF : VL st2.1 wF := by
       change VL (st1.1 + 1) wF
       exact validLit_fresh st1
     have hinL1 : VL st2.1 inL.1 := by
       dsimp only [inL]; split_ifs
       · exact (hwires _).1.mono (by omega)
       · exact hf1.mono (by omega)
     have hinL2 : VL st2.1 inL.2 := by
       dsimp only [inL]; split_ifs
       · exact (hwires _).2.mono (by omega)
       · exact hf2.mono (by omega)
     have hinR1 : VL st2.1 inR.1 := by
       dsimp only [inR]; split_ifs
       · exact (hwires _).1.mono (by omega)
       · exact hf1.mono (by omega)
     have hinR2 : VL st2.1 inR.2 := by
       dsimp only [inR]; split_ifs
       · exact (hwires _).2.mono (by omega)
       · exact hf2.mono (by omega)
     have hst3 : VS (edg g.op inL inR (wT, wF) st2) :=
       validSt_emitDualGate g.op hst2 hinL1 hinL2 hinR1 hinR2 hwT hwF
     have hst3_1 : (edg g.op inL inR (wT, wF) st2).1 = st.1 + 2 := hst2_1
     have hst4 : VS st4 :=
       validSt_emitImp3 hst3 (hwT.mono (by omega)) (hwF.mono (by omega))
         (hexv.mono (by rw [hst3_1]; omega))
     have hwires' : ∀ u, VL st4.1 (wires' u).1 ∧ VL st4.1 (wires' u).2 := by
       intro u; dsimp only [wires']; split_ifs
       · exact ⟨hwT, hwF⟩
       · exact ⟨(hwires u).1.mono (by omega), (hwires u).2.mono (by omega)⟩
     obtain ⟨α', hlt', hinl', hsat'⟩ := ih (k + 1) hm1 wires' st4 α1 hst4
       (hf1.mono (by omega)) (hf2.mono (by omega)) (hexv.mono (by omega)) hwires' hsat4 hex1
     refine ⟨α', fun w hw => ?_, fun v => (hinl' v).trans (hα1_inl v), hsat'⟩
     exact (hlt' w (by omega)).trans (hα1_lt w hw)
   · simp only [hdep, ↓reduceIte]
     exact ih (k + 1) hm1 wires st α hst hf1 hf2 hexv hwires hsat hex

lemma bcg_sa {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) (x : Fin n → Bool) :
   ∀ (m k : ℕ) (hm : gs.length - k = m)
     (wires : ℕ → LN V × LN V) (st : St V)
     (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ ex, exclOpt = some ex → VL st.1 ex) →
     (∀ u, VL st.1 (wires u).1 ∧ VL st.1 (wires u).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     (∀ ex, exclOpt = some ex → lEv α ex = false) →
     (lEv α fd.1 = false ∧ lEv α fd.2 = true) →
     (∀ u < n + k, dv n gs u ≤ D →
       lEv α (wires u).1 = wv n x gs u ∧
       lEv α (wires u).2 = !(wv n x gs u)) →
     (∀ u ≥ n + gs.length, lEv α (wires u).1 = false ∧ lEv α (wires u).2 = true) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ v : V, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ C ∈ (bcg n D gs fd exclOpt k wires st).2.2, ClauseSat α' C) ∧
       (∀ u < n + gs.length, dv n gs u ≤ D →
         lEv α' ((bcg n D gs fd exclOpt k wires st).1 u).1 = wv n x gs u ∧
         lEv α' ((bcg n D gs fd exclOpt k wires st).1 u).2 = !(wv n x gs u)) ∧
       (∀ u ≥ n + gs.length,
         lEv α' ((bcg n D gs fd exclOpt k wires st).1 u).1 = false ∧
         lEv α' ((bcg n D gs fd exclOpt k wires st).1 u).2 = true) := by
 intro m
 induction m with
 | zero =>
   intro k hm wires st α _ _ _ _ _ hsat _ _ hlt hge
   have hge_k : ¬ (k < gs.length) := by omega
   unfold bcg
   simp only [hge_k, ↓reduceDIte]
   refine ⟨α, fun _ _ => rfl, fun _ => rfl, hsat, ?_, hge⟩
   intro u hu hd
   exact hlt u (by omega) hd
 | succ m ih =>
   intro k hm wires st α hst hf1 hf2 hexv hwires hsat hex hfval hlt hge
   have hk : k < gs.length := by omega
   have hm1 : gs.length - (k + 1) = m := by omega
   unfold bcg
   simp only [hk, ↓reduceDIte]
   by_cases hdep : dv n gs (n + k) ≤ D
   · simp only [hdep, ↓reduceIte]
     set wT := (fv st).1
     set st1 := (fv st).2
     set wF := (fv st1).1
     set st2 := (fv st1).2
     set g := gs[k]'hk
     set inL := if g.left < n + k then wires g.left else fd
     set inR := if g.right < n + k then wires g.right else fd
     set st3 := edg g.op inL inR (wT, wF) st2
     set st4 := match exclOpt with
       | none => ei2 wT (negL wF) st3
       | some ex => ei3 wT wF ex st3
     let wires' : ℕ → LN V × LN V :=
       fun u => if u = n + k then (wT, wF) else wires u
     let valk := wv n x gs (n + k)
     let α1 : Sum V ℕ → Bool := fun z =>
       match z with
       | Sum.inl v => α (Sum.inl v)
       | Sum.inr w => if w = st.1 then valk else if w = st.1 + 1 then !valk else α (Sum.inr w)
     have hα1_lt : ∀ w < st.1, α1 (Sum.inr w) = α (Sum.inr w) := by
       intro w hw; simp [α1, show w ≠ st.1 by omega, show w ≠ st.1 + 1 by omega]
     have hα1_inl : ∀ v : V, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
     have hsat2 : ∀ C ∈ st2.2, ClauseSat α1 C := by
       intro C hC
       exact (cscl hα1_inl hα1_lt (hst C hC).2).2 (hsat C hC)
     have hwT_val : lEv α1 wT = valk := by simp [wT, fv, lEv, α1]
     have hwF_val : lEv α1 wF = !valk := by
       simp [wF, st1, fv, lEv, α1, show st.1 + 1 ≠ st.1 by omega]
     have hdep_eq : dv n gs (n + k) =
         max (if g.left < n + k then dv n gs g.left else 0)
             (if g.right < n + k then dv n gs g.right else 0) + 1 := by
       conv_lhs => rw [dv]
       have hnotn : ¬ (n + k < n) := by omega
       have hlt_len : n + k < n + gs.length := by omega
       simp only [hnotn, ↓reduceDIte, hlt_len, Nat.add_sub_cancel_left]
       rfl
     have hvalk_eq : valk = g.op (if g.left < n + k then wv n x gs g.left else false)
         (if g.right < n + k then wv n x gs g.right else false) := by
       dsimp only [valk]
       conv_lhs => rw [wv]
       have hnotn : ¬ (n + k < n) := by omega
       have hlt_len : n + k < n + gs.length := by omega
       simp only [hnotn, ↓reduceDIte, hlt_len, Nat.add_sub_cancel_left]
       rfl
     set lv := if g.left < n + k then wv n x gs g.left else false
     set rv := if g.right < n + k then wv n x gs g.right else false
     have hinL_val : lEv α1 inL.1 = lv ∧ lEv α1 inL.2 = !lv := by
       dsimp only [inL, lv]
       split_ifs with hl
       · have hdL : dv n gs g.left ≤ D := by
           simp only [hl, ↓reduceIte] at hdep_eq; omega
         have hprev := hlt g.left hl hdL
         exact ⟨(lecl hα1_inl hα1_lt (hwires _).1).trans hprev.1,
               (lecl hα1_inl hα1_lt (hwires _).2).trans hprev.2⟩
       · exact ⟨(lecl hα1_inl hα1_lt hf1).trans hfval.1,
               (lecl hα1_inl hα1_lt hf2).trans hfval.2⟩
     have hinR_val : lEv α1 inR.1 = rv ∧ lEv α1 inR.2 = !rv := by
       dsimp only [inR, rv]
       split_ifs with hr
       · have hdR : dv n gs g.right ≤ D := by
           simp only [hr, ↓reduceIte] at hdep_eq; omega
         have hprev := hlt g.right hr hdR
         exact ⟨(lecl hα1_inl hα1_lt (hwires _).1).trans hprev.1,
               (lecl hα1_inl hα1_lt (hwires _).2).trans hprev.2⟩
       · exact ⟨(lecl hα1_inl hα1_lt hf1).trans hfval.1,
               (lecl hα1_inl hα1_lt hf2).trans hfval.2⟩
     have hsat3 : ∀ C ∈ st3.2, ClauseSat α1 C :=
       emitDualGate_sat_of_exact g.op α1 inL inR (wT, wF) st2 lv rv
         hinL_val.1 hinL_val.2 hinR_val.1 hinR_val.2
         (by rw [hwT_val, hvalk_eq]) (by rw [hwF_val, hvalk_eq]) hsat2
     have hsat4 : ∀ C ∈ st4.2, ClauseSat α1 C := by
       cases hopt : exclOpt with
       | none =>
         simp only [st4, hopt, ei2, addCl, List.mem_cons]
         intro C hC
         rcases hC with rfl | hC3
         · rw [clauseSat_imp2, litEval_negL, hwT_val, hwF_val]
           cases valk <;> simp
         · exact hsat3 C hC3
       | some ex =>
         simp only [st4, hopt, ei3, addCl, List.mem_cons]
         intro C hC
         rcases hC with rfl | hC3
         · rw [clauseSat_imp3, hwT_val, hwF_val]
           cases valk <;> simp
         · exact hsat3 C hC3
     have hst2 : VS st2 := validSt_fresh (validSt_fresh hst)
     have hst2_1 : st2.1 = st.1 + 2 := rfl
     have hst4_1 : st4.1 = st.1 + 2 := by
       cases hopt : exclOpt <;> simp [st4, hopt, st3, edg, ei2, ei3, addCl, hst2_1]
     have hwT2 : VL st2.1 wT := (validLit_fresh st).mono (by simp [st1, st2, fv])
     have hwF2 : VL st2.1 wF := by
       change VL (st1.1 + 1) wF
       exact validLit_fresh st1
     have hinL1 : VL st2.1 inL.1 := by
       dsimp only [inL]; split_ifs
       · exact (hwires _).1.mono (by omega)
       · exact hf1.mono (by omega)
     have hinL2 : VL st2.1 inL.2 := by
       dsimp only [inL]; split_ifs
       · exact (hwires _).2.mono (by omega)
       · exact hf2.mono (by omega)
     have hinR1 : VL st2.1 inR.1 := by
       dsimp only [inR]; split_ifs
       · exact (hwires _).1.mono (by omega)
       · exact hf1.mono (by omega)
     have hinR2 : VL st2.1 inR.2 := by
       dsimp only [inR]; split_ifs
       · exact (hwires _).2.mono (by omega)
       · exact hf2.mono (by omega)
     have hst3 : VS st3 := validSt_emitDualGate g.op hst2 hinL1 hinL2 hinR1 hinR2 hwT2 hwF2
     have hst3_1 : st3.1 = st.1 + 2 := hst2_1
     have hwT : VL st4.1 wT := hwT2.mono (by omega)
     have hwF : VL st4.1 wF := hwF2.mono (by omega)
     have hst4 : VS st4 := by
       cases hopt : exclOpt with
       | none =>
         simp only [st4, hopt]
         exact validSt_emitImp2 hst3 (hwT2.mono (by omega)) (validLit_negL.2 (hwF2.mono (by omega)))
       | some ex =>
         simp only [st4, hopt]
         exact validSt_emitImp3 hst3 (hwT2.mono (by omega)) (hwF2.mono (by omega))
           ((hexv ex hopt).mono (by rw [hst3_1]; omega))
     have hwires' : ∀ u, VL st4.1 (wires' u).1 ∧ VL st4.1 (wires' u).2 := by
       intro u; dsimp only [wires']; split_ifs
       · exact ⟨hwT, hwF⟩
       · exact ⟨(hwires u).1.mono (by omega), (hwires u).2.mono (by omega)⟩
     have hex4 : ∀ ex, exclOpt = some ex → VL st4.1 ex :=
       fun ex h => (hexv ex h).mono (by omega)
     have hexval4 : ∀ ex, exclOpt = some ex → lEv α1 ex = false :=
       fun ex h => (lecl hα1_inl hα1_lt (hexv ex h)).trans (hex ex h)
     have hfval4 : lEv α1 fd.1 = false ∧ lEv α1 fd.2 = true :=
       ⟨(lecl hα1_inl hα1_lt hf1).trans hfval.1,
       (lecl hα1_inl hα1_lt hf2).trans hfval.2⟩
     have hlt4 : ∀ u < n + (k + 1), dv n gs u ≤ D →
         lEv α1 (wires' u).1 = wv n x gs u ∧
         lEv α1 (wires' u).2 = !(wv n x gs u) := by
       intro u hu hd
       dsimp only [wires']
       split_ifs with heq
       · subst heq; exact ⟨hwT_val, hwF_val⟩
       · have hu' : u < n + k := by omega
         have hprev := hlt u hu' hd
         exact ⟨(lecl hα1_inl hα1_lt (hwires u).1).trans hprev.1,
               (lecl hα1_inl hα1_lt (hwires u).2).trans hprev.2⟩
     have hge4 : ∀ u ≥ n + gs.length, lEv α1 (wires' u).1 = false ∧ lEv α1 (wires' u).2 = true := by
       intro u hu
       dsimp only [wires']
       split_ifs with heq
       · omega
       · have hprev := hge u hu
         exact ⟨(lecl hα1_inl hα1_lt (hwires u).1).trans hprev.1,
               (lecl hα1_inl hα1_lt (hwires u).2).trans hprev.2⟩
     obtain ⟨α', hlt', hinl', hsat', hres_lt, hres_ge⟩ :=
       ih (k + 1) hm1 wires' st4 α1 hst4 (hf1.mono (by omega)) (hf2.mono (by omega))
         hex4 hwires' hsat4 hexval4 hfval4 hlt4 hge4
     exact ⟨α', fun w hw => (hlt' w (by omega)).trans (hα1_lt w hw),
       fun v => (hinl' v).trans (hα1_inl v), hsat', hres_lt, hres_ge⟩
   · simp only [hdep, ↓reduceIte]
     have hlt' : ∀ u < n + (k + 1), dv n gs u ≤ D →
         lEv α (wires u).1 = wv n x gs u ∧
         lEv α (wires u).2 = !(wv n x gs u) := by
       intro u hu hd
       have hne : u ≠ n + k := by intro h; subst h; exact hdep hd
       exact hlt u (by omega) hd
     exact ih (k + 1) hm1 wires st α hst hf1 hf2 hexv hwires hsat hex hfval hlt' hge

lemma bcg_cm {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) :
   ∀ (m k : ℕ) (hm : gs.length - k = m)
     (wires : ℕ → LN V × LN V) (st : St V),
     ∀ C ∈ st.2, C ∈ (bcg n D gs fd exclOpt k wires st).2.2 := by
 intro m
 induction m with
 | zero =>
   intro k hm wires st C hC
   have hge : ¬ (k < gs.length) := by omega
   unfold bcg
   simp only [hge, ↓reduceDIte]
   exact hC
 | succ m ih =>
   intro k hm wires st C hC
   have hk : k < gs.length := by omega
   have hm1 : gs.length - (k + 1) = m := by omega
   rw [bcg_step n D gs fd exclOpt k hk wires st]
   by_cases hdep : dv n gs (n + k) ≤ D
   · simp only [hdep, ↓reduceIte]
     apply ih (k + 1) hm1
     cases hopt : exclOpt <;> simp [hopt, ei2, ei3, edg, addCl, fv, hC]
   · simp only [hdep, ↓reduceIte]
     exact ih (k + 1) hm1 wires st C hC

lemma bcg_ss {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) (x : Fin n → Bool) :
   ∀ (m k : ℕ) (hm : gs.length - k = m)
     (wires : ℕ → LN V × LN V) (st : St V)
     (α : Sum V ℕ → Bool),
     (∀ C ∈ (bcg n D gs fd exclOpt k wires st).2.2, ClauseSat α C) →
     (∀ ex, exclOpt = some ex → lEv α ex = false) →
     (lEv α fd.1 = false ∧ lEv α fd.2 = true) →
     (∀ u < n + k, dv n gs u ≤ D →
       lEv α (wires u).1 = wv n x gs u ∧
       lEv α (wires u).2 = !(wv n x gs u)) →
     ∀ u < n + gs.length, dv n gs u ≤ D →
       lEv α ((bcg n D gs fd exclOpt k wires st).1 u).1 = wv n x gs u ∧
       lEv α ((bcg n D gs fd exclOpt k wires st).1 u).2 = !(wv n x gs u) := by
 intro m
 induction m with
 | zero =>
   intro k hm wires st α _ _ _ hlt u hu hd
   have hge : ¬ (k < gs.length) := by omega
   unfold bcg
   simp only [hge, ↓reduceDIte]
   exact hlt u (by omega) hd
 | succ m ih =>
   intro k hm wires st α hsat hex hfval hlt
   have hk : k < gs.length := by omega
   have hm1 : gs.length - (k + 1) = m := by omega
   rw [bcg_step n D gs fd exclOpt k hk wires st] at hsat ⊢
   by_cases hdep : dv n gs (n + k) ≤ D
   · simp only [hdep, ↓reduceIte] at hsat ⊢
     set wT := (fv st).1
     set st1 := (fv st).2
     set wF := (fv st1).1
     set st2 := (fv st1).2
     set g := gs[k]'hk
     set inL := if g.left < n + k then wires g.left else fd
     set inR := if g.right < n + k then wires g.right else fd
     set st3 := edg g.op inL inR (wT, wF) st2
     set st4 := match exclOpt with
       | none => ei2 wT (negL wF) st3
       | some ex => ei3 wT wF ex st3
     let wires' : ℕ → LN V × LN V :=
       fun u => if u = n + k then (wT, wF) else wires u
     have hsub4 : ∀ C ∈ st4.2, C ∈ (bcg n D gs fd exclOpt (k + 1) wires' st4).2.2 :=
       bcg_cm n D gs fd exclOpt m (k + 1) hm1 wires' st4
     have hsat4 : ∀ C ∈ st4.2, ClauseSat α C := fun C hC => hsat C (hsub4 C hC)
     have hsat3 : ∀ C ∈ st3.2, ClauseSat α C := by
       intro C hC
       apply hsat4
       cases hopt : exclOpt <;> simp [st4, hopt, ei2, ei3, addCl, hC]
     have hnot : ¬ (lEv α wT = true ∧ lEv α wF = true) := by
       rintro ⟨ht, hf⟩
       cases hopt : exclOpt with
       | none =>
         have hc : ClauseSat α {negL wT, negL wF} := hsat4 _ (by simp [st4, hopt, ei2, addCl])
         rw [clauseSat_imp2, litEval_negL] at hc
         have := hc ht
         simp [hf] at this
       | some ex =>
         have hc : ClauseSat α {negL wT, negL wF, ex} := hsat4 _ (by simp [st4, hopt, ei3, addCl])
         rw [clauseSat_imp3] at hc
         have := hc ht hf
         rw [hex ex hopt] at this
         cases this
     have hdep_eq : dv n gs (n + k) =
         max (if g.left < n + k then dv n gs g.left else 0)
             (if g.right < n + k then dv n gs g.right else 0) + 1 := by
       conv_lhs => rw [dv]
       have hnotn : ¬ (n + k < n) := by omega
       have hlt_len : n + k < n + gs.length := by omega
       simp only [hnotn, ↓reduceDIte, hlt_len, Nat.add_sub_cancel_left]
       rfl
     have hvalk_eq : wv n x gs (n + k) =
         g.op (if g.left < n + k then wv n x gs g.left else false)
             (if g.right < n + k then wv n x gs g.right else false) := by
       conv_lhs => rw [wv]
       have hnotn : ¬ (n + k < n) := by omega
       have hlt_len : n + k < n + gs.length := by omega
       simp only [hnotn, ↓reduceDIte, hlt_len, Nat.add_sub_cancel_left]
       rfl
     set lv := if g.left < n + k then wv n x gs g.left else false
     set rv := if g.right < n + k then wv n x gs g.right else false
     have hinL_val : lEv α inL.1 = lv ∧ lEv α inL.2 = !lv := by
       dsimp only [inL, lv]
       split_ifs with hl
       · have hdL : dv n gs g.left ≤ D := by
           simp only [hl, ↓reduceIte] at hdep_eq; omega
         exact hlt g.left hl hdL
       · exact hfval
     have hinR_val : lEv α inR.1 = rv ∧ lEv α inR.2 = !rv := by
       dsimp only [inR, rv]
       split_ifs with hr
       · have hdR : dv n gs g.right ≤ D := by
           simp only [hr, ↓reduceIte] at hdep_eq; omega
         exact hlt g.right hr hdR
       · exact hfval
     have hexact := emitDualGate_sat_to_exact g.op α inL inR (wT, wF) st2 lv rv
       hinL_val.1 hinL_val.2 hinR_val.1 hinR_val.2 hnot hsat3
     have hlt' : ∀ u < n + (k + 1), dv n gs u ≤ D →
         lEv α (wires' u).1 = wv n x gs u ∧
         lEv α (wires' u).2 = !(wv n x gs u) := by
       intro u hu hd
       dsimp only [wires']
       split_ifs with heq
       · subst heq
         rw [hvalk_eq]
         exact hexact
       · exact hlt u (by omega) hd
     exact ih (k + 1) hm1 wires' st4 α hsat hex hfval hlt'
   · simp only [hdep, ↓reduceIte] at hsat ⊢
     have hlt' : ∀ u < n + (k + 1), dv n gs u ≤ D →
         lEv α (wires u).1 = wv n x gs u ∧
         lEv α (wires u).2 = !(wv n x gs u) := by
       intro u hu hd
       have hne : u ≠ n + k := by intro h; subst h; exact hdep hd
       exact hlt u (by omega) hd
     exact ih (k + 1) hm1 wires st α hsat hex hfval hlt'

lemma bcg_up {V : Type} [DecidableEq V] (n D : ℕ)
   (gs : List BinaryGate)
   (fd : LN V × LN V)
   (exclOpt : Option (LN V)) (x : Fin n → Bool)
   (F : Finset (CN V)) (S : ℕ → Set (LN V))
   (hSmono : ∀ d, S d ⊆ S (d + 1)) (hSstep : ∀ d, upS F (S d) ⊆ S (d + 1)) :
   ∀ (m k : ℕ) (hm : gs.length - k = m)
     (wires : ℕ → LN V × LN V) (st : St V),
     (∀ C ∈ (bcg n D gs fd exclOpt k wires st).2.2, C ∈ F) →
     fd.2 ∈ S 0 →
     (∀ u < n + k, dv n gs u ≤ D →
       lod (wires u) (wv n x gs u) ∈ S (dv n gs u)) →
     ∀ u < n + gs.length, dv n gs u ≤ D →
       lod ((bcg n D gs fd exclOpt k wires st).1 u)
         (wv n x gs u) ∈ S (dv n gs u) := by
 intro m
 induction m with
 | zero =>
   intro k hm wires st _ _ hlt u hu hd
   have hge : ¬ (k < gs.length) := by omega
   unfold bcg
   simp only [hge, ↓reduceDIte]
   exact hlt u (by omega) hd
 | succ m ih =>
   intro k hm wires st hF hf2 hlt
   have hk : k < gs.length := by omega
   have hm1 : gs.length - (k + 1) = m := by omega
   rw [bcg_step n D gs fd exclOpt k hk wires st] at hF ⊢
   by_cases hdep : dv n gs (n + k) ≤ D
   · simp only [hdep, ↓reduceIte] at hF ⊢
     set wT := (fv st).1
     set st1 := (fv st).2
     set wF := (fv st1).1
     set st2 := (fv st1).2
     set g := gs[k]'hk
     set inL := if g.left < n + k then wires g.left else fd
     set inR := if g.right < n + k then wires g.right else fd
     set st3 := edg g.op inL inR (wT, wF) st2
     set st4 := match exclOpt with
       | none => ei2 wT (negL wF) st3
       | some ex => ei3 wT wF ex st3
     let wires' : ℕ → LN V × LN V :=
       fun u => if u = n + k then (wT, wF) else wires u
     have hsub4 : ∀ C ∈ st4.2, C ∈ (bcg n D gs fd exclOpt (k + 1) wires' st4).2.2 :=
       bcg_cm n D gs fd exclOpt m (k + 1) hm1 wires' st4
     have hF3 : ∀ C ∈ st3.2, C ∈ F := by
       intro C hC
       apply hF
       apply hsub4
       cases hopt : exclOpt <;> simp [st4, hopt, ei2, ei3, addCl, hC]
     have hdep_eq : dv n gs (n + k) =
         max (if g.left < n + k then dv n gs g.left else 0)
             (if g.right < n + k then dv n gs g.right else 0) + 1 := by
       conv_lhs => rw [dv]
       have hnotn : ¬ (n + k < n) := by omega
       have hlt_len : n + k < n + gs.length := by omega
       simp only [hnotn, ↓reduceDIte, hlt_len, Nat.add_sub_cancel_left]
       rfl
     have hvalk_eq : wv n x gs (n + k) =
         g.op (if g.left < n + k then wv n x gs g.left else false)
             (if g.right < n + k then wv n x gs g.right else false) := by
       conv_lhs => rw [wv]
       have hnotn : ¬ (n + k < n) := by omega
       have hlt_len : n + k < n + gs.length := by omega
       simp only [hnotn, ↓reduceDIte, hlt_len, Nat.add_sub_cancel_left]
       rfl
     set d := dv n gs (n + k)
     have hd1 : 1 ≤ d := by dsimp only [d]; omega
     have hSle : ∀ a b : ℕ, a ≤ b → S a ⊆ S b := by
       intro a b hab
       induction hab with
       | refl => exact Set.Subset.rfl
       | @step m' _ ihm => exact Set.Subset.trans ihm (hSmono m')
     set lv := if g.left < n + k then wv n x gs g.left else false
     set rv := if g.right < n + k then wv n x gs g.right else false
     have hinL_mem : lod inL lv ∈ S (d - 1) := by
       dsimp only [inL, lv]
       split_ifs with hl
       · have hdL : dv n gs g.left ≤ d - 1 := by
           dsimp only [d]; simp only [hl, ↓reduceIte] at hdep_eq; omega
         exact hSle _ _ hdL (hlt g.left hl (by omega))
       · exact hSle 0 (d - 1) (Nat.zero_le _) hf2
     have hinR_mem : lod inR rv ∈ S (d - 1) := by
       dsimp only [inR, rv]
       split_ifs with hr
       · have hdR : dv n gs g.right ≤ d - 1 := by
           dsimp only [d]; simp only [hr, ↓reduceIte] at hdep_eq; omega
         exact hSle _ _ hdR (hlt g.right hr (by omega))
       · exact hSle 0 (d - 1) (Nat.zero_le _) hf2
     have hgate_mem : lod (wT, wF) (g.op lv rv) ∈ upS F (S (d - 1)) := by
       cases hlv : lv <;> cases hrv : rv
       · have hC : ({negL inL.2, negL inR.2, if g.op false false then wT else wF} : CN V) ∈ F :=
           hF3 _ (by simp [st3, edg, ei3, addCl])
         simpa [lod, hlv, hrv, negL_negL] using
           upStep_unit3 hC (by simpa [lod, hlv, negL_negL] using hinL_mem)
                           (by simpa [lod, hrv, negL_negL] using hinR_mem)
       · have hC : ({negL inL.2, negL inR.1, if g.op false true then wT else wF} : CN V) ∈ F :=
           hF3 _ (by simp [st3, edg, ei3, addCl])
         simpa [lod, hlv, hrv, negL_negL] using
           upStep_unit3 hC (by simpa [lod, hlv, negL_negL] using hinL_mem)
                           (by simpa [lod, hrv, negL_negL] using hinR_mem)
       · have hC : ({negL inL.1, negL inR.2, if g.op true false then wT else wF} : CN V) ∈ F :=
           hF3 _ (by simp [st3, edg, ei3, addCl])
         simpa [lod, hlv, hrv, negL_negL] using
           upStep_unit3 hC (by simpa [lod, hlv, negL_negL] using hinL_mem)
                           (by simpa [lod, hrv, negL_negL] using hinR_mem)
       · have hC : ({negL inL.1, negL inR.1, if g.op true true then wT else wF} : CN V) ∈ F :=
           hF3 _ (by simp [st3, edg, ei3, addCl])
         simpa [lod, hlv, hrv, negL_negL] using
           upStep_unit3 hC (by simpa [lod, hlv, negL_negL] using hinL_mem)
                           (by simpa [lod, hrv, negL_negL] using hinR_mem)
     have hk_mem : lod (wT, wF) (wv n x gs (n + k)) ∈ S d := by
       have heq : d = (d - 1) + 1 := by omega
       rw [heq, hvalk_eq]
       exact hSstep (d - 1) hgate_mem
     have hlt' : ∀ u < n + (k + 1), dv n gs u ≤ D →
         lod (wires' u) (wv n x gs u) ∈ S (dv n gs u) := by
       intro u hu hd
       dsimp only [wires']
       split_ifs with heq
       · subst heq; exact hk_mem
       · exact hlt u (by omega) hd
     exact ih (k + 1) hm1 wires' st4 hF hf2 hlt'
   · simp only [hdep, ↓reduceIte] at hF ⊢
     have hlt' : ∀ u < n + (k + 1), dv n gs u ≤ D →
         lod (wires u) (wv n x gs u) ∈ S (dv n gs u) := by
       intro u hu hd
       have hne : u ≠ n + k := by intro h; subst h; exact hdep hd
       exact hlt u (by omega) hd
     exact ih (k + 1) hm1 wires st hF hf2 hlt'

def boc {n t : ℕ} (out : Fin t → ℕ)
   (wires : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (exclOpt : Option (LN (Fin n ⊕ Fin t))) :
   ℕ → St (Fin n ⊕ Fin t) → St (Fin n ⊕ Fin t)
 | j, st =>
   if hj : j < t then
     let jf : Fin t := ⟨j, hj⟩
     let o := wires (out jf)
     let st1 := match exclOpt with
       | none =>
         ei2 o.2 (Sum.inl (Sum.inr jf), false)
           (ei2 o.1 (Sum.inl (Sum.inr jf), true) st)
       | some ex =>
         ei3 o.2 (Sum.inl (Sum.inr jf), true) ex
           (ei3 o.1 (Sum.inl (Sum.inr jf), false) ex st)
     boc out wires exclOpt (j + 1) st1
   else st
termination_by j => t - j

lemma boc_pr {n t : ℕ} (out : Fin t → ℕ)
   (wires : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (exclOpt : Option (LN (Fin n ⊕ Fin t))) :
   ∀ (m j : ℕ) (hm : t - j = m) (st : St (Fin n ⊕ Fin t)),
     VS st →
     (∀ ex, exclOpt = some ex → VL st.1 ex) →
     (∀ u, VL st.1 (wires u).1 ∧ VL st.1 (wires u).2) →
     let st' := boc out wires exclOpt j st
     VS st' ∧
     st'.1 = st.1 ∧
     st'.2.length ≤ st.2.length + 2 * m ∧
     (∀ C ∈ st.2, C ∈ st'.2) ∧
     (∀ jf : Fin t, j ≤ jf.val →
       let o := wires (out jf)
       match exclOpt with
       | none =>
         {negL o.1, (Sum.inl (Sum.inr jf), true)} ∈ st'.2 ∧
         {negL o.2, (Sum.inl (Sum.inr jf), false)} ∈ st'.2
       | some ex =>
         {negL o.1, negL (Sum.inl (Sum.inr jf), false), ex} ∈ st'.2 ∧
         {negL o.2, negL (Sum.inl (Sum.inr jf), true), ex} ∈ st'.2) := by
 intro m
 induction m with
 | zero =>
   intro j hm st hst _ _
   have hge : ¬ (j < t) := by omega
   unfold boc
   simp only [hge, ↓reduceDIte]
   refine ⟨hst, trivial, by omega, fun _ h => h, fun jf hjf => by exfalso; omega⟩
 | succ m ih =>
   intro j hm st hst hex hwires
   have hj : j < t := by omega
   have hm1 : t - (j + 1) = m := by omega
   unfold boc
   simp only [hj, ↓reduceDIte]
   set jf : Fin t := ⟨j, hj⟩
   set o := wires (out jf)
   set st1 := match exclOpt with
     | none =>
       ei2 o.2 (Sum.inl (Sum.inr jf), false)
         (ei2 o.1 (Sum.inl (Sum.inr jf), true) st)
     | some ex =>
       ei3 o.2 (Sum.inl (Sum.inr jf), true) ex
         (ei3 o.1 (Sum.inl (Sum.inr jf), false) ex st)
   have hst1 : VS st1 := by
     cases hopt : exclOpt with
     | none =>
       simp only [st1, hopt]
       exact validSt_emitImp2 (validSt_emitImp2 hst (hwires _).1 (validLit_inl _ _ _))
         (hwires _).2 (validLit_inl _ _ _)
     | some ex =>
       simp only [st1, hopt]
       exact validSt_emitImp3 (validSt_emitImp3 hst (hwires _).1 (validLit_inl _ _ _) (hex ex hopt))
         (hwires _).2 (validLit_inl _ _ _) (hex ex hopt)
   have hst1_1 : st1.1 = st.1 := by
     cases hopt : exclOpt <;> simp [st1, hopt, ei2, ei3, addCl]
   have hlen1 : st1.2.length = st.2.length + 2 := by
     cases hopt : exclOpt <;> simp [st1, hopt, ei2, ei3, addCl]
   have hsub1 : ∀ C ∈ st.2, C ∈ st1.2 := by
     intro C hC
     cases hopt : exclOpt <;> simp [st1, hopt, ei2, ei3, addCl, hC]
   have hex1 : ∀ ex, exclOpt = some ex → VL st1.1 ex := fun ex h => by rw [hst1_1]; exact hex ex h
   have hwires1 : ∀ u, VL st1.1 (wires u).1 ∧ VL st1.1 (wires u).2 :=
     fun u => by rw [hst1_1]; exact hwires u
   obtain ⟨r1, r2, r3, r4, r5⟩ := ih (j + 1) hm1 st1 hst1 hex1 hwires1
   refine ⟨r1, r2.trans hst1_1, by omega, fun C hC => r4 C (hsub1 C hC), fun jf' hjf' => ?_⟩
   by_cases heq : j = jf'.val
   · have hjfeq : jf = jf' := Fin.ext heq
     rw [← hjfeq]
     cases hopt : exclOpt with
     | none =>
       rw [hopt] at r4
       refine ⟨r4 {negL o.1, (Sum.inl (Sum.inr jf), true)} (by simp [st1, hopt, ei2, addCl]),
               r4 {negL o.2, (Sum.inl (Sum.inr jf), false)} (by simp [st1, hopt, ei2, addCl])⟩
     | some ex =>
       rw [hopt] at r4
       refine ⟨r4 {negL o.1, negL (Sum.inl (Sum.inr jf), false), ex} (by simp [st1, hopt, ei3, addCl]),
               r4 {negL o.2, negL (Sum.inl (Sum.inr jf), true), ex} (by simp [st1, hopt, ei3, addCl])⟩
   · have hj1 : j + 1 ≤ jf'.val := by omega
     exact r5 jf' hj1

lemma boc_sat {n t : ℕ} (out : Fin t → ℕ)
   (wires : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (exclOpt : Option (LN (Fin n ⊕ Fin t))) (α : Sum (Fin n ⊕ Fin t) ℕ → Bool) :
   ∀ (m j : ℕ) (hm : t - j = m) (st : St (Fin n ⊕ Fin t)),
     (∀ C ∈ st.2, ClauseSat α C) →
     ((∃ ex, exclOpt = some ex ∧ lEv α ex = true) ∨
       (∀ jf : Fin t, j ≤ jf.val →
         let o := wires (out jf)
         (lEv α o.1 = true → α (Sum.inl (Sum.inr jf)) = true) ∧
         (lEv α o.2 = true → α (Sum.inl (Sum.inr jf)) = false))) →
     ∀ C ∈ (boc out wires exclOpt j st).2, ClauseSat α C := by
 intro m
 induction m with
 | zero =>
   intro j hm st hst _
   have hge : ¬ (j < t) := by omega
   unfold boc
   simp only [hge, ↓reduceDIte]
   exact hst
 | succ m ih =>
   intro j hm st hst hcond
   have hj : j < t := by omega
   have hm1 : t - (j + 1) = m := by omega
   unfold boc
   simp only [hj, ↓reduceDIte]
   set jf : Fin t := ⟨j, hj⟩
   set o := wires (out jf)
   set st1 := match exclOpt with
     | none =>
       ei2 o.2 (Sum.inl (Sum.inr jf), false)
         (ei2 o.1 (Sum.inl (Sum.inr jf), true) st)
     | some ex =>
       ei3 o.2 (Sum.inl (Sum.inr jf), true) ex
         (ei3 o.1 (Sum.inl (Sum.inr jf), false) ex st)
   have hsat1 : ∀ C ∈ st1.2, ClauseSat α C := by
     cases hopt : exclOpt with
     | none =>
       simp only [st1, hopt, ei2, addCl, List.mem_cons]
       rcases hcond with ⟨ex, h, _⟩ | hok
       · rw [hopt] at h; cases h
       · have hjf := hok jf le_rfl
         intro C hC
         rcases hC with rfl | rfl | hC
         · rw [clauseSat_imp2]; intro h; simpa [lEv] using hjf.2 h
         · rw [clauseSat_imp2]; intro h; simpa [lEv] using hjf.1 h
         · exact hst C hC
     | some ex =>
       simp only [st1, hopt, ei3, addCl, List.mem_cons]
       rcases hcond with ⟨ex', h, hex⟩ | hok
       · rw [hopt] at h; cases h
         intro C hC
         rcases hC with rfl | rfl | hC
         · rw [clauseSat_imp3]; intro _ _; exact hex
         · rw [clauseSat_imp3]; intro _ _; exact hex
         · exact hst C hC
       · have hjf := hok jf le_rfl
         intro C hC
         rcases hC with rfl | rfl | hC
         · rw [clauseSat_imp3]; intro h1 h2
           exfalso
           have := hjf.2 h1
           simp only [lEv] at h2
           rw [this] at h2
           cases h2
         · rw [clauseSat_imp3]; intro h1 h2
           exfalso
           have := hjf.1 h1
           simp only [lEv] at h2
           rw [this] at h2
           cases h2
         · exact hst C hC
   refine ih (j + 1) hm1 st1 hsat1 ?_
   rcases hcond with h | hok
   · exact Or.inl h
   · exact Or.inr fun jf' hjf' => hok jf' (by omega)

lemma enc_conflict_sound {n t m : ℕ} {gates : List BinaryGate}
   {out : Fin t → ℕ}
   {F : Finset (Clause (Sum (Fin n ⊕ Fin t) (Fin m)))}
   (hsat : ∀ v : Fin n ⊕ Fin t → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) →
     ∃ aux : Fin m → Bool, Satisfies (Sum.elim v aux) (↑F : Set _))
   {ρ : Fin n ⊕ Fin t → Option Bool}
   (hcomp : ∃ v : Fin n ⊕ Fin t → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) ∧
     ∀ (raw : Fin n ⊕ Fin t) (sign : Bool), ρ raw = some sign → v raw = sign)
   {d : ℕ} :
   ¬ ∃ C ∈ F, ∀ l ∈ C, negL l ∈ (upS F)^[d] (sd ρ) := by
 rintro ⟨C, hC, hfalse⟩
 obtain ⟨v, hv, hρ⟩ := hcomp
 obtain ⟨aux, haux⟩ := hsat v hv
 have hK := upStep_iter_sound haux (seedOf_sound (aux := aux) hρ) d
 obtain ⟨l, hlC, hl⟩ := haux C hC
 have hneg := hK (negL l) (hfalse l hlC)
 simp only [negL_fst, negL_snd] at hneg
 rw [hl] at hneg
 cases l.2 <;> simp at hneg

lemma enc_force_sound {n t m d : ℕ} {gates : List BinaryGate}
   {out : Fin t → ℕ}
   {F : Finset (Clause (Sum (Fin n ⊕ Fin t) (Fin m)))}
   (hsat : ∀ v : Fin n ⊕ Fin t → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) →
     ∃ aux : Fin m → Bool, Satisfies (Sum.elim v aux) (↑F : Set _))
   {ρ : Fin n ⊕ Fin t → Option Bool} {raw : Fin n ⊕ Fin t} {sign : Bool}
   (hmem : (Sum.inl raw, sign) ∈ (upS F)^[d] (sd ρ)) :
   ∀ v : Fin n ⊕ Fin t → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) →
     (∀ (raw' : Fin n ⊕ Fin t) (sign' : Bool), ρ raw' = some sign' → v raw' = sign') →
     v raw = sign := by
 intro v hv hρ
 obtain ⟨aux, haux⟩ := hsat v hv
 have hK := upStep_iter_sound haux (seedOf_sound (aux := aux) hρ) d
 simpa using hK (Sum.inl raw, sign) hmem

lemma upper_bound_h0 (n t h : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (hh0 : h = 0 ∨ n = 0) :
   let V := Fin n ⊕ Fin t
   let circuit : BinaryCircuit := ⟨gates, 0⟩
   let agrees := fun (v : V → Bool) =>
     let wires := circuit.wires (List.ofFn (fun i : Fin n => v (Sum.inl i)))
     ∀ j : Fin t, v (Sum.inr j) = wires.getD (out j) false
   let depths := gates.foldl (fun (w : List ℕ) g =>
     w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
   let D := (Finset.univ : Finset (Fin t)).sup (fun j => depths.getD (out j) 0)
   let rounds := 128*(D+h+Nat.clog 2 (n+t+1)+1)
   ∃ (m : ℕ) (F : Finset (Clause (Sum V (Fin m)))),
     m + (∑ C ∈ F, C.card) ≤ 262144*(n+t+gates.length+1)*(h+1)^2*(Nat.clog 2 (n+1)+1)*2^h ∧
     (∀ C ∈ F, C.card ≤ 3) ∧
     (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
       Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
     ∀ ρ : V → Option Bool,
       (Finset.univ.filter (fun i : Fin n => ρ (Sum.inl i) = none)).card ≤ h →
       let seed : Set (Literal (Sum V (Fin m))) :=
         {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
       let advance := fun S : Set (Literal (Sum V (Fin m))) =>
         S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
           negL other ∈ S}
       let known := (advance^[rounds]) seed
       let complete := fun v : V → Bool => agrees v ∧
         ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
       ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, negL l ∈ known) ∧
       ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
         (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known) := by
 classical
 let V := Fin n ⊕ Fin t
 let depths := gates.foldl (fun (w : List ℕ) g =>
   w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
 let D := (Finset.univ : Finset (Fin t)).sup (fun j => depths.getD (out j) 0)
 have hD_eq : ∀ u : ℕ, depths.getD u 0 = dv n gates u :=
   (depths_length_and_getD n gates).2
 have hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D := by
   intro j
   rw [← hD_eq (out j)]
   exact Finset.le_sup (f := fun j' : Fin t => depths.getD (out j') 0) (Finset.mem_univ j)
 let tL : LN V := (Sum.inr 0, true)
 let fL : LN V := (Sum.inr 0, false)
 let fd : LN V × LN V := (fL, tL)
 let st0 : St V := eu tL (1, [])
 let wires0 : ℕ → LN V × LN V := fun u =>
   if hu : u < n then ((Sum.inl (Sum.inl ⟨u, hu⟩), true), (Sum.inl (Sum.inl ⟨u, hu⟩), false))
   else fd
 let resG := bcg n D gates fd none 0 wires0 st0
 let st2 := boc out resG.1 none 0 resG.2
 have hst0 : VS st0 := validSt_emitUnit (fun _ h => by simp at h) (fun k hk => by simp [tL] at hk; omega)
 have hf1 : VL st0.1 fd.1 := fun k hk => by simp [fd, fL, st0, eu, addCl] at hk ⊢; omega
 have hf2 : VL st0.1 fd.2 := fun k hk => by simp [fd, tL, st0, eu, addCl] at hk ⊢; omega
 have hw0 : ∀ u, VL st0.1 (wires0 u).1 ∧ VL st0.1 (wires0 u).2 := by
   intro u; dsimp only [wires0]; split_ifs
   · exact ⟨validLit_inl _ _ _, validLit_inl _ _ _⟩
   · exact ⟨hf1, hf2⟩
 have hGprops := bcg_pr n D gates fd none gates.length 0
   (Nat.sub_zero _) wires0 st0 hst0 hf1 hf2 (fun _ h => by cases h) hw0
 rcases hGprops with ⟨hGvalid, hGm1, hGm2, hGl2, hGsub, hGwires, hGlt, hGge⟩
 have hOprops := boc_pr out resG.1 none t 0 (Nat.sub_zero _) resG.2 hGvalid
   (fun _ h => by cases h) hGwires
 rcases hOprops with ⟨hOvalid, hOm, hOl, hOsub, hOmem⟩
 let m : ℕ := st2.1
 have hm : 0 < m := by dsimp only [m]; rw [hOm]; exact Nat.lt_of_lt_of_le (by simp [st0, eu, addCl]) hGm1
 let Fnat : Finset (CN V) := st2.2.toFinset
 let Lfin : List (Cl (Sum V (Fin m))) := st2.2.map (mapCl m hm)
 let Ffin : Finset (Cl (Sum V (Fin m))) := Lfin.toFinset
 have hImgF : ∀ C ∈ Fnat, mapCl m hm C ∈ Ffin := fun C hC =>
   List.mem_toFinset.2 (List.mem_map.2 ⟨C, List.mem_toFinset.1 hC, rfl⟩)
 have hcard3 : ∀ C ∈ Ffin, C.card ≤ 3 := by
   intro C hC
   rcases List.mem_map.1 (List.mem_toFinset.1 hC) with ⟨C', hC', rfl⟩
   exact (mapCl_card_le m hm C').trans (hOvalid C' hC').1
 have hsat_nat : ∀ v : V → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) ↔
     ∃ aux : ℕ → Bool, ∀ C ∈ st2.2, ClauseSat (Sum.elim v aux) C := by
   intro v
   let x : Fin n → Bool := fun i => v (Sum.inl i)
   have hwires_eq : ∀ u : ℕ, ((⟨gates, 0⟩ : BinaryCircuit).wires (List.ofFn x)).getD u false =
       wv n x gates u := (wires_length_and_getD n x gates).2
   constructor
   · intro hag
     let α0 : Sum V ℕ → Bool := Sum.elim v (fun _ => true)
     have hα0_sat : ∀ C ∈ st0.2, ClauseSat α0 C := by
       intro C hC
       simp only [st0, eu, addCl, List.mem_singleton] at hC
       subst hC
       rw [clauseSat_singleton]
       rfl
     have hα0_f : lEv α0 fd.1 = false ∧ lEv α0 fd.2 = true := by
       simp [fd, fL, tL, lEv, α0]
     have hα0_lt : ∀ u < n + 0, dv n gates u ≤ D →
         lEv α0 (wires0 u).1 = wv n x gates u ∧
         lEv α0 (wires0 u).2 = !(wv n x gates u) := by
       intro u hu _
       have hu' : u < n := by omega
       simp only [wires0, hu', ↓reduceDIte, lEv, α0, Sum.elim_inl]
       have hwv : wv n x gates u = x ⟨u, hu'⟩ := by rw [wv]; simp [hu']
       rw [hwv]
       cases hx : x ⟨u, hu'⟩ <;> simp [x, hx]
     have hα0_ge : ∀ u ≥ n + gates.length, lEv α0 (wires0 u).1 = false ∧ lEv α0 (wires0 u).2 = true := by
       intro u hu
       have hnot : ¬ (u < n) := by omega
       simp [wires0, hnot, fd, fL, tL, lEv, α0]
     obtain ⟨α1, h1lt, h1inl, h1sat, h1res_lt, h1res_ge⟩ :=
       bcg_sa n D gates fd none x gates.length 0
         (Nat.sub_zero _) wires0 st0 α0 hst0 hf1 hf2 (fun _ h => by cases h) hw0 hα0_sat
         (fun _ h => by cases h) hα0_f hα0_lt hα0_ge
     have h1out : ∀ C ∈ st2.2, ClauseSat α1 C := by
       refine boc_sat out resG.1 none α1 t 0 (Nat.sub_zero _) resG.2 h1sat (Or.inr fun jf _ => ?_)
       by_cases hlt : out jf < n + gates.length
       · have hres := h1res_lt (out jf) hlt (hD_bound jf)
         have hagj := hag jf
         rw [hwires_eq] at hagj
         have heq : α1 (Sum.inl (Sum.inr jf)) = wv n x gates (out jf) :=
           (h1inl (Sum.inr jf)).trans hagj
         rw [heq]
         exact ⟨fun h => by rw [hres.1] at h; exact h,
               fun h => by rw [hres.2] at h; cases hw : wv n x gates (out jf) <;> simp [hw] at h ⊢⟩
       · have hge : out jf ≥ n + gates.length := by omega
         have hres := h1res_ge (out jf) hge
         have hagj := hag jf
         rw [hwires_eq] at hagj
         have hwv : wv n x gates (out jf) = false := by
           rw [wv]; simp [show ¬ (out jf < n) by omega, hlt]
         have heq : α1 (Sum.inl (Sum.inr jf)) = false :=
           (h1inl (Sum.inr jf)).trans (hagj.trans hwv)
         rw [heq]
         constructor
         · intro h; rw [hres.1] at h; cases h
         · intro _; rfl
     refine ⟨fun k => α1 (Sum.inr k), fun C hC => ?_⟩
     have heq : Sum.elim v (fun k => α1 (Sum.inr k)) = α1 := by
       ext z
       cases z with
       | inl u => exact (h1inl u).symm
       | inr k => rfl
     rw [heq]
     exact h1out C hC
   · rintro ⟨aux, haux⟩ jf
     let α := Sum.elim v aux
     have hsatG : ∀ C ∈ resG.2.2, ClauseSat α C := fun C hC => haux C (hOsub C hC)
     have hsat0 : ∀ C ∈ st0.2, ClauseSat α C := fun C hC => hsatG C (hGsub C hC)
     have htrue : aux 0 = true := by
       have hc := hsat0 {tL} (by simp [st0, eu, addCl])
       rw [clauseSat_singleton] at hc
       simpa [lEv, α, tL] using hc
     have hfval : lEv α fd.1 = false ∧ lEv α fd.2 = true := by
       simp [fd, fL, tL, lEv, α, htrue]
     have hlt0 : ∀ u < n + 0, dv n gates u ≤ D →
         lEv α (wires0 u).1 = wv n x gates u ∧
         lEv α (wires0 u).2 = !(wv n x gates u) := by
       intro u hu _
       have hu' : u < n := by omega
       simp only [wires0, hu', ↓reduceDIte, lEv, α, Sum.elim_inl]
       have hwv : wv n x gates u = x ⟨u, hu'⟩ := by rw [wv]; simp [hu']
       rw [hwv]
       cases hx : x ⟨u, hu'⟩ <;> simp [x, hx]
     have hsound := bcg_ss n D gates fd none x gates.length 0
       (Nat.sub_zero _) wires0 st0 α hsatG (fun _ h => by cases h) hfval hlt0
     have hom := hOmem jf (Nat.zero_le _)
     simp only at hom
     have hc1 := haux _ hom.1
     have hc2 := haux _ hom.2
     rw [clauseSat_imp2] at hc1 hc2
     rw [hwires_eq]
     by_cases hlt : out jf < n + gates.length
     · have hres := hsound (out jf) hlt (hD_bound jf)
       cases hwv : wv n x gates (out jf)
       · have h1 := hc2 (by rw [hres.2, hwv]; rfl)
         simpa [lEv, α] using h1
       · have h1 := hc1 (by rw [hres.1, hwv])
         simpa [lEv, α] using h1
     · have hge : out jf ≥ n + gates.length := by omega
       have hres_eq : resG.1 (out jf) = wires0 (out jf) := hGge (out jf) hge
       have hwv : wv n x gates (out jf) = false := by
         rw [wv]; simp [show ¬ (out jf < n) by omega, hlt]
       have hnotn : ¬ (out jf < n) := by omega
       have h2 : lEv α (resG.1 (out jf)).2 = true := by
         rw [hres_eq]
         simp [wires0, hnotn, fd, tL, lEv, α, htrue]
       have h1 := hc2 h2
       rw [hwv]
       simpa [lEv, α] using h1
 have hsat : ∀ v : V → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) ↔
     ∃ aux : Fin m → Bool, Satisfies (Sum.elim v aux) (↑Ffin : Set _) := by
   intro v
   rw [hsat_nat v]
   constructor
   · rintro ⟨aux, haux⟩
     refine ⟨fun k : Fin m => aux k.val, fun C hC => ?_⟩
     rcases List.mem_map.1 (List.mem_toFinset.1 hC) with ⟨C', hC', rfl⟩
     exact mapCl_sat_of_nat m hm v aux (hOvalid C' hC').2 (haux C' hC')
   · rintro ⟨auxFin, haux⟩
     refine ⟨fun k => if hk : k < m then auxFin ⟨k, hk⟩ else false, fun C hC => ?_⟩
     have hmem : mapCl m hm C ∈ Ffin := List.mem_toFinset.2 (List.mem_map.2 ⟨C, hC, rfl⟩)
     exact mapCl_sat_to_nat m hm v auxFin (hOvalid C hC).2 (haux _ hmem)
 refine ⟨m, Ffin, ?_, hcard3, hsat, ?_⟩
 · have hsum1 : (∑ C ∈ Ffin, C.card) ≤ (Lfin.map Finset.card).sum := sum_toFinset_card_le Lfin
   have hsum2 : (Lfin.map Finset.card).sum ≤ 3 * Lfin.length :=
     sum_map_card_le Lfin 3 fun D hD => hcard3 D (List.mem_toFinset.2 hD)
   have hLlen : Lfin.length = st2.2.length := by simp [Lfin]
   have hst0_1 : st0.1 = 1 := rfl
   have hst0_2 : st0.2.length = 1 := rfl
   have hresG1 : resG.2.1 ≤ 1 + 2 * gates.length := by
     dsimp only [resG]
     rw [← hst0_1]
     exact hGm2
   have hresG2 : resG.2.2.length ≤ 1 + 5 * gates.length := by
     dsimp only [resG]
     rw [← hst0_2]
     exact hGl2
   have hm_le : m ≤ 1 + 2 * gates.length := by
     dsimp only [m, st2]
     rw [hOm]
     exact hresG1
   have hcl_le : st2.2.length ≤ 1 + 5 * gates.length + 2 * t := by
     dsimp only [st2]
     omega
   have h1 : 1 ≤ (h + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
   have h2 : 1 ≤ Nat.clog 2 (n + 1) + 1 := by omega
   have h3 : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by omega)
   have h4 : 0 < (h + 1) ^ 2 * (Nat.clog 2 (n + 1) + 1) * 2 ^ h :=
     Nat.mul_pos (Nat.mul_pos h1 h2) h3
   have htot : m + (∑ C ∈ Ffin, C.card) ≤ 4 + 17 * gates.length + 6 * t := by omega
   have hrhs : 4 + 17 * gates.length + 6 * t ≤ 262144 * (n + t + gates.length + 1) := by linarith
   have hmul : 262144 * (n + t + gates.length + 1) ≤
       262144 * (n + t + gates.length + 1) * (h + 1) ^ 2 * (Nat.clog 2 (n + 1) + 1) * 2 ^ h := by
     calc 262144 * (n + t + gates.length + 1)
       _ ≤ 262144 * (n + t + gates.length + 1) * ((h + 1) ^ 2 * (Nat.clog 2 (n + 1) + 1) * 2 ^ h) :=
         Nat.le_mul_of_pos_right _ h4
       _ = 262144 * (n + t + gates.length + 1) * (h + 1) ^ 2 * (Nat.clog 2 (n + 1) + 1) * 2 ^ h := by ring
   exact le_trans htot (le_trans hrhs hmul)
 · intro ρ hρ
   let rounds := 128 * (D + h + Nat.clog 2 (n + t + 1) + 1)
   have hnone_empty : ∀ i : Fin n, ρ (Sum.inl i) ≠ none := by
     intro i hi
     rcases hh0 with rfl | rfl
     · have hpos : 0 < (Finset.univ.filter (fun i : Fin n => ρ (Sum.inl i) = none)).card :=
         Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
       omega
     · exact Fin.elim0 i
   let x : Fin n → Bool := fun i =>
     match ρ (Sum.inl i) with
     | some b => b
     | none => false
   have hx_seed : ∀ i : Fin n, (Sum.inl (Sum.inl i), x i) ∈ (sd ρ : Set (LN V)) := by
     intro i
     dsimp only [x]
     cases hri : ρ (Sum.inl i) with
     | none => exact absurd hri (hnone_empty i)
     | some b => exact ⟨Sum.inl i, rfl, hri⟩
   have hFnat_sub : ∀ C ∈ st2.2, C ∈ Fnat := fun C hC => List.mem_toFinset.2 hC
   have htrue_up : tL ∈ (upS Fnat)^[1] (sd ρ) := by
     rw [Function.iterate_one]
     exact upStep_unit1 (hFnat_sub _ (hOsub _ (hGsub _ (by simp [st0, eu, addCl]))))
   have hup_gates : ∀ u < n + gates.length, dv n gates u ≤ D →
       lod (resG.1 u) (wv n x gates u) ∈
         (upS Fnat)^[dv n gates u + 1] (sd ρ) := by
     refine bcg_up n D gates fd none x Fnat
       (fun d => (upS Fnat)^[d + 1] (sd ρ))
       (fun d => upStep_iter_le Fnat (sd ρ) (by omega))
       (fun d => by
         rw [Function.iterate_succ_apply' (upS Fnat) (d + 1) (sd ρ)])
       gates.length 0 (Nat.sub_zero _) wires0 st0
       (fun C hC => hFnat_sub C (hOsub C hC))
       (by simpa [fd] using htrue_up) ?_
     intro u hu _
     have hu' : u < n := by omega
     have hdep0 : dv n gates u = 0 := by rw [dv]; simp [hu']
     have hwv : wv n x gates u = x ⟨u, hu'⟩ := by rw [wv]; simp [hu']
     rw [hdep0, hwv]
     refine upStep_iter_le Fnat (sd ρ) (Nat.le_refl 1) ?_
     rw [Function.iterate_one]
     apply subset_upStep
     dsimp only [wires0]
     simp only [hu', ↓reduceDIte]
     cases hx : x ⟨u, hu'⟩ <;> simpa [lod, hx] using hx_seed ⟨u, hu'⟩
   have hup_out : ∀ j : Fin t,
       let w := wv n x gates (out j)
       lod (resG.1 (out j)) w ∈ (upS Fnat)^[D + 1] (sd ρ) := by
     intro j
     by_cases hlt : out j < n + gates.length
     · exact upStep_iter_le Fnat (sd ρ) (Nat.add_le_add_right (hD_bound j) 1)
         (hup_gates (out j) hlt (hD_bound j))
     · have hge : out j ≥ n + gates.length := by omega
       have hwv : wv n x gates (out j) = false := by
         rw [wv]; simp [show ¬ (out j < n) by omega, hlt]
       have hres_eq : resG.1 (out j) = wires0 (out j) := hGge (out j) hge
       have hnotn : ¬ (out j < n) := by omega
       rw [hwv, hres_eq]
       simp only [wires0, hnotn, ↓reduceDIte, fd, lod, Bool.false_eq_true]
       exact upStep_iter_le Fnat (sd ρ) (by omega) htrue_up
   have hrounds_ge : D + 2 ≤ rounds := by
     dsimp only [rounds]
     omega
   let v0 : V → Bool := fun raw =>
     match raw with
     | Sum.inl i => x i
     | Sum.inr j => wv n x gates (out j)
   have hv0_ag : ∀ j : Fin t, v0 (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v0 (Sum.inl i)))).getD (out j) false := by
     intro j
     rw [(wires_length_and_getD n (fun i => v0 (Sum.inl i)) gates).2 (out j)]
   constructor
   · constructor
     · intro hno
       have hbad_j : ∃ j : Fin t, ρ (Sum.inr j) = some (!(v0 (Sum.inr j))) := by
         by_contra hnone
         push Not at hnone
         apply hno
         refine ⟨v0, hv0_ag, fun raw sign hraw => ?_⟩
         cases raw with
         | inl i =>
           have h1 := hx_seed i
           rw [sd] at h1
           rcases h1 with ⟨raw', hraw', hρ'⟩
           have : Sum.inl i = raw' := Sum.inl.inj hraw'
           subst this
           rw [hraw] at hρ'
           exact (Option.some.inj hρ').symm
         | inr j =>
           have hnj := hnone j
           cases hs : sign
           · cases hv : v0 (Sum.inr j)
             · rfl
             · rw [hs] at hraw; exact absurd hraw (by simpa [hv] using hnj)
           · cases hv : v0 (Sum.inr j)
             · rw [hs] at hraw; exact absurd hraw (by simpa [hv] using hnj)
             · rfl
       obtain ⟨j, hj⟩ := hbad_j
       have hom := hOmem j (Nat.zero_le _)
       dsimp only at hom
       have hmem_out := hup_out j
       cases hv : v0 (Sum.inr j) with
       | false =>
         have hC_nat : ({negL (resG.1 (out j)).2, (Sum.inl (Sum.inr j), false)} : CN V) ∈ Fnat :=
           hFnat_sub _ hom.2
         refine ⟨mapCl m hm _, hImgF _ hC_nat, fun l hl => ?_⟩
         rcases Finset.mem_image.1 hl with ⟨l0, hl0, rfl⟩
         change negL (mapLit m hm l0) ∈ (upS Ffin)^[rounds] (sd ρ)
         rw [← mapLit_negL m hm l0]
         apply upStep_map_transport m hm Fnat Ffin hImgF ρ rounds
         simp only [Finset.mem_insert, Finset.mem_singleton] at hl0
         rcases hl0 with rfl | rfl
         · rw [negL_negL]
           have hmem1 : (resG.1 (out j)).2 ∈ (upS Fnat)^[D + 1] (sd ρ) := by
             change lod (resG.1 (out j)) false ∈ _
             rw [← hv]
             exact hmem_out
           exact upStep_iter_le Fnat (sd ρ) (Nat.le_trans (Nat.le_succ _) hrounds_ge) hmem1
         · exact upStep_iter_le Fnat (sd ρ) (Nat.zero_le _) ⟨Sum.inr j, rfl, by simpa [hv, negL, PEqualNP.Search.negLit] using hj⟩
       | true =>
         have hC_nat : ({negL (resG.1 (out j)).1, (Sum.inl (Sum.inr j), true)} : CN V) ∈ Fnat :=
           hFnat_sub _ hom.1
         refine ⟨mapCl m hm _, hImgF _ hC_nat, fun l hl => ?_⟩
         rcases Finset.mem_image.1 hl with ⟨l0, hl0, rfl⟩
         change negL (mapLit m hm l0) ∈ (upS Ffin)^[rounds] (sd ρ)
         rw [← mapLit_negL m hm l0]
         apply upStep_map_transport m hm Fnat Ffin hImgF ρ rounds
         simp only [Finset.mem_insert, Finset.mem_singleton] at hl0
         rcases hl0 with rfl | rfl
         · rw [negL_negL]
           have hmem1 : (resG.1 (out j)).1 ∈ (upS Fnat)^[D + 1] (sd ρ) := by
             change lod (resG.1 (out j)) true ∈ _
             rw [← hv]
             exact hmem_out
           exact upStep_iter_le Fnat (sd ρ) (Nat.le_trans (Nat.le_succ _) hrounds_ge) hmem1
         · exact upStep_iter_le Fnat (sd ρ) (Nat.zero_le _) ⟨Sum.inr j, rfl, by simpa [hv, negL, PEqualNP.Search.negLit] using hj⟩
     · intro hconf hcomp
       exact enc_conflict_sound (d := rounds) (fun v hv => (hsat v).1 hv) hcomp hconf
   · intro hcomp raw sign
     constructor
     · intro hforced
       obtain ⟨v, hv_ag, hv_ρ⟩ := hcomp
       have heqv : v = v0 := by
         ext z
         cases z with
         | inl i =>
           have h1 := hx_seed i
           rcases h1 with ⟨raw', hraw', hρ'⟩
           have : Sum.inl i = raw' := Sum.inl.inj hraw'
           subst this
           exact hv_ρ (Sum.inl i) (x i) hρ'
         | inr j =>
           rw [hv_ag j, hv0_ag j]
           congr 2
           apply List.ofFn_inj.2
           ext i
           have h1 := hx_seed i
           rcases h1 with ⟨raw', hraw', hρ'⟩
           have : Sum.inl i = raw' := Sum.inl.inj hraw'
           subst this
           exact hv_ρ (Sum.inl i) (x i) hρ'
       have hsign : v0 raw = sign := by rw [← heqv]; exact hforced v ⟨hv_ag, hv_ρ⟩
       have hnat : (Sum.inl raw, sign) ∈ (upS Fnat)^[rounds] (sd ρ) := by
         cases raw with
         | inl i =>
           have h1 := hx_seed i
           rcases h1 with ⟨raw', hraw', hρ'⟩
           have : Sum.inl i = raw' := Sum.inl.inj hraw'
           subst this
           have hx_eq : x i = sign := hsign
           rw [← hx_eq]
           exact upStep_iter_le Fnat (sd ρ) (Nat.zero_le _) ⟨Sum.inl i, rfl, hρ'⟩
         | inr j =>
           have hom := hOmem j (Nat.zero_le _)
           dsimp only at hom
           have hmem_out := hup_out j
           have hv0j : wv n x gates (out j) = sign := hsign
           have hstep : (Sum.inl (Sum.inr j), sign) ∈ (upS Fnat)^[D + 2] (sd ρ) := by
             rw [Function.iterate_succ_apply']
             cases hsn : sign
             · have hC : ({negL (resG.1 (out j)).2, (Sum.inl (Sum.inr j), false)} : CN V) ∈ Fnat :=
                 hFnat_sub _ hom.2
               exact upStep_unit2 hC (by rw [negL_negL]; simpa [hv0j, hsn, lod] using hmem_out)
             · have hC : ({negL (resG.1 (out j)).1, (Sum.inl (Sum.inr j), true)} : CN V) ∈ Fnat :=
                 hFnat_sub _ hom.1
               exact upStep_unit2 hC (by rw [negL_negL]; simpa [hv0j, hsn, lod] using hmem_out)
           exact upStep_iter_le Fnat (sd ρ) hrounds_ge hstep
       have htr := upStep_map_transport m hm Fnat Ffin hImgF ρ rounds (Sum.inl raw, sign) hnat
       exact htr
     · intro hmem v ⟨hv_ag, hv_ρ⟩
       exact enc_force_sound (d := rounds) (fun v' hv' => (hsat v').1 hv') hmem v hv_ag hv_ρ

lemma clauseSat_congr {W : Type} {α β : W → Bool} {C : Cl W}
   (h : ∀ l ∈ C, lEv α l = lEv β l) (hC : ClauseSat β C) : ClauseSat α C := by
 rw [clauseSat_iff] at hC ⊢
 obtain ⟨l, hlC, hle⟩ := hC
 exact ⟨l, hlC, (h l hlC).trans hle⟩

lemma xorList_append (L1 L2 : List Bool) :
   xl (L1 ++ L2) = (xl L1 ^^ xl L2) := by
 induction L1 with
 | nil => simp [xl]
 | cons a rest ih => simp [xl, ih, Bool.xor_assoc]

def bat {V : Type} [DecidableEq V] :
   BTree (LN V) → St V → LN V × St V
 | .leaf a, st => (a, st)
 | .node l r, st =>
   let p1 := bat l st
   let p2 := bat r p1.2
   let p3 := fv p2.2
   (p3.1, ea p1.1 p2.1 p3.1 p3.2)

lemma bat_pr {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V),
     VS st →
     (∀ a ∈ t.leaves, VL st.1 a) →
     let res := bat t st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + t.nodes ∧
     res.2.2.length ≤ st.2.length + 3 * t.nodes ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     VL res.2.1 res.1
 | .leaf a, st, hst, ha => by
   refine ⟨hst, le_rfl, by simp [bat, BTree.nodes], by simp [bat, BTree.nodes],
     fun _ h => h, ha a (by simp [BTree.leaves])⟩
 | .node l r, st, hst, ha => by
   have hal : ∀ a ∈ l.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_left h)
   have har0 : ∀ a ∈ r.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_right h)
   obtain ⟨hst1, hle1, hm1, hl1, hsub1, hv1⟩ := bat_pr l st hst hal
   have har : ∀ a ∈ r.leaves, VL (bat l st).2.1 a :=
     fun a h => VL.mono hle1 (har0 a h)
   obtain ⟨hst2, hle2, hm2, hl2, hsub2, hv2⟩ := bat_pr r (bat l st).2 hst1 har
   set st2 := (bat r (bat l st).2).2
   set p3 := fv st2
   have hp3st : VS p3.2 := validSt_fresh hst2
   have hp3_1 : p3.2.1 = st2.1 + 1 := rfl
   have hp3_v : VL p3.2.1 p3.1 := validLit_fresh st2
   have hst3 : VS (ea (bat l st).1 (bat r (bat l st).2).1 p3.1 p3.2) :=
     validSt_emitAnd hp3st (VL.mono (by omega) hv1) (VL.mono (by omega) hv2) hp3_v
   refine ⟨hst3, ?_, ?_, ?_, ?_, ?_⟩
   · simp only [bat, ea, ei2, ei3, addCl, fv]
     change st.1 ≤ st2.1 + 1; omega
   · simp only [bat, BTree.nodes, ea, ei2, ei3, addCl]
     change st2.1 + 1 ≤ _; omega
   · simp only [bat, BTree.nodes, ea, ei2, ei3, addCl, List.length_cons]
     change st2.2.length + 3 ≤ _; omega
   · intro C hC
     simp only [bat, ea, ei2, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (hsub2 C (hsub1 C hC))))
   · simpa [bat, ea, ei2, ei3, addCl] using hp3_v

lemma bat_sa {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ a ∈ t.leaves, VL st.1 a) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bat t st).2.2, ClauseSat α' C) ∧
       lEv α' (bat t st).1 = t.leaves.all (lEv α)
 | .leaf a, st, α, _, _, hsat =>
   ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, by simp [bat, BTree.leaves]⟩
 | .node l r, st, α, hst, ha, hsat => by
   have hal : ∀ a ∈ l.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_left h)
   have har0 : ∀ a ∈ r.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_right h)
   obtain ⟨hst1, hle1, _, _, _, hv1⟩ := bat_pr l st hst hal
   obtain ⟨α1, h1inl, h1lt, h1sat, h1val⟩ := bat_sa l st α hst hal hsat
   have har : ∀ a ∈ r.leaves, VL (bat l st).2.1 a :=
     fun a h => VL.mono hle1 (har0 a h)
   obtain ⟨hst2, hle2, _, _, _, hv2⟩ := bat_pr r (bat l st).2 hst1 har
   obtain ⟨α2, h2inl, h2lt, h2sat, h2val⟩ := bat_sa r (bat l st).2 α1 hst1 har h1sat
   have hα2_eq_α1 : ∀ a, VL (bat l st).2.1 a → lEv α2 a = lEv α1 a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, h2inl v]
     | inr k => simp [lEv, ha1, h2lt k (hva k ha1)]
   have hall_r : r.leaves.all (lEv α1) = r.leaves.all (lEv α) := by
     rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
     refine ⟨fun h a ha' => ?_, fun h a ha' => ?_⟩
     · have h1 := h a ha'
       cases ha1 : a.1 with
       | inl v => simpa [lEv, ha1, h1inl v] using h1
       | inr k => simpa [lEv, ha1, h1lt k (har0 a ha' k ha1)] using h1
     · have h1 := h a ha'
       cases ha1 : a.1 with
       | inl v => simpa [lEv, ha1, h1inl v] using h1
       | inr k => simpa [lEv, ha1, h1lt k (har0 a ha' k ha1)] using h1
   set st2 := (bat r (bat l st).2).2
   let valZ := l.leaves.all (lEv α) && r.leaves.all (lEv α)
   let α3 : Sum V ℕ → Bool := fun w =>
     match w with
     | Sum.inl v => α2 (Sum.inl v)
     | Sum.inr k => if k = st2.1 then valZ else α2 (Sum.inr k)
   have hα3_eq_α2 : ∀ a, VL st2.1 a → lEv α3 a = lEv α2 a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, α3]
     | inr k =>
       have hne : k ≠ st2.1 := Nat.ne_of_lt (hva k ha1)
       simp [lEv, ha1, α3, hne]
   have hsat3 : ∀ C ∈ st2.2, ClauseSat α3 C := by
     intro C hC
     exact clauseSat_congr (fun a haC => hα3_eq_α2 a ((hst2 C hC).2 a haC)) (h2sat C hC)
   have hval_z : lEv α3 (fv st2).1 = valZ := by
     simp [fv, lEv, α3]
   have hval_l : lEv α3 (bat l st).1 = l.leaves.all (lEv α) := by
     rw [hα3_eq_α2 _ (VL.mono hle2 hv1), hα2_eq_α1 _ hv1, h1val]
   have hval_r : lEv α3 (bat r (bat l st).2).1 = r.leaves.all (lEv α) := by
     rw [hα3_eq_α2 _ hv2, h2val]
     cases hrl : r.leaves.all (lEv α1)
     · cases hr0 : r.leaves.all (lEv α)
       · rfl
       · rw [hr0] at hall_r; cases hall_r.symm.trans hrl
     · cases hr0 : r.leaves.all (lEv α)
       · rw [hrl] at hall_r; cases (hall_r.trans hr0).symm
       · rfl
   refine ⟨α3, fun v => (h2inl v).trans (h1inl v), fun k hk => ?_, ?_, ?_⟩
   · have hne : k ≠ st2.1 := by omega
     simp only [α3, hne, ↓reduceIte]
     exact (h2lt k (by omega)).trans (h1lt k hk)
   · change ∀ C ∈ (ea _ _ _ (fv st2).2).2, ClauseSat α3 C
     rw [emitAnd_sat_iff]
     refine ⟨?_, hsat3⟩
     rw [hval_z, hval_l, hval_r]
   · simp only [bat, BTree.leaves, List.all_append]
     exact hval_z

lemma bat_ss {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V) (α : Sum V ℕ → Bool),
     (∀ C ∈ (bat t st).2.2, ClauseSat α C) →
     (∀ C ∈ st.2, ClauseSat α C) ∧
     lEv α (bat t st).1 = t.leaves.all (lEv α)
 | .leaf a, st, α, h => ⟨h, by simp [bat, BTree.leaves]⟩
 | .node l r, st, α, h => by
   change ∀ C ∈ (ea _ _ _ (fv (bat r (bat l st).2).2).2).2,
     ClauseSat α C at h
   rw [emitAnd_sat_iff] at h
   obtain ⟨hz, h2⟩ := h
   obtain ⟨h1, hr⟩ := bat_ss r (bat l st).2 α h2
   obtain ⟨h0, hl⟩ := bat_ss l st α h1
   refine ⟨h0, ?_⟩
   simp only [bat, BTree.leaves, List.all_append]
   rw [hz, hl, hr]

lemma bat_cm {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bat t st).2.2
 | .leaf _, _, _, hC => hC
 | .node l r, st, C, hC => by
   simp only [bat, ea, ei2, ei3, addCl, List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (bat_cm r (bat l st).2 C
     (bat_cm l st C hC))))

lemma bat_up {V : Type} [DecidableEq V] (F : Finset (CN V)) (S : Set (LN V)) :
   ∀ (t : BTree (LN V)) (st : St V) (d : ℕ),
     (∀ C ∈ (bat t st).2.2, C ∈ F) →
     (∀ a ∈ t.leaves, a ∈ (upS F)^[d] S) →
     (bat t st).1 ∈ (upS F)^[d + t.depth] S
 | .leaf a, st, d, _, ha => by
   simpa [bat, BTree.depth] using ha a (by simp [BTree.leaves])
 | .node l r, st, d, hF, ha => by
   set p1 := bat l st
   set p2 := bat r p1.2
   have hFr : ∀ C ∈ p2.2.2, C ∈ F := fun C hC => by
     apply hF
     simp only [bat, ea, ei2, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr hC))
   have hFl : ∀ C ∈ p1.2.2, C ∈ F :=
     fun C hC => hFr C (bat_cm r p1.2 C hC)
   have hl_mem : p1.1 ∈ (upS F)^[d + l.depth] S :=
     bat_up F S l st d hFl (fun a h => ha a (BTree.mem_leaves_node_left h))
   have hr_mem : p2.1 ∈ (upS F)^[d + r.depth] S :=
     bat_up F S r p1.2 d hFr (fun a h => ha a (BTree.mem_leaves_node_right h))
   have hmax1 : d + l.depth ≤ d + max l.depth r.depth := Nat.add_le_add_left (le_max_left _ _) d
   have hmax2 : d + r.depth ≤ d + max l.depth r.depth := Nat.add_le_add_left (le_max_right _ _) d
   have hl' : p1.1 ∈ (upS F)^[d + max l.depth r.depth] S := upStep_iter_le F S hmax1 hl_mem
   have hr' : p2.1 ∈ (upS F)^[d + max l.depth r.depth] S := upStep_iter_le F S hmax2 hr_mem
   have hC : ({negL p1.1, negL p2.1, (fv p2.2).1} : CN V) ∈ F := by
     apply hF
     simp only [bat, ea, ei2, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inl rfl))
   have hz : (fv p2.2).1 ∈ (upS F)^[d + (max l.depth r.depth + 1)] S := by
     rw [show d + (max l.depth r.depth + 1) = (d + max l.depth r.depth) + 1 by omega]
     rw [Function.iterate_succ_apply']
     exact upStep_unit3 hC (by simpa [negL_negL] using hl') (by simpa [negL_negL] using hr')
   simpa [bat, BTree.depth] using hz

def bot {V : Type} [DecidableEq V] :
   BTree (LN V) → St V → LN V × St V
 | .leaf a, st => (a, st)
 | .node l r, st =>
   let p1 := bot l st
   let p2 := bot r p1.2
   let p3 := fv p2.2
   (p3.1, eo p1.1 p2.1 p3.1 p3.2)

lemma bot_cm {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bot t st).2.2
 | .leaf _, _, _, hC => hC
 | .node l r, st, C, hC => by
   simp only [bot, eo, ec3, ei2, addCl, List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (bot_cm r (bot l st).2 C
     (bot_cm l st C hC))))

lemma bot_pr {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V),
     VS st →
     (∀ a ∈ t.leaves, VL st.1 a) →
     let res := bot t st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + t.nodes ∧
     res.2.2.length ≤ st.2.length + 3 * t.nodes ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     VL res.2.1 res.1
 | .leaf a, st, hst, ha => by
   refine ⟨hst, le_rfl, by simp [bot, BTree.nodes], by simp [bot, BTree.nodes],
     fun _ h => h, ha a (by simp [BTree.leaves])⟩
 | .node l r, st, hst, ha => by
   have hal : ∀ a ∈ l.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_left h)
   have har0 : ∀ a ∈ r.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_right h)
   obtain ⟨hst1, hle1, hm1, hl1, hsub1, hv1⟩ := bot_pr l st hst hal
   have har : ∀ a ∈ r.leaves, VL (bot l st).2.1 a :=
     fun a h => VL.mono hle1 (har0 a h)
   obtain ⟨hst2, hle2, hm2, hl2, hsub2, hv2⟩ := bot_pr r (bot l st).2 hst1 har
   set st2 := (bot r (bot l st).2).2
   set p3 := fv st2
   have hp3st : VS p3.2 := validSt_fresh hst2
   have hp3_1 : p3.2.1 = st2.1 + 1 := rfl
   have hp3_2 : p3.2.2 = st2.2 := rfl
   have hp3_v : VL p3.2.1 p3.1 := validLit_fresh st2
   have hst3 : VS (eo (bot l st).1 (bot r (bot l st).2).1 p3.1 p3.2) :=
     validSt_emitOr hp3st (VL.mono (by omega) hv1) (VL.mono (by omega) hv2) hp3_v
   refine ⟨hst3, ?_, ?_, ?_, ?_, ?_⟩
   · simp only [bot, eo, ec3, ei2, addCl, fv]
     change st.1 ≤ st2.1 + 1; omega
   · simp only [bot, BTree.nodes, eo, ec3, ei2, addCl]
     change st2.1 + 1 ≤ _; omega
   · simp only [bot, BTree.nodes, eo, ec3, ei2, addCl, List.length_cons]
     change st2.2.length + 3 ≤ _; omega
   · intro C hC
     simp only [bot, eo, ec3, ei2, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (hsub2 C (hsub1 C hC))))
   · simpa [bot, eo, ec3, ei2, addCl] using hp3_v

lemma bot_sa {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ a ∈ t.leaves, VL st.1 a) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bot t st).2.2, ClauseSat α' C) ∧
       lEv α' (bot t st).1 = t.leaves.any (lEv α)
 | .leaf a, st, α, _, _, hsat =>
   ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, by simp [bot, BTree.leaves]⟩
 | .node l r, st, α, hst, ha, hsat => by
   have hal : ∀ a ∈ l.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_left h)
   have har0 : ∀ a ∈ r.leaves, VL st.1 a := fun a h => ha a (BTree.mem_leaves_node_right h)
   obtain ⟨hst1, hle1, _, _, _, hv1⟩ := bot_pr l st hst hal
   obtain ⟨α1, h1inl, h1lt, h1sat, h1val⟩ := bot_sa l st α hst hal hsat
   have har : ∀ a ∈ r.leaves, VL (bot l st).2.1 a :=
     fun a h => VL.mono hle1 (har0 a h)
   obtain ⟨hst2, hle2, _, _, _, hv2⟩ := bot_pr r (bot l st).2 hst1 har
   obtain ⟨α2, h2inl, h2lt, h2sat, h2val⟩ := bot_sa r (bot l st).2 α1 hst1 har h1sat
   have hα2_eq_α1 : ∀ a, VL (bot l st).2.1 a → lEv α2 a = lEv α1 a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, h2inl v]
     | inr k =>
       have hk : k < (bot l st).2.1 := hva k ha1
       simp [lEv, ha1, h2lt k hk]
   have hany_r : r.leaves.any (lEv α1) = r.leaves.any (lEv α) := by
     rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
     constructor
     · rintro ⟨a, ha', h1⟩
       refine ⟨a, ha', ?_⟩
       cases ha1 : a.1 with
       | inl v => simpa [lEv, ha1, h1inl v] using h1
       | inr k => simpa [lEv, ha1, h1lt k (har0 a ha' k ha1)] using h1
     · rintro ⟨a, ha', h1⟩
       refine ⟨a, ha', ?_⟩
       cases ha1 : a.1 with
       | inl v => simpa [lEv, ha1, h1inl v] using h1
       | inr k => simpa [lEv, ha1, h1lt k (har0 a ha' k ha1)] using h1
   set st2 := (bot r (bot l st).2).2
   let valZ := l.leaves.any (lEv α) || r.leaves.any (lEv α)
   let α3 : Sum V ℕ → Bool := fun w =>
     match w with
     | Sum.inl v => α2 (Sum.inl v)
     | Sum.inr k => if k = st2.1 then valZ else α2 (Sum.inr k)
   have hα3_eq_α2 : ∀ a, VL st2.1 a → lEv α3 a = lEv α2 a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, α3]
     | inr k =>
       have hne : k ≠ st2.1 := Nat.ne_of_lt (hva k ha1)
       simp [lEv, ha1, α3, hne]
   have hsat3 : ∀ C ∈ st2.2, ClauseSat α3 C := by
     intro C hC
     exact clauseSat_congr (fun a haC => hα3_eq_α2 a ((hst2 C hC).2 a haC)) (h2sat C hC)
   have hval_z : lEv α3 (fv st2).1 = valZ := by
     simp [fv, lEv, α3]
   have hval_l : lEv α3 (bot l st).1 = l.leaves.any (lEv α) := by
     rw [hα3_eq_α2 _ (VL.mono hle2 hv1), hα2_eq_α1 _ hv1, h1val]
   have hval_r : lEv α3 (bot r (bot l st).2).1 = r.leaves.any (lEv α) := by
     rw [hα3_eq_α2 _ hv2, h2val, hany_r]
   refine ⟨α3, fun v => (h2inl v).trans (h1inl v), fun k hk => ?_, ?_, ?_⟩
   · have hne : k ≠ st2.1 := by omega
     simp only [α3, hne, ↓reduceIte]
     exact (h2lt k (by omega)).trans (h1lt k hk)
   · change ∀ C ∈ (eo _ _ _ (fv st2).2).2, ClauseSat α3 C
     rw [emitOr_sat_iff]
     refine ⟨?_, hsat3⟩
     rw [hval_z, hval_l, hval_r]
   · simp only [bot, BTree.leaves, List.any_append]
     exact hval_z

lemma bot_ss {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V)) (st : St V) (α : Sum V ℕ → Bool),
     (∀ C ∈ (bot t st).2.2, ClauseSat α C) →
     (∀ C ∈ st.2, ClauseSat α C) ∧
     lEv α (bot t st).1 = t.leaves.any (lEv α)
 | .leaf a, st, α, h => ⟨h, by simp [bot, BTree.leaves]⟩
 | .node l r, st, α, h => by
   change ∀ C ∈ (eo _ _ _ (fv (bot r (bot l st).2).2).2).2,
     ClauseSat α C at h
   rw [emitOr_sat_iff] at h
   obtain ⟨hz, h2⟩ := h
   obtain ⟨h1, hr⟩ := bot_ss r (bot l st).2 α h2
   obtain ⟨h0, hl⟩ := bot_ss l st α h1
   refine ⟨h0, ?_⟩
   simp only [bot, BTree.leaves, List.any_append]
   rw [hz, hl, hr]

lemma bot_up {V : Type} [DecidableEq V] (F : Finset (CN V)) (S : Set (LN V)) :
   ∀ (t : BTree (LN V)) (st : St V) (d : ℕ),
     (∀ C ∈ (bot t st).2.2, C ∈ F) →
     (∃ a ∈ t.leaves, a ∈ (upS F)^[d] S) →
     (bot t st).1 ∈ (upS F)^[d + t.depth] S
 | .leaf a, st, d, _, ⟨b, hb, hm⟩ => by
   simp only [BTree.leaves, List.mem_singleton] at hb
   subst hb
   simpa [bot, BTree.depth] using hm
 | .node l r, st, d, hF, ⟨b, hb, hm⟩ => by
   set p1 := bot l st
   set p2 := bot r p1.2
   have hFr : ∀ C ∈ p2.2.2, C ∈ F := fun C hC => by
     apply hF
     simp only [bot, eo, ec3, ei2, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr hC))
   have hFl : ∀ C ∈ p1.2.2, C ∈ F :=
     fun C hC => hFr C (bot_cm r p1.2 C hC)
   have hC_l : ({negL p1.1, (fv p2.2).1} : CN V) ∈ F := by
     apply hF
     simp only [bot, eo, ec3, ei2, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inl rfl))
   have hC_r : ({negL p2.1, (fv p2.2).1} : CN V) ∈ F := by
     apply hF
     simp only [bot, eo, ec3, ei2, addCl, List.mem_cons]
     exact Or.inr (Or.inl rfl)
   simp only [BTree.leaves, List.mem_append] at hb
   rcases hb with hbl | hbr
   · have hl_mem : p1.1 ∈ (upS F)^[d + l.depth] S := bot_up F S l st d hFl ⟨b, hbl, hm⟩
     have hl' : p1.1 ∈ (upS F)^[d + max l.depth r.depth] S :=
       upStep_iter_le F S (Nat.add_le_add_left (le_max_left _ _) d) hl_mem
     have hz : (fv p2.2).1 ∈ (upS F)^[d + (max l.depth r.depth + 1)] S := by
       rw [show d + (max l.depth r.depth + 1) = (d + max l.depth r.depth) + 1 by omega]
       rw [Function.iterate_succ_apply']
       exact upStep_unit2 hC_l (by simpa [negL_negL] using hl')
     simpa [bot, BTree.depth] using hz
   · have hr_mem : p2.1 ∈ (upS F)^[d + r.depth] S := bot_up F S r p1.2 d hFr ⟨b, hbr, hm⟩
     have hr' : p2.1 ∈ (upS F)^[d + max l.depth r.depth] S :=
       upStep_iter_le F S (Nat.add_le_add_left (le_max_right _ _) d) hr_mem
     have hz : (fv p2.2).1 ∈ (upS F)^[d + (max l.depth r.depth + 1)] S := by
       rw [show d + (max l.depth r.depth + 1) = (d + max l.depth r.depth) + 1 by omega]
       rw [Function.iterate_succ_apply']
       exact upStep_unit2 hC_r (by simpa [negL_negL] using hr')
     simpa [bot, BTree.depth] using hz

def bdxt {V : Type} [DecidableEq V] :
   BTree (LN V × LN V) → St V → (LN V × LN V) × St V
 | .leaf a, st => (a, st)
 | .node l r, st =>
   let p1 := bdxt l st
   let p2 := bdxt r p1.2
   let p3 := fv p2.2
   let p4 := fv p3.2
   ((p3.1, p4.1), edg Bool.xor p1.1 p2.1 (p3.1, p4.1) p4.2)

lemma bdxt_cm {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V × LN V)) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bdxt t st).2.2
 | .leaf _, _, _, hC => hC
 | .node l r, st, C, hC => by
   simp only [bdxt, edg, ei3, addCl, List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (Or.inr (bdxt_cm r (bdxt l st).2 C
     (bdxt_cm l st C hC)))))

lemma bdxt_pr {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V × LN V)) (st : St V),
     VS st →
     (∀ a ∈ t.leaves, VL st.1 a.1 ∧ VL st.1 a.2) →
     let res := bdxt t st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + 2 * t.nodes ∧
     res.2.2.length ≤ st.2.length + 4 * t.nodes ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     VL res.2.1 res.1.1 ∧ VL res.2.1 res.1.2
 | .leaf a, st, hst, ha => by
   have h0 := ha a (by simp [BTree.leaves])
   refine ⟨hst, le_rfl, by simp [bdxt, BTree.nodes], by simp [bdxt, BTree.nodes],
     fun _ h => h, h0.1, h0.2⟩
 | .node l r, st, hst, ha => by
   have hal : ∀ a ∈ l.leaves, VL st.1 a.1 ∧ VL st.1 a.2 :=
     fun a h => ha a (BTree.mem_leaves_node_left h)
   have har0 : ∀ a ∈ r.leaves, VL st.1 a.1 ∧ VL st.1 a.2 :=
     fun a h => ha a (BTree.mem_leaves_node_right h)
   obtain ⟨hst1, hle1, hm1, hl1, hsub1, hv1a, hv1b⟩ := bdxt_pr l st hst hal
   have har : ∀ a ∈ r.leaves, VL (bdxt l st).2.1 a.1 ∧
       VL (bdxt l st).2.1 a.2 :=
     fun a h => ⟨VL.mono hle1 (har0 a h).1, VL.mono hle1 (har0 a h).2⟩
   obtain ⟨hst2, hle2, hm2, hl2, hsub2, hv2a, hv2b⟩ :=
     bdxt_pr r (bdxt l st).2 hst1 har
   set st2 := (bdxt r (bdxt l st).2).2
   set p3 := fv st2
   set p4 := fv p3.2
   have hp3st : VS p3.2 := validSt_fresh hst2
   have hp4st : VS p4.2 := validSt_fresh hp3st
   have hst4 : VS (edg Bool.xor (bdxt l st).1
       (bdxt r (bdxt l st).2).1 (p3.1, p4.1) p4.2) :=
     validSt_emitDualGate Bool.xor hp4st
       (VL.mono (by change _ ≤ st2.1 + 2; omega) hv1a)
       (VL.mono (by change _ ≤ st2.1 + 2; omega) hv1b)
       (VL.mono (by change _ ≤ st2.1 + 2; omega) hv2a)
       (VL.mono (by change _ ≤ st2.1 + 2; omega) hv2b)
       (VL.mono (by change st2.1 + 1 ≤ st2.1 + 2; omega) (validLit_fresh st2))
       (validLit_fresh p3.2)
   refine ⟨hst4, ?_, ?_, ?_, ?_, ?_, ?_⟩
   · simp only [bdxt, edg, ei3, addCl]; change st.1 ≤ st2.1 + 2; omega
   · simp only [bdxt, BTree.nodes, edg, ei3, addCl]; change st2.1 + 2 ≤ _; omega
   · simp only [bdxt, BTree.nodes, edg, ei3, addCl, List.length_cons]
     change st2.2.length + 4 ≤ _; omega
   · intro C hC
     simp only [bdxt, edg, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr (hsub2 C (hsub1 C hC)))))
   · simp only [bdxt, edg, ei3, addCl]
     exact VL.mono (by change st2.1 + 1 ≤ st2.1 + 2; omega) (validLit_fresh st2)
   · simp only [bdxt, edg, ei3, addCl]
     exact validLit_fresh p3.2

lemma bdxt_fst_le {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V × LN V)) (st : St V),
     st.1 ≤ (bdxt t st).2.1
 | .leaf _, _ => le_rfl
 | .node l r, st => by
   simp only [bdxt, edg, ei3, addCl]
   have h1 := bdxt_fst_le l st
   have h2 := bdxt_fst_le r (bdxt l st).2
   change st.1 ≤ (bdxt r (bdxt l st).2).2.1 + 2
   omega

lemma bdxt_si {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V × LN V)) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ C ∈ st.2, ClauseSat α C) →
     let α' : Sum V ℕ → Bool := fun w =>
       match w with
       | Sum.inl v => α (Sum.inl v)
       | Sum.inr k => if k < st.1 then α (Sum.inr k) else true
     ∀ C ∈ (bdxt t st).2.2, ClauseSat α' C := by
 intro t st α hst hsat α'
 have hbase : ∀ C ∈ st.2, ClauseSat α' C := by
   intro C hC
   refine clauseSat_congr (fun a ha => ?_) (hsat C hC)
   cases ha1 : a.1 with
   | inl v => simp [lEv, ha1, α']
   | inr k => simp [lEv, ha1, α', (hst C hC).2 a ha k ha1]
 have haux : ∀ (t' : BTree (LN V × LN V)) (st' : St V),
     st.1 ≤ st'.1 →
     (∀ C ∈ st'.2, ClauseSat α' C) →
     ∀ C ∈ (bdxt t' st').2.2, ClauseSat α' C := by
   intro t'
   induction t' with
   | leaf a => intro st' _ hst'; exact hst'
   | node l r ihl ihr =>
     intro st' hle hst'
     set p1 := bdxt l st'
     set p2 := bdxt r p1.2
     have hle1 : st'.1 ≤ p1.2.1 := bdxt_fst_le l st'
     have hle2 : p1.2.1 ≤ p2.2.1 := bdxt_fst_le r p1.2
     have hsat1 := ihl st' hle hst'
     have hsat2 := ihr p1.2 (le_trans hle hle1) hsat1
     set p3 := fv p2.2
     set p4 := fv p3.2
     have hne1 : ¬ (p2.2.1 < st.1) := by omega
     have hne2 : ¬ (p3.2.1 < st.1) := by
       have hp3eq : p3.2.1 = p2.2.1 + 1 := rfl
       omega
     have hz1 : lEv α' p3.1 = true := by simp [p3, fv, lEv, α', hne1]
     have hz2 : lEv α' p4.1 = true := by
       have hp4_1 : p4.1 = (Sum.inr p3.2.1, true) := rfl
       simp [hp4_1, lEv, α', hne2]
     exact emitDualGate_sat_of_both Bool.xor α' p1.1 p2.1 (p3.1, p4.1) p4.2 hz1 hz2 hsat2
 exact haux t st le_rfl hbase

lemma bdxt_sa {V : Type} [DecidableEq V] :
   ∀ (t : BTree (LN V × LN V)) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ a ∈ t.leaves, VL st.1 a.1 ∧ VL st.1 a.2) →
     (∀ a ∈ t.leaves, lEv α a.2 = !(lEv α a.1)) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bdxt t st).2.2, ClauseSat α' C) ∧
       lEv α' (bdxt t st).1.1 = xl (t.leaves.map (fun a => lEv α a.1)) ∧
       lEv α' (bdxt t st).1.2 = !(xl (t.leaves.map (fun a => lEv α a.1)))
 | .leaf a, st, α, _, _, hanti, hsat => by
   have h0 := hanti a (by simp [BTree.leaves])
   refine ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, ?_, ?_⟩
   · simp [bdxt, BTree.leaves, xl]
   · simp [bdxt, BTree.leaves, xl, h0]
 | .node l r, st, α, hst, ha, hanti, hsat => by
   have hal : ∀ a ∈ l.leaves, VL st.1 a.1 ∧ VL st.1 a.2 :=
     fun a h => ha a (BTree.mem_leaves_node_left h)
   have har0 : ∀ a ∈ r.leaves, VL st.1 a.1 ∧ VL st.1 a.2 :=
     fun a h => ha a (BTree.mem_leaves_node_right h)
   have hantil : ∀ a ∈ l.leaves, lEv α a.2 = !(lEv α a.1) :=
     fun a h => hanti a (BTree.mem_leaves_node_left h)
   have hantr0 : ∀ a ∈ r.leaves, lEv α a.2 = !(lEv α a.1) :=
     fun a h => hanti a (BTree.mem_leaves_node_right h)
   obtain ⟨hst1, hle1, _, _, _, hv1a, hv1b⟩ := bdxt_pr l st hst hal
   obtain ⟨α1, h1inl, h1lt, h1sat, h1v1, h1v2⟩ :=
     bdxt_sa l st α hst hal hantil hsat
   have har : ∀ a ∈ r.leaves, VL (bdxt l st).2.1 a.1 ∧
       VL (bdxt l st).2.1 a.2 :=
     fun a h => ⟨VL.mono hle1 (har0 a h).1, VL.mono hle1 (har0 a h).2⟩
   have hα1_eq_α : ∀ a, VL st.1 a → lEv α1 a = lEv α a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, h1inl v]
     | inr k => simp [lEv, ha1, h1lt k (hva k ha1)]
   have hantr : ∀ a ∈ r.leaves, lEv α1 a.2 = !(lEv α1 a.1) := by
     intro a ha'
     rw [hα1_eq_α a.2 (har0 a ha').2, hα1_eq_α a.1 (har0 a ha').1]
     exact hantr0 a ha'
   obtain ⟨hst2, hle2, _, _, _, hv2a, hv2b⟩ :=
     bdxt_pr r (bdxt l st).2 hst1 har
   obtain ⟨α2, h2inl, h2lt, h2sat, h2v1, h2v2⟩ :=
     bdxt_sa r (bdxt l st).2 α1 hst1 har hantr h1sat
   have hα2_eq_α1 : ∀ a, VL (bdxt l st).2.1 a → lEv α2 a = lEv α1 a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, h2inl v]
     | inr k => simp [lEv, ha1, h2lt k (hva k ha1)]
   have hmap_r : r.leaves.map (fun a => lEv α1 a.1) = r.leaves.map (fun a => lEv α a.1) := by
     refine List.map_congr_left fun a ha' => hα1_eq_α a.1 (har0 a ha').1
   set st2 := (bdxt r (bdxt l st).2).2
   let vl := xl (l.leaves.map (fun a => lEv α a.1))
   let vr := xl (r.leaves.map (fun a => lEv α a.1))
   let vz := vl ^^ vr
   let α3 : Sum V ℕ → Bool := fun w =>
     match w with
     | Sum.inl v => α2 (Sum.inl v)
     | Sum.inr k => if k = st2.1 then vz else if k = st2.1 + 1 then !vz else α2 (Sum.inr k)
   have hα3_eq_α2 : ∀ a, VL st2.1 a → lEv α3 a = lEv α2 a := by
     intro a hva
     cases ha1 : a.1 with
     | inl v => simp [lEv, ha1, α3]
     | inr k =>
       have hne1 : k ≠ st2.1 := Nat.ne_of_lt (hva k ha1)
       have hne2 : k ≠ st2.1 + 1 := by have := hva k ha1; omega
       simp [lEv, ha1, α3, hne1, hne2]
   have hsat3 : ∀ C ∈ st2.2, ClauseSat α3 C := by
     intro C hC
     exact clauseSat_congr (fun a haC => hα3_eq_α2 a ((hst2 C hC).2 a haC)) (h2sat C hC)
   have h1a : lEv α3 (bdxt l st).1.1 = vl := by
     rw [hα3_eq_α2 _ (VL.mono hle2 hv1a), hα2_eq_α1 _ hv1a, h1v1]
   have h1b : lEv α3 (bdxt l st).1.2 = !vl := by
     rw [hα3_eq_α2 _ (VL.mono hle2 hv1b), hα2_eq_α1 _ hv1b, h1v2]
   have h2a : lEv α3 (bdxt r (bdxt l st).2).1.1 = vr := by
     rw [hα3_eq_α2 _ hv2a, h2v1, hmap_r]
   have h2b : lEv α3 (bdxt r (bdxt l st).2).1.2 = !vr := by
     rw [hα3_eq_α2 _ hv2b, h2v2, hmap_r]
   have hzT : lEv α3 (fv st2).1 = vz := by simp [fv, lEv, α3]
   have hzF : lEv α3 (fv (fv st2).2).1 = !vz := by
     have hp1 : (fv st2).2.1 = st2.1 + 1 := rfl
     have hne : ¬ (st2.1 + 1 = st2.1) := by omega
     simp [fv, lEv, α3, hp1, hne]
   refine ⟨α3, fun v => (h2inl v).trans (h1inl v), fun k hk => ?_, ?_, ?_, ?_⟩
   · have hne1 : k ≠ st2.1 := by omega
     have hne2 : k ≠ st2.1 + 1 := by omega
     simp only [α3, hne1, ↓reduceIte, hne2]
     exact (h2lt k (by omega)).trans (h1lt k hk)
   · change ∀ C ∈ (edg Bool.xor _ _ _ (fv (fv st2).2).2).2, ClauseSat α3 C
     exact emitDualGate_sat_of_exact Bool.xor α3 _ _ _ _ vl vr h1a h1b h2a h2b hzT hzF hsat3
   · simp only [bdxt, BTree.leaves, List.map_append, xorList_append]
     exact hzT
   · simp only [bdxt, BTree.leaves, List.map_append, xorList_append]
     exact hzF

lemma bdxt_up {V : Type} [DecidableEq V] (F : Finset (CN V)) (S : Set (LN V))
   (val : LN V × LN V → Bool) :
   ∀ (t : BTree (LN V × LN V)) (st : St V) (d : ℕ),
     (∀ C ∈ (bdxt t st).2.2, C ∈ F) →
     (∀ a ∈ t.leaves, lod a (val a) ∈ (upS F)^[d] S) →
     lod (bdxt t st).1 (xl (t.leaves.map val)) ∈ (upS F)^[d + t.depth] S
 | .leaf a, st, d, _, ha => by
   simpa [bdxt, BTree.depth, BTree.leaves, xl] using ha a (by simp [BTree.leaves])
 | .node l r, st, d, hF, ha => by
   set p1 := bdxt l st
   set p2 := bdxt r p1.2
   have hFr : ∀ C ∈ p2.2.2, C ∈ F := fun C hC => by
     apply hF
     simp only [bdxt, edg, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
   have hFl : ∀ C ∈ p1.2.2, C ∈ F :=
     fun C hC => hFr C (bdxt_cm r p1.2 C hC)
   have hl_mem := bdxt_up F S val l st d hFl (fun a h => ha a (BTree.mem_leaves_node_left h))
   have hr_mem := bdxt_up F S val r p1.2 d hFr (fun a h => ha a (BTree.mem_leaves_node_right h))
   set vl := xl (l.leaves.map val)
   set vr := xl (r.leaves.map val)
   have hl' : lod p1.1 vl ∈ (upS F)^[d + max l.depth r.depth] S :=
     upStep_iter_le F S (Nat.add_le_add_left (le_max_left _ _) d) hl_mem
   have hr' : lod p2.1 vr ∈ (upS F)^[d + max l.depth r.depth] S :=
     upStep_iter_le F S (Nat.add_le_add_left (le_max_right _ _) d) hr_mem
   set p3 := fv p2.2
   set p4 := fv p3.2
   have hstep : lod (p3.1, p4.1) (vl ^^ vr) ∈
       (upS F)^[d + (max l.depth r.depth + 1)] S := by
     rw [show d + (max l.depth r.depth + 1) = (d + max l.depth r.depth) + 1 by omega]
     rw [Function.iterate_succ_apply']
     cases hvl : vl <;> cases hvr : vr
     · have hC : ({negL p1.1.2, negL p2.1.2, p4.1} : CN V) ∈ F := by
         apply hF; simp [bdxt, edg, ei3, addCl, p1, p2, p3, p4]
       simpa [lod, hvl, hvr, negL_negL] using
         upStep_unit3 hC (by simpa [lod, hvl, negL_negL] using hl')
                         (by simpa [lod, hvr, negL_negL] using hr')
     · have hC : ({negL p1.1.2, negL p2.1.1, p3.1} : CN V) ∈ F := by
         apply hF; simp [bdxt, edg, ei3, addCl, p1, p2, p3, p4]
       simpa [lod, hvl, hvr, negL_negL] using
         upStep_unit3 hC (by simpa [lod, hvl, negL_negL] using hl')
                         (by simpa [lod, hvr, negL_negL] using hr')
     · have hC : ({negL p1.1.1, negL p2.1.2, p3.1} : CN V) ∈ F := by
         apply hF; simp [bdxt, edg, ei3, addCl, p1, p2, p3, p4]
       simpa [lod, hvl, hvr, negL_negL] using
         upStep_unit3 hC (by simpa [lod, hvl, negL_negL] using hl')
                         (by simpa [lod, hvr, negL_negL] using hr')
     · have hC : ({negL p1.1.1, negL p2.1.1, p4.1} : CN V) ∈ F := by
         apply hF; simp [bdxt, edg, ei3, addCl, p1, p2, p3, p4]
       simpa [lod, hvl, hvr, negL_negL] using
         upStep_unit3 hC (by simpa [lod, hvl, negL_negL] using hl')
                         (by simpa [lod, hvr, negL_negL] using hr')
   simpa [bdxt, BTree.depth, BTree.leaves, List.map_append, xorList_append] using hstep

lemma emitAnd_up {V : Type} [DecidableEq V] {F : Finset (CN V)} {S : Set (LN V)}
   {a b z : LN V} {st : St V}
   (hF : ∀ C ∈ (ea a b z st).2, C ∈ F) (ha : a ∈ S) (hb : b ∈ S) :
   z ∈ upS F S := by
 have hC : ({negL a, negL b, z} : CN V) ∈ F := hF _ (by simp [ea, ei2, ei3, addCl])
 exact upStep_unit3 hC (by simpa [negL_negL] using ha) (by simpa [negL_negL] using hb)

lemma emitXor_up {V : Type} [DecidableEq V] {F : Finset (CN V)} {S : Set (LN V)}
   {a b z : LN V} {st : St V} {va vb : Bool}
   (hF : ∀ C ∈ (exr a b z st).2, C ∈ F) (ha : fLt a va ∈ S) (hb : fLt b vb ∈ S) :
   fLt z (va ^^ vb) ∈ upS F S := by
 cases va <;> cases vb
 · have hC : ({negL (negL a), negL (negL b), negL z} : CN V) ∈ F :=
     hF _ (by simp [exr, edg, ei3, addCl])
   rw [negL_negL, negL_negL] at hC
   simpa [fLt] using upStep_unit3 hC (by simpa [fLt, negL_negL] using ha)
     (by simpa [fLt, negL_negL] using hb)
 · have hC : ({negL (negL a), negL b, z} : CN V) ∈ F :=
     hF _ (by simp [exr, edg, ei3, addCl])
   rw [negL_negL] at hC
   simpa [fLt] using upStep_unit3 hC (by simpa [fLt, negL_negL] using ha)
     (by simpa [fLt, negL_negL] using hb)
 · have hC : ({negL a, negL (negL b), z} : CN V) ∈ F :=
     hF _ (by simp [exr, edg, ei3, addCl])
   rw [negL_negL] at hC
   simpa [fLt] using upStep_unit3 hC (by simpa [fLt, negL_negL] using ha)
     (by simpa [fLt, negL_negL] using hb)
 · have hC : ({negL a, negL b, negL z} : CN V) ∈ F :=
     hF _ (by simp [exr, edg, ei3, addCl])
   simpa [fLt] using upStep_unit3 hC (by simpa [fLt, negL_negL] using ha)
     (by simpa [fLt, negL_negL] using hb)

def BTree.intNodes {α : Type} : BTree α → ℕ
 | .leaf _ => 0
 | .node l r => 1 + l.intNodes + r.intNodes

lemma BTree.intNodes_add_one {α : Type} : ∀ t : BTree α, t.intNodes + 1 = t.leaves.length
 | .leaf _ => rfl
 | .node l r => by
   simp only [BTree.intNodes, BTree.leaves, List.length_append]
   have h1 := BTree.intNodes_add_one l
   have h2 := BTree.intNodes_add_one r
   omega

inductive UET (V α : Type) where
 | leaf (i : α) (upA upX : LN V) : UET V α
 | node (upA upX : LN V) (l r : UET V α) : UET V α

def UET.upA {V α : Type} : UET V α → LN V
 | .leaf _ a _ => a
 | .node a _ _ _ => a

def UET.upX {V α : Type} : UET V α → LN V
 | .leaf _ _ x => x
 | .node _ x _ _ => x

def UET.depth {V α : Type} : UET V α → ℕ
 | .leaf _ _ _ => 0
 | .node _ _ l r => max l.depth r.depth + 1

def UET.intNodes {V α : Type} : UET V α → ℕ
 | .leaf _ _ _ => 0
 | .node _ _ l r => 1 + l.intNodes + r.intNodes

def UET.leaves {V α : Type} : UET V α → List α
 | .leaf i _ _ => [i]
 | .node _ _ l r => l.leaves ++ r.leaves

def UTV {V α : Type} (m : ℕ) : UET V α → Prop
 | .leaf _ a b => VL m a ∧ VL m b
 | .node a b l r => VL m a ∧ VL m b ∧ UTV m l ∧ UTV m r

lemma UTV.mono {V α : Type} {m1 m2 : ℕ} (h : m1 ≤ m2) :
   ∀ {u : UET V α}, UTV m1 u → UTV m2 u
 | .leaf _ _ _, ⟨ha, hb⟩ => ⟨ha.mono h, hb.mono h⟩
 | .node _ _ l r, ⟨ha, hb, hl, hr⟩ => ⟨ha.mono h, hb.mono h, hl.mono h, hr.mono h⟩

lemma UTV.root {V α : Type} {m : ℕ} :
   ∀ {u : UET V α}, UTV m u → VL m u.upA ∧ VL m u.upX
 | .leaf _ _ _, h => h
 | .node _ _ _ _, ⟨ha, hb, _, _⟩ => ⟨ha, hb⟩

def UpSat {V : Type} {n : ℕ} (α : Sum V ℕ → Bool) (S : Fin n → Bool) (x : Fin n → Bool) :
   UET V (Fin n) → Prop
 | .leaf i a b => lEv α a = true ∧ lEv α b = (if S i then x i else false)
 | .node a b l r =>
   lEv α a = true ∧
   lEv α b = xl ((UET.node a b l r).leaves.map (fun i => if S i then x i else false)) ∧
   UpSat α S x l ∧ UpSat α S x r

lemma UpSat.root {V : Type} {n : ℕ} {α : Sum V ℕ → Bool} {S x : Fin n → Bool} :
   ∀ {u : UET V (Fin n)}, UpSat α S x u →
     lEv α u.upA = true ∧
     lEv α u.upX = xl (u.leaves.map (fun i => if S i then x i else false))
 | .leaf _ _ _, ⟨h1, h2⟩ => ⟨h1, by simpa [UET.upX, UET.leaves, xl] using h2⟩
 | .node _ _ _ _, ⟨h1, h2, _, _⟩ => ⟨h1, h2⟩

lemma UpSat.congr_lt {V : Type} {n m : ℕ} {α1 α2 : Sum V ℕ → Bool}
   (hinl : ∀ v : V, α1 (Sum.inl v) = α2 (Sum.inl v))
   (hinr : ∀ w < m, α1 (Sum.inr w) = α2 (Sum.inr w))
   (S x : Fin n → Bool) :
   ∀ {u : UET V (Fin n)}, UTV m u → UpSat α1 S x u → UpSat α2 S x u
 | .leaf _ _ _, ⟨ha, hb⟩, ⟨h1, h2⟩ =>
   ⟨by rw [← lecl hinl hinr ha]; exact h1,
   by rw [← lecl hinl hinr hb]; exact h2⟩
 | .node _ _ _ _, ⟨ha, hb, hl, hr⟩, ⟨h1, h2, hsl, hsr⟩ =>
   ⟨by rw [← lecl hinl hinr ha]; exact h1,
   by rw [← lecl hinl hinr hb]; exact h2,
   hsl.congr_lt hinl hinr S x hl, hsr.congr_lt hinl hinr S x hr⟩

def UpReady {V : Type} (F : Finset (CN V)) (seed : Set (LN V))
   {n : ℕ} (S x : Fin n → Bool) (i : Fin n) : UET V (Fin n) → Prop
 | .leaf j a b =>
   j ≠ i → a ∈ (upS F)^[1] seed ∧ fLt b (if S j then x j else false) ∈ (upS F)^[1] seed
 | .node a b l r =>
   UpReady F seed S x i l ∧ UpReady F seed S x i r ∧
   (i ∉ (UET.node a b l r).leaves →
     a ∈ (upS F)^[(UET.node a b l r).depth + 1] seed ∧
     fLt b (xl ((UET.node a b l r).leaves.map (fun j => if S j then x j else false))) ∈
       (upS F)^[(UET.node a b l r).depth + 1] seed)

lemma UpReady.root {V : Type} {F : Finset (CN V)} {seed : Set (LN V)}
   {n : ℕ} {S x : Fin n → Bool} {i : Fin n} :
   ∀ {u : UET V (Fin n)}, UpReady F seed S x i u → i ∉ u.leaves →
     u.upA ∈ (upS F)^[u.depth + 1] seed ∧
     fLt u.upX (xl (u.leaves.map (fun j => if S j then x j else false))) ∈
       (upS F)^[u.depth + 1] seed
 | .leaf j _ _, h, hni => by
   have hne : j ≠ i := fun heq => hni (by simp [UET.leaves, heq])
   simpa [UET.upA, UET.upX, UET.depth, UET.leaves, xl] using h hne
 | .node _ _ _ _, ⟨_, _, h⟩, hni => h hni

def bue {V : Type} [DecidableEq V] {n : ℕ}
   (S : Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) :
   BTree (Fin n) → St V → UET V (Fin n) × St V
 | .leaf i, st =>
   let p := if S i then (kL i, xLit i) else (tL, fL)
   (.leaf i p.1 p.2, st)
 | .node l r, st =>
   let p1 := bue S kL xLit tL fL l st
   let p2 := bue S kL xLit tL fL r p1.2
   let pA := fv p2.2
   let pX := fv pA.2
   let st1 := ea p1.1.upA p2.1.upA pA.1 pX.2
   let st2 := exr p1.1.upX p2.1.upX pX.1 st1
   (.node pA.1 pX.1 p1.1 p2.1, st2)

lemma bue_cm {V : Type} [DecidableEq V] {n : ℕ}
   (S : Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) :
   ∀ (t : BTree (Fin n)) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bue S kL xLit tL fL t st).2.2
 | .leaf _, _, _, hC => hC
 | .node l r, st, C, hC => by
   simp only [bue, exr, edg, ea, ei2, ei3, addCl, List.mem_cons]
   have h1 := bue_cm S kL xLit tL fL l st C hC
   have h2 := bue_cm S kL xLit tL fL r
     (bue S kL xLit tL fL l st).2 C h1
   exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))))

lemma bue_pr {V : Type} [DecidableEq V] {n : ℕ}
   (S : Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) :
   ∀ (t : BTree (Fin n)) (st : St V),
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     let res := bue S kL xLit tL fL t st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + 2 * t.intNodes ∧
     res.2.2.length ≤ st.2.length + 7 * t.intNodes ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     UTV res.2.1 res.1 ∧
     res.1.leaves = t.leaves ∧
     res.1.depth = t.depth ∧
     res.1.intNodes = t.intNodes
 | .leaf i, st, hst, hT, hF, hkx => by
   simp only [bue, BTree.intNodes, BTree.leaves, BTree.depth]
   refine ⟨hst, le_rfl, by omega, by omega, fun _ h => h, ?_, rfl, rfl, rfl⟩
   split_ifs
   · exact hkx i
   · exact ⟨hT, hF⟩
 | .node l r, st, hst, hT, hF, hkx => by
   obtain ⟨hst1, hle1, hm1, hl1, hsub1, huv1, hlv1, hdp1, hin1⟩ :=
     bue_pr S kL xLit tL fL l st hst hT hF hkx
   set p1 := bue S kL xLit tL fL l st
   obtain ⟨hst2, hle2, hm2, hl2, hsub2, huv2, hlv2, hdp2, hin2⟩ :=
     bue_pr S kL xLit tL fL r p1.2 hst1
       (hT.mono hle1) (hF.mono hle1) (fun i => ⟨(hkx i).1.mono hle1, (hkx i).2.mono hle1⟩)
   set p2 := bue S kL xLit tL fL r p1.2
   set pA := fv p2.2
   set pX := fv pA.2
   set st1 := ea p1.1.upA p2.1.upA pA.1 pX.2
   set st2 := exr p1.1.upX p2.1.upX pX.1 st1
   have hpAst : VS pA.2 := validSt_fresh hst2
   have hpXst : VS pX.2 := validSt_fresh hpAst
   have hpX_1 : pX.2.1 = p2.2.1 + 2 := rfl
   have hpA_v : VL pX.2.1 pA.1 := (validLit_fresh p2.2).mono (by rw [hpX_1]; exact Nat.le_succ _)
   have hpX_v : VL pX.2.1 pX.1 := by change VL (pA.2.1 + 1) pX.1; exact validLit_fresh pA.2
   have hr1 := (huv1.mono hle2).root
   have hr2 := huv2.root
   have hst1_1 : st1.1 = p2.2.1 + 2 := rfl
   have hst2_1 : st2.1 = p2.2.1 + 2 := rfl
   have hst1v : VS st1 := validSt_emitAnd hpXst
     (hr1.1.mono (by omega)) (hr2.1.mono (by omega)) hpA_v
   have hst2v : VS st2 := validSt_emitXor hst1v
     (hr1.2.mono (by rw [hst1_1]; omega)) (hr2.2.mono (by rw [hst1_1]; omega)) (hpX_v.mono (by rw [hst1_1]; omega))
   refine ⟨hst2v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
   · simp only [bue]; change st.1 ≤ st2.1; rw [hst2_1]; exact le_trans hle1 (by omega)
   · simp only [bue, BTree.intNodes]; change st2.1 ≤ _; rw [hst2_1]; omega
   · simp only [bue, BTree.intNodes, exr, edg, ea, ei2, ei3, addCl,
       List.length_cons]
     change p2.2.2.length + 7 ≤ _; omega
   · intro C hC
     exact bue_cm S kL xLit tL fL (.node l r) st C hC
   · refine ⟨hpA_v.mono (by change pX.2.1 ≤ st2.1; rw [hst2_1, hpX_1]),
       hpX_v.mono (by change pX.2.1 ≤ st2.1; rw [hst2_1, hpX_1]),
       (huv1.mono (by change p1.2.1 ≤ st2.1; rw [hst2_1]; omega)),
       (huv2.mono (by change p2.2.1 ≤ st2.1; rw [hst2_1]; omega))⟩
   · simp only [bue, UET.leaves, BTree.leaves]; change p1.1.leaves ++ p2.1.leaves = _; rw [hlv1, hlv2]
   · simp only [bue, UET.depth, BTree.depth]; change max p1.1.depth p2.1.depth + 1 = _; rw [hdp1, hdp2]
   · simp only [bue, UET.intNodes, BTree.intNodes]; change 1 + p1.1.intNodes + p2.1.intNodes = _; rw [hin1, hin2]

lemma bue_leaves_depth {V : Type} [DecidableEq V] {n : ℕ}
   (S : Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) :
   ∀ (t : BTree (Fin n)) (st : St V),
     (bue S kL xLit tL fL t st).1.leaves = t.leaves ∧
     (bue S kL xLit tL fL t st).1.depth = t.depth
 | .leaf _, _ => ⟨rfl, rfl⟩
 | .node l r, st => by
   have h1 := bue_leaves_depth S kL xLit tL fL l st
   have h2 := bue_leaves_depth S kL xLit tL fL r
     (bue S kL xLit tL fL l st).2
   simp [bue, UET.leaves, UET.depth, BTree.leaves, BTree.depth, h1.1, h1.2, h2.1, h2.2]

lemma bue_sat {V : Type} [DecidableEq V] {n : ℕ}
   (S : Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) :
   ∀ (t : BTree (Fin n)) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α tL = true → lEv α fL = false →
     (∀ i, lEv α (kL i) = true) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bue S kL xLit tL fL t st).2.2, ClauseSat α' C) ∧
       UpSat α' S (fun i => lEv α (xLit i)) (bue S kL xLit tL fL t st).1
 | .leaf i, st, α, _, _, _, _, hsat, hT, hF, hK => by
   refine ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, ?_⟩
   simp only [bue, UpSat]
   split_ifs with hSi
   · exact ⟨hK i, by simp [hSi]⟩
   · exact ⟨hT, by simp [hSi, hF]⟩
 | .node l r, st, α, hst, hT, hF, hkx, hsat, hTv, hFv, hKv => by
   obtain ⟨hst1, hle1, _, _, _, huv1, _, _, _⟩ :=
     bue_pr S kL xLit tL fL l st hst hT hF hkx
   obtain ⟨α1, h1inl, h1lt, h1sat, h1up⟩ :=
     bue_sat S kL xLit tL fL l st α hst hT hF hkx hsat hTv hFv hKv
   set p1 := bue S kL xLit tL fL l st
   have hT1 := hT.mono hle1
   have hF1 := hF.mono hle1
   have hkx1 : ∀ i, VL p1.2.1 (kL i) ∧ VL p1.2.1 (xLit i) :=
     fun i => ⟨(hkx i).1.mono hle1, (hkx i).2.mono hle1⟩
   have hTv1 : lEv α1 tL = true := (lecl h1inl h1lt hT).trans hTv
   have hFv1 : lEv α1 fL = false := (lecl h1inl h1lt hF).trans hFv
   have hKv1 : ∀ i, lEv α1 (kL i) = true :=
     fun i => (lecl h1inl h1lt (hkx i).1).trans (hKv i)
   have hxv1 : (fun i => lEv α1 (xLit i)) = (fun i => lEv α (xLit i)) := by
     ext i; exact lecl h1inl h1lt (hkx i).2
   obtain ⟨hst2, hle2, _, _, _, huv2, _, _, _⟩ :=
     bue_pr S kL xLit tL fL r p1.2 hst1 hT1 hF1 hkx1
   obtain ⟨α2, h2inl, h2lt, h2sat, h2up⟩ :=
     bue_sat S kL xLit tL fL r p1.2 α1 hst1 hT1 hF1 hkx1 h1sat hTv1 hFv1 hKv1
   rw [hxv1] at h2up
   set p2 := bue S kL xLit tL fL r p1.2
   let x : Fin n → Bool := fun i => lEv α (xLit i)
   have h1up2 : UpSat α2 S x p1.1 :=
     UpSat.congr_lt (fun v => (h2inl v).symm) (fun k hk => (h2lt k hk).symm) S x huv1 h1up
   let valX := xl (p1.1.leaves.map (fun i => if S i then x i else false)) ^^
               xl (p2.1.leaves.map (fun i => if S i then x i else false))
   let α3 : Sum V ℕ → Bool := fun w =>
     match w with
     | Sum.inl v => α2 (Sum.inl v)
     | Sum.inr k => if k = p2.2.1 then true else if k = p2.2.1 + 1 then valX else α2 (Sum.inr k)
   have hα3_lt : ∀ k < p2.2.1, α3 (Sum.inr k) = α2 (Sum.inr k) := by
     intro k hk
     simp [α3, show k ≠ p2.2.1 by omega, show k ≠ p2.2.1 + 1 by omega]
   have hα3_inl : ∀ v, α3 (Sum.inl v) = α2 (Sum.inl v) := fun _ => rfl
   have h1up3 : UpSat α3 S x p1.1 :=
     UpSat.congr_lt (fun v => (hα3_inl v).symm) (fun k hk => (hα3_lt k hk).symm) S x (huv1.mono hle2) h1up2
   have h2up3 : UpSat α3 S x p2.1 :=
     UpSat.congr_lt (fun v => (hα3_inl v).symm) (fun k hk => (hα3_lt k hk).symm) S x huv2 h2up
   have hsat2 : ∀ C ∈ p2.2.2, ClauseSat α3 C := fun C hC =>
     (cscl hα3_inl hα3_lt (hst2 C hC).2).2 (h2sat C hC)
   have hA1 : lEv α3 p1.1.upA = true := h1up3.root.1
   have hA2 : lEv α3 p2.1.upA = true := h2up3.root.1
   have hX1 : lEv α3 p1.1.upX = xl (p1.1.leaves.map (fun i => if S i then x i else false)) :=
     h1up3.root.2
   have hX2 : lEv α3 p2.1.upX = xl (p2.1.leaves.map (fun i => if S i then x i else false)) :=
     h2up3.root.2
   have hpA_val : lEv α3 (fv p2.2).1 = true := by simp [fv, lEv, α3]
   have hpX_val : lEv α3 (fv (fv p2.2).2).1 = valX := by
     have hp1 : (fv p2.2).2.1 = p2.2.1 + 1 := rfl
     have hne : ¬ (p2.2.1 + 1 = p2.2.1) := by omega
     simp [fv, lEv, α3, hp1, hne]
   have hsat_final : ∀ C ∈ (bue S kL xLit tL fL (.node l r) st).2.2,
       ClauseSat α3 C := by
     change ∀ C ∈ (exr p1.1.upX p2.1.upX _ (ea p1.1.upA p2.1.upA _ _)).2, ClauseSat α3 C
     rw [emitXor_sat_iff, emitAnd_sat_iff]
     refine ⟨?_, ?_, hsat2⟩
     · rw [hpX_val, hX1, hX2]
     · rw [hpA_val, hA1, hA2]; rfl
   refine ⟨α3, fun v => (h2inl v).trans (h1inl v), fun k hk => ?_, hsat_final, ?_⟩
   · exact (hα3_lt k (by omega)).trans ((h2lt k (by omega)).trans (h1lt k hk))
   · simp only [bue, UpSat, UET.leaves, List.map_append, xorList_append]
     exact ⟨hpA_val, hpX_val, h1up3, h2up3⟩

lemma bue_up {V : Type} [DecidableEq V] {n : ℕ}
   (F : Finset (CN V)) (seed : Set (LN V))
   (S x : Fin n → Bool) (i : Fin n)
   (kL xLit : Fin n → LN V) (tL fL : LN V) :
   ∀ (t : BTree (Fin n)) (st : St V),
     (∀ C ∈ (bue S kL xLit tL fL t st).2.2, C ∈ F) →
     tL ∈ (upS F)^[1] seed →
     negL fL ∈ (upS F)^[1] seed →
     (∀ j, j ≠ i → S j = true →
       kL j ∈ (upS F)^[1] seed ∧ fLt (xLit j) (x j) ∈ (upS F)^[1] seed) →
     UpReady F seed S x i (bue S kL xLit tL fL t st).1
 | .leaf j, st, _, hT, hF, hkx => by
   simp only [bue, UpReady]
   intro hne
   split_ifs with hSj
   · have h := hkx j hne hSj
     simpa [hSj] using h
   · simpa [hSj, fLt] using And.intro hT hF
 | .node l r, st, hF_all, hT, hF, hkx => by
   set p1 := bue S kL xLit tL fL l st
   set p2 := bue S kL xLit tL fL r p1.2
   have hFr : ∀ C ∈ p2.2.2, C ∈ F := fun C hC => by
     apply hF_all
     simp only [bue, exr, edg, ea, ei2, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hC))))))
   have hFl : ∀ C ∈ p1.2.2, C ∈ F :=
     fun C hC => hFr C (bue_cm S kL xLit tL fL r p1.2 C hC)
   have hRl := bue_up F seed S x i kL xLit tL fL l st hFl hT hF hkx
   have hRr := bue_up F seed S x i kL xLit tL fL r p1.2 hFr hT hF hkx
   simp only [bue, UpReady]
   refine ⟨hRl, hRr, fun hni => ?_⟩
   have hnil : i ∉ p1.1.leaves := fun hi => hni (List.mem_append_left _ hi)
   have hnir : i ∉ p2.1.leaves := fun hi => hni (List.mem_append_right _ hi)
   obtain ⟨hlA, hlX⟩ := hRl.root hnil
   obtain ⟨hrA, hrX⟩ := hRr.root hnir
   have hleL : p1.1.depth + 1 ≤ max p1.1.depth p2.1.depth + 1 :=
     Nat.add_le_add_right (le_max_left _ _) 1
   have hleR : p2.1.depth + 1 ≤ max p1.1.depth p2.1.depth + 1 :=
     Nat.add_le_add_right (le_max_right _ _) 1
   have hlA' := upStep_iter_le F seed hleL hlA
   have hrA' := upStep_iter_le F seed hleR hrA
   have hlX' := upStep_iter_le F seed hleL hlX
   have hrX' := upStep_iter_le F seed hleR hrX
   have hF_and : ∀ C ∈ (ea p1.1.upA p2.1.upA (fv p2.2).1 (fv (fv p2.2).2).2).2, C ∈ F := by
     intro C hC
     apply hF_all
     simp only [bue, exr, edg, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
   have hF_xor : ∀ C ∈ (exr p1.1.upX p2.1.upX (fv (fv p2.2).2).1
       (ea p1.1.upA p2.1.upA (fv p2.2).1 (fv (fv p2.2).2).2)).2, C ∈ F := by
     intro C hC
     exact hF_all C hC
   have hdepth : (UET.node (fv p2.2).1 (fv (fv p2.2).2).1 p1.1 p2.1).depth + 1 =
       (max p1.1.depth p2.1.depth + 1) + 1 := rfl
   rw [hdepth, Function.iterate_succ_apply']
   refine ⟨emitAnd_up hF_and hlA' hrA', ?_⟩
   simp only [UET.leaves, List.map_append, xorList_append]
   exact emitXor_up hF_xor hlX' hrX'

lemma list_filter_ne_append_left {α : Type} [DecidableEq α] {L1 L2 : List α} {i : α}
   (hnd : (L1 ++ L2).Nodup) (hi : i ∈ L1) :
   (L1 ++ L2).filter (· ≠ i) = L1.filter (· ≠ i) ++ L2 := by
 have hdisj := List.disjoint_of_nodup_append hnd
 have hni : i ∉ L2 := hdisj hi
 have hL2 : L2.filter (· ≠ i) = L2 :=
   List.filter_eq_self.2 (fun x hx => decide_eq_true (by rintro rfl; exact hni hx))
 rw [List.filter_append, hL2]

lemma list_filter_ne_append_right {α : Type} [DecidableEq α] {L1 L2 : List α} {i : α}
   (hnd : (L1 ++ L2).Nodup) (hi : i ∈ L2) :
   (L1 ++ L2).filter (· ≠ i) = L1 ++ L2.filter (· ≠ i) := by
 have hdisj := List.disjoint_of_nodup_append hnd
 have hni : i ∉ L1 := fun hi1 => hdisj hi1 hi
 have hL1 : L1.filter (· ≠ i) = L1 :=
   List.filter_eq_self.2 (fun x hx => decide_eq_true (by rintro rfl; exact hni hx))
 rw [List.filter_append, hL1]

def bde {V : Type} [DecidableEq V] {n : ℕ} :
   UET V (Fin n) → LN V × LN V → St V →
   (Fin n → LN V × LN V) × St V
 | .leaf _ _ _, p, st => (fun _ => p, st)
 | .node _ _ l r, p, st =>
   let lA := fv st
   let lX := fv lA.2
   let st1 := ea p.1 r.upA lA.1 lX.2
   let st2 := exr p.2 r.upX lX.1 st1
   let rA := fv st2
   let rX := fv rA.2
   let st3 := ea p.1 l.upA rA.1 rX.2
   let st4 := exr p.2 l.upX rX.1 st3
   let resL := bde l (lA.1, lX.1) st4
   let resR := bde r (rA.1, rX.1) resL.2
   (fun j => if j ∈ l.leaves then resL.1 j else resR.1 j, resR.2)

lemma bde_cm {V : Type} [DecidableEq V] {n : ℕ} :
   ∀ (u : UET V (Fin n)) (p : LN V × LN V) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bde u p st).2.2
 | .leaf _ _ _, _, _, _, hC => hC
 | .node _ _ l r, p, st, C, hC => by
   simp only [bde]
   apply bde_cm r
   apply bde_cm l
   set lA := fv st
   set lX := fv lA.2
   set st1 := ea p.1 r.upA lA.1 lX.2
   set st2 := exr p.2 r.upX lX.1 st1
   set rA := fv st2
   set rX := fv rA.2
   set st3 := ea p.1 l.upA rA.1 rX.2
   have h1 : C ∈ st1.2 := by simp [st1, ea, ei2, ei3, addCl, lX, lA, fv, hC]
   have h2 : C ∈ st2.2 := by simp [st2, exr, edg, ei3, addCl, h1]
   have h3 : C ∈ st3.2 := by simp [st3, ea, ei2, ei3, addCl, rX, rA, fv, h2]
   simp [exr, edg, ei3, addCl, h3]

lemma bde_pr {V : Type} [DecidableEq V] {n : ℕ} :
   ∀ (u : UET V (Fin n)) (p : LN V × LN V) (st : St V),
     VS st →
     UTV st.1 u →
     VL st.1 p.1 → VL st.1 p.2 →
     let res := bde u p st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + 4 * u.intNodes ∧
     res.2.2.length ≤ st.2.length + 14 * u.intNodes ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ j, VL res.2.1 (res.1 j).1 ∧ VL res.2.1 (res.1 j).2)
 | .leaf _ _ _, p, st, hst, _, hp1, hp2 =>
   ⟨hst, le_rfl, by simp [bde, UET.intNodes],
   by simp [bde, UET.intNodes], fun _ h => h, fun _ => ⟨hp1, hp2⟩⟩
 | .node upA upX l r, p, st, hst, ⟨_, _, hul, hur⟩, hp1, hp2 => by
   set lA := fv st
   set lX := fv lA.2
   set st1 := ea p.1 r.upA lA.1 lX.2
   set st2 := exr p.2 r.upX lX.1 st1
   set rA := fv st2
   set rX := fv rA.2
   set st3 := ea p.1 l.upA rA.1 rX.2
   set st4 := exr p.2 l.upX rX.1 st3
   have hlAst : VS lA.2 := validSt_fresh hst
   have hlXst : VS lX.2 := validSt_fresh hlAst
   have hlX_1 : lX.2.1 = st.1 + 2 := rfl
   have hlA_v2 : VL lX.2.1 lA.1 := (validLit_fresh st).mono (by rw [hlX_1]; omega)
   have hlX_v2 : VL lX.2.1 lX.1 := by change VL (lA.2.1 + 1) lX.1; exact validLit_fresh lA.2
   have hst1_1 : st1.1 = st.1 + 2 := rfl
   have hst2_1 : st2.1 = st.1 + 2 := rfl
   have hst1v : VS st1 := validSt_emitAnd hlXst (hp1.mono (by rw [hlX_1]; omega))
     (hur.root.1.mono (by rw [hlX_1]; omega)) hlA_v2
   have hst2v : VS st2 := validSt_emitXor hst1v (hp2.mono (by rw [hst1_1]; omega))
     (hur.root.2.mono (by rw [hst1_1]; omega)) (hlX_v2.mono (by rw [hst1_1, hlX_1]))
   have hrAst : VS rA.2 := validSt_fresh hst2v
   have hrXst : VS rX.2 := validSt_fresh hrAst
   have hrX_1 : rX.2.1 = st.1 + 4 := rfl
   have hst3_1 : st3.1 = st.1 + 4 := rfl
   have hst4_1 : st4.1 = st.1 + 4 := rfl
   have hlA_v : VL st4.1 lA.1 := hlA_v2.mono (by rw [hst4_1, hlX_1]; omega)
   have hlX_v : VL st4.1 lX.1 := hlX_v2.mono (by rw [hst4_1, hlX_1]; omega)
   have hrA_v : VL st4.1 rA.1 := by
     have h1 : st2.1 + 1 ≤ st4.1 := by rw [hst2_1, hst4_1]; omega
     exact (validLit_fresh st2).mono h1
   have hrX_v : VL st4.1 rX.1 := by
     change VL (rA.2.1 + 1) rX.1; exact validLit_fresh rA.2
   have hst4 : VS st4 :=
     validSt_emitXor (validSt_emitAnd hrXst (hp1.mono (by rw [hrX_1]; omega))
       (hul.root.1.mono (by rw [hrX_1]; omega)) (hrA_v.mono (by rw [hrX_1, hst4_1])))
       (hp2.mono (by rw [hst3_1]; omega)) (hul.root.2.mono (by rw [hst3_1]; omega))
       (hrX_v.mono (by rw [hst3_1, hst4_1]))
   obtain ⟨hstL, hleL, hmL, hlL, hsubL, hwL⟩ :=
     bde_pr l (lA.1, lX.1) st4 hst4 (hul.mono (by omega)) hlA_v hlX_v
   set resL := bde l (lA.1, lX.1) st4
   obtain ⟨hstR, hleR, hmR, hlR, hsubR, hwR⟩ :=
     bde_pr r (rA.1, rX.1) resL.2 hstL (hur.mono (by omega))
       (hrA_v.mono hleL) (hrX_v.mono hleL)
   set resR := bde r (rA.1, rX.1) resL.2
   have hlen4 : st4.2.length = st.2.length + 14 := by
     simp [st4, st3, st2, st1, exr, edg, ea, ei2, ei3, addCl, lX, lA, rX, rA, fv]
   refine ⟨hstR, ?_, ?_, ?_, ?_, ?_⟩
   · simp only [bde]; change st.1 ≤ resR.2.1; omega
   · simp only [bde, UET.intNodes]; change resR.2.1 ≤ _; omega
   · simp only [bde, UET.intNodes]; change resR.2.2.length ≤ _; omega
   · intro C hC
     exact bde_cm (.node upA upX l r) p st C hC
   · intro j
     dsimp only [bde]
     split_ifs
     · exact ⟨(hwL j).1.mono hleR, (hwL j).2.mono hleR⟩
     · exact hwR j

lemma bde_sat {V : Type} [DecidableEq V] {n : ℕ} (S x : Fin n → Bool) :
   ∀ (u : UET V (Fin n)) (p : LN V × LN V) (st : St V)
     (α : Sum V ℕ → Bool) (prefVal : Bool),
     VS st →
     UTV st.1 u →
     VL st.1 p.1 → VL st.1 p.2 →
     u.leaves.Nodup →
     UpSat α S x u →
     lEv α p.1 = true → lEv α p.2 = prefVal →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bde u p st).2.2, ClauseSat α' C) ∧
       ∀ j ∈ u.leaves,
         lEv α' ((bde u p st).1 j).1 = true ∧
         lEv α' ((bde u p st).1 j).2 =
           (prefVal ^^ xl ((u.leaves.filter (· ≠ j)).map (fun q => if S q then x q else false)))
 | .leaf i _ _, p, st, α, prefVal, _, _, _, _, _, _, hp1, hp2, hsat => by
   refine ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun j hj => ?_⟩
   simp only [UET.leaves, List.mem_singleton] at hj
   subst hj
   simpa [bde, UET.leaves, xl] using And.intro hp1 hp2
 | .node _ _ l r, p, st, α, prefVal, hst, ⟨_, _, hul, hur⟩, hp1, hp2, hnd,
     ⟨_, _, hsatL, hsatR⟩, hpv1, hpv2, hsat => by
   have hndl : l.leaves.Nodup := (List.nodup_append.1 hnd).1
   have hndr : r.leaves.Nodup := (List.nodup_append.1 hnd).2.1
   let valL := xl (l.leaves.map (fun q => if S q then x q else false))
   let valR := xl (r.leaves.map (fun q => if S q then x q else false))
   let lA := fv st
   let lX := fv lA.2
   let st1 := ea p.1 r.upA lA.1 lX.2
   let st2 := exr p.2 r.upX lX.1 st1
   let rA := fv st2
   let rX := fv rA.2
   let st3 := ea p.1 l.upA rA.1 rX.2
   let st4 := exr p.2 l.upX rX.1 st3
   let α1 : Sum V ℕ → Bool := fun w =>
     match w with
     | Sum.inl v => α (Sum.inl v)
     | Sum.inr k =>
       if k = st.1 then true
       else if k = st.1 + 1 then (prefVal ^^ valR)
       else if k = st.1 + 2 then true
       else if k = st.1 + 3 then (prefVal ^^ valL)
       else α (Sum.inr k)
   have hα1_lt : ∀ k < st.1, α1 (Sum.inr k) = α (Sum.inr k) := by
     intro k hk
     simp [α1, show k ≠ st.1 by omega, show k ≠ st.1 + 1 by omega,
       show k ≠ st.1 + 2 by omega, show k ≠ st.1 + 3 by omega]
   have hα1_inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
   have hsat_st : ∀ C ∈ st.2, ClauseSat α1 C := fun C hC =>
     (cscl hα1_inl hα1_lt (hst C hC).2).2 (hsat C hC)
   have hsl1 : UpSat α1 S x l :=
     UpSat.congr_lt (fun v => (hα1_inl v).symm) (fun k hk => (hα1_lt k hk).symm) S x hul hsatL
   have hsr1 : UpSat α1 S x r :=
     UpSat.congr_lt (fun v => (hα1_inl v).symm) (fun k hk => (hα1_lt k hk).symm) S x hur hsatR
   have hAl : lEv α1 l.upA = true := hsl1.root.1
   have hAr : lEv α1 r.upA = true := hsr1.root.1
   have hXl : lEv α1 l.upX = valL := hsl1.root.2
   have hXr : lEv α1 r.upX = valR := hsr1.root.2
   have hpv1' : lEv α1 p.1 = true := (lecl hα1_inl hα1_lt hp1).trans hpv1
   have hpv2' : lEv α1 p.2 = prefVal := (lecl hα1_inl hα1_lt hp2).trans hpv2
   have hlAv : lEv α1 lA.1 = true := by simp [lA, fv, lEv, α1]
   have hlXv : lEv α1 lX.1 = (prefVal ^^ valR) := by
     simp [lX, lA, fv, lEv, α1, show st.1 + 1 ≠ st.1 by omega]
   have hrAv : lEv α1 rA.1 = true := by
     have hrA1 : rA.1 = (Sum.inr (st.1 + 2), true) := rfl
     rw [hrA1]
     simp [lEv, α1, show st.1 + 2 ≠ st.1 by omega, show st.1 + 2 ≠ st.1 + 1 by omega]
   have hrXv : lEv α1 rX.1 = (prefVal ^^ valL) := by
     have hrX1 : rX.1 = (Sum.inr (st.1 + 3), true) := rfl
     rw [hrX1]
     simp [lEv, α1, show st.1 + 3 ≠ st.1 by omega, show st.1 + 3 ≠ st.1 + 1 by omega,
       show st.1 + 3 ≠ st.1 + 2 by omega]
   have hsat_st1 : ∀ C ∈ st1.2, ClauseSat α1 C := by
     dsimp only [st1]
     rw [emitAnd_sat_iff]
     exact ⟨by rw [hlAv, hpv1', hAr]; rfl, hsat_st⟩
   have hsat_st2 : ∀ C ∈ st2.2, ClauseSat α1 C := by
     dsimp only [st2]
     rw [emitXor_sat_iff]
     exact ⟨by rw [hlXv, hpv2', hXr], hsat_st1⟩
   have hsat_st3 : ∀ C ∈ st3.2, ClauseSat α1 C := by
     dsimp only [st3]
     rw [emitAnd_sat_iff]
     exact ⟨by rw [hrAv, hpv1', hAl]; rfl, hsat_st2⟩
   have hsat_st4 : ∀ C ∈ st4.2, ClauseSat α1 C := by
     dsimp only [st4]
     rw [emitXor_sat_iff]
     exact ⟨by rw [hrXv, hpv2', hXl], hsat_st3⟩
   have hst4_1 : st4.1 = st.1 + 4 := rfl
   have hul4 : UTV st4.1 l := hul.mono (by omega)
   have hur4 : UTV st4.1 r := hur.mono (by omega)
   have hlAv_lit2 : VL (st.1 + 2) lA.1 := (validLit_fresh st).mono (by omega)
   have hlXv_lit2 : VL (st.1 + 2) lX.1 := by
     change VL (lA.2.1 + 1) lX.1; exact validLit_fresh lA.2
   have hlAv_lit : VL st4.1 lA.1 := hlAv_lit2.mono (by omega)
   have hlXv_lit : VL st4.1 lX.1 := hlXv_lit2.mono (by omega)
   have hrAv_lit : VL st4.1 rA.1 := by
     have h1 : st2.1 + 1 ≤ st4.1 := by change (st.1 + 2) + 1 ≤ st.1 + 4; omega
     exact (validLit_fresh st2).mono h1
   have hrXv_lit : VL st4.1 rX.1 := by
     change VL (rA.2.1 + 1) rX.1; exact validLit_fresh rA.2
   have hst4_v : VS st4 := by
     have hlAst : VS lA.2 := validSt_fresh hst
     have hlXst : VS lX.2 := validSt_fresh hlAst
     have hlX_1 : lX.2.1 = st.1 + 2 := rfl
     have hst1_1 : st1.1 = st.1 + 2 := rfl
     have hrAst : VS rA.2 := by
       have hst1v : VS st1 := validSt_emitAnd hlXst (hp1.mono (by rw [hlX_1]; omega))
         (hur.root.1.mono (by rw [hlX_1]; omega)) (hlAv_lit2.mono (by rw [hlX_1]))
       have hst2v : VS st2 := validSt_emitXor hst1v (hp2.mono (by rw [hst1_1]; omega))
         (hur.root.2.mono (by rw [hst1_1]; omega)) (hlXv_lit2.mono (by rw [hst1_1]))
       exact validSt_fresh hst2v
     have hrXst : VS rX.2 := validSt_fresh hrAst
     have hrX_1 : rX.2.1 = st.1 + 4 := rfl
     have hst3_1 : st3.1 = st.1 + 4 := rfl
     exact validSt_emitXor (validSt_emitAnd hrXst (hp1.mono (by rw [hrX_1]; omega))
       (hul.root.1.mono (by rw [hrX_1]; omega)) (hrAv_lit.mono (by rw [hrX_1, hst4_1])))
       (hp2.mono (by rw [hst3_1]; omega)) (hul.root.2.mono (by rw [hst3_1]; omega))
       (hrXv_lit.mono (by rw [hst3_1, hst4_1]))
   obtain ⟨α2, h2inl, h2lt, h2sat, h2resL⟩ :=
     bde_sat S x l (lA.1, lX.1) st4 α1 (prefVal ^^ valR) hst4_v hul4 hlAv_lit hlXv_lit
       hndl hsl1 hlAv hlXv hsat_st4
   set resL := bde l (lA.1, lX.1) st4
   obtain ⟨hstL, hleL, _, _, _, hwL⟩ := bde_pr l (lA.1, lX.1) st4 hst4_v hul4 hlAv_lit hlXv_lit
   have hurL : UTV resL.2.1 r := hur4.mono hleL
   have hrAv_L : VL resL.2.1 rA.1 := hrAv_lit.mono hleL
   have hrXv_L : VL resL.2.1 rX.1 := hrXv_lit.mono hleL
   have hrAv2 : lEv α2 rA.1 = true := (lecl h2inl h2lt hrAv_lit).trans hrAv
   have hrXv2 : lEv α2 rX.1 = (prefVal ^^ valL) := (lecl h2inl h2lt hrXv_lit).trans hrXv
   obtain ⟨α3, h3inl, h3lt, h3sat, h3resR⟩ :=
     bde_sat S x r (rA.1, rX.1) resL.2 α2 (prefVal ^^ valL) hstL hurL hrAv_L hrXv_L
       hndr (UpSat.congr_lt (fun v => (h2inl v).symm) (fun k hk => (h2lt k hk).symm) S x hur4 hsr1)
       hrAv2 hrXv2 h2sat
   refine ⟨α3, fun v => (h3inl v).trans ((h2inl v).trans (hα1_inl v)), fun k hk => ?_, h3sat, ?_⟩
   · have hk4 : k < st4.1 := by rw [hst4_1]; omega
     exact (h3lt k (lt_of_lt_of_le hk4 hleL)).trans ((h2lt k hk4).trans (hα1_lt k hk))
   · intro j hj
     simp only [UET.leaves, List.mem_append] at hj
     simp only [bde]
     rcases hj with hjL | hjR
     · simp only [hjL, ↓reduceIte]
       change lEv α3 (resL.1 j).1 = true ∧ lEv α3 (resL.1 j).2 =
         (prefVal ^^ xl ((l.leaves ++ r.leaves).filter (· ≠ j) |>.map (fun q => if S q then x q else false)))
       have heq1 : lEv α3 (resL.1 j).1 = lEv α2 (resL.1 j).1 :=
         lecl h3inl h3lt (hwL j).1
       have heq2 : lEv α3 (resL.1 j).2 = lEv α2 (resL.1 j).2 :=
         lecl h3inl h3lt (hwL j).2
       have h2j := h2resL j hjL
       dsimp only [resL] at heq1 heq2
       rw [heq1, heq2, h2j.1, h2j.2]
       rw [list_filter_ne_append_left hnd hjL, List.map_append, xorList_append]
       refine ⟨rfl, ?_⟩
       rw [Bool.xor_assoc]
       congr 1
       exact Bool.xor_comm _ _
     · have hjLn : ¬ (j ∈ l.leaves) := fun hj1 => (List.disjoint_of_nodup_append hnd) hj1 hjR
       simp only [hjLn, ↓reduceIte]
       change lEv α3 ((bde r (rA.1, rX.1) resL.2).1 j).1 = true ∧
         lEv α3 ((bde r (rA.1, rX.1) resL.2).1 j).2 =
         (prefVal ^^ xl ((l.leaves ++ r.leaves).filter (· ≠ j) |>.map (fun q => if S q then x q else false)))
       rw [(h3resR j hjR).1, (h3resR j hjR).2]
       rw [list_filter_ne_append_right hnd hjR, List.map_append, xorList_append]
       refine ⟨rfl, ?_⟩
       rw [Bool.xor_assoc]

lemma bde_up {V : Type} [DecidableEq V] {n : ℕ}
   (F : Finset (CN V)) (seed : Set (LN V))
   (S x : Fin n → Bool) (i : Fin n) (Dmax : ℕ) :
   ∀ (u : UET V (Fin n)) (p : LN V × LN V) (st : St V)
     (d : ℕ) (prefVal : Bool),
     (∀ C ∈ (bde u p st).2.2, C ∈ F) →
     UpReady F seed S x i u →
     i ∈ u.leaves →
     u.leaves.Nodup →
     u.depth ≤ Dmax →
     p.1 ∈ (upS F)^[Dmax + 1 + d] seed →
     fLt p.2 prefVal ∈ (upS F)^[Dmax + 1 + d] seed →
     ((bde u p st).1 i).1 ∈ (upS F)^[Dmax + 1 + d + u.depth] seed ∧
     fLt ((bde u p st).1 i).2
       (prefVal ^^ xl ((u.leaves.filter (· ≠ i)).map (fun q => if S q then x q else false))) ∈
       (upS F)^[Dmax + 1 + d + u.depth] seed
 | .leaf j _ _, p, st, d, prefVal, _, _, hi, _, _, hp1, hp2 => by
   simp only [UET.leaves, List.mem_singleton] at hi
   subst hi
   simpa [bde, UET.depth, UET.leaves, xl] using And.intro hp1 hp2
 | .node upA upX l r, p, st, d, prefVal, hF_all, ⟨hRl, hRr, _⟩, hi, hnd, hdep, hp1, hp2 => by
   set lA := fv st
   set lX := fv lA.2
   set st1 := ea p.1 r.upA lA.1 lX.2
   set st2 := exr p.2 r.upX lX.1 st1
   set rA := fv st2
   set rX := fv rA.2
   set st3 := ea p.1 l.upA rA.1 rX.2
   set st4 := exr p.2 l.upX rX.1 st3
   set resL := bde l (lA.1, lX.1) st4
   have hFr : ∀ C ∈ (bde r (rA.1, rX.1) resL.2).2.2, C ∈ F := fun C hC => hF_all C hC
   have hFl : ∀ C ∈ resL.2.2, C ∈ F := fun C hC =>
     hFr C (bde_cm r (rA.1, rX.1) resL.2 C hC)
   have hFst4 : ∀ C ∈ st4.2, C ∈ F := fun C hC =>
     hFl C (bde_cm l (lA.1, lX.1) st4 C hC)
   have hFst3 : ∀ C ∈ st3.2, C ∈ F := fun C hC => by
     apply hFst4; simp only [st4, exr, edg, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
   have hFst2 : ∀ C ∈ st2.2, C ∈ F := fun C hC => by
     apply hFst3; simp only [st3, ea, ei2, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr hC))
   have hFst1 : ∀ C ∈ st1.2, C ∈ F := fun C hC => by
     apply hFst2; simp only [st2, exr, edg, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
   have hndl : l.leaves.Nodup := (List.nodup_append.1 hnd).1
   have hndr : r.leaves.Nodup := (List.nodup_append.1 hnd).2.1
   have hdepl : l.depth ≤ Dmax := by simp [UET.depth] at hdep; omega
   have hdepr : r.depth ≤ Dmax := by simp [UET.depth] at hdep; omega
   simp only [UET.leaves, List.mem_append] at hi
   rcases hi with hiL | hiR
   · have hiRn : i ∉ r.leaves := (List.disjoint_of_nodup_append hnd) hiL
     obtain ⟨hrA, hrX⟩ := hRr.root hiRn
     have hrle : r.depth + 1 ≤ Dmax + 1 + d := by simp [UET.depth] at hdep; omega
     have hrA' := upStep_iter_le F seed hrle hrA
     have hrX' := upStep_iter_le F seed hrle hrX
     have hlA_mem : lA.1 ∈ (upS F)^[Dmax + 1 + (d + 1)] seed := by
       rw [show Dmax + 1 + (d + 1) = (Dmax + 1 + d) + 1 by omega, Function.iterate_succ_apply']
       exact emitAnd_up hFst1 hp1 hrA'
     have hlX_mem : fLt lX.1 (prefVal ^^ xl (r.leaves.map (fun q => if S q then x q else false))) ∈
         (upS F)^[Dmax + 1 + (d + 1)] seed := by
       rw [show Dmax + 1 + (d + 1) = (Dmax + 1 + d) + 1 by omega, Function.iterate_succ_apply']
       exact emitXor_up hFst2 hp2 hrX'
     obtain ⟨hL1, hL2⟩ := bde_up F seed S x i Dmax l (lA.1, lX.1) st4 (d + 1)
       (prefVal ^^ xl (r.leaves.map (fun q => if S q then x q else false)))
       hFl hRl hiL hndl hdepl hlA_mem hlX_mem
     have hdle : Dmax + 1 + (d + 1) + l.depth ≤
         Dmax + 1 + d + (UET.node upA upX l r).depth := by
       dsimp only [UET.depth]; omega
     simp only [bde, hiL, ↓reduceIte]
     refine ⟨upStep_iter_le F seed hdle hL1, ?_⟩
     dsimp only [UET.leaves]
     rw [list_filter_ne_append_left hnd hiL, List.map_append, xorList_append]
     have hL2' := upStep_iter_le F seed hdle hL2
     convert hL2' using 2
     rw [Bool.xor_assoc]
     congr 1
     exact Bool.xor_comm _ _
   · have hiLn : ¬ (i ∈ l.leaves) := fun h1 => (List.disjoint_of_nodup_append hnd) h1 hiR
     obtain ⟨hlA, hlX⟩ := hRl.root hiLn
     have hlle : l.depth + 1 ≤ Dmax + 1 + d := by simp [UET.depth] at hdep; omega
     have hlA' := upStep_iter_le F seed hlle hlA
     have hlX' := upStep_iter_le F seed hlle hlX
     have hrA_mem : rA.1 ∈ (upS F)^[Dmax + 1 + (d + 1)] seed := by
       rw [show Dmax + 1 + (d + 1) = (Dmax + 1 + d) + 1 by omega, Function.iterate_succ_apply']
       exact emitAnd_up hFst3 hp1 hlA'
     have hrX_mem : fLt rX.1 (prefVal ^^ xl (l.leaves.map (fun q => if S q then x q else false))) ∈
         (upS F)^[Dmax + 1 + (d + 1)] seed := by
       rw [show Dmax + 1 + (d + 1) = (Dmax + 1 + d) + 1 by omega, Function.iterate_succ_apply']
       exact emitXor_up hFst4 hp2 hlX'
     obtain ⟨hR1, hR2⟩ := bde_up F seed S x i Dmax r (rA.1, rX.1) resL.2 (d + 1)
       (prefVal ^^ xl (l.leaves.map (fun q => if S q then x q else false)))
       hFr hRr hiR hndr hdepr hrA_mem hrX_mem
     have hdle : Dmax + 1 + (d + 1) + r.depth ≤ Dmax + 1 + d + (UET.node upA upX l r).depth := by
       simp [UET.depth]; omega
     simp only [bde, hiLn, ↓reduceIte]
     refine ⟨upStep_iter_le F seed hdle hR1, ?_⟩
     dsimp only [UET.leaves]
     rw [list_filter_ne_append_right hnd hiR, List.map_append, xorList_append]
     have hR2' := upStep_iter_le F seed hdle hR2
     convert hR2' using 2
     rw [Bool.xor_assoc]

def setBit0 (k d : ℕ) : ℕ := if k.testBit d then k ^^^ (2 ^ d) else k

def setBit1 (k d : ℕ) : ℕ := if k.testBit d then k else k ^^^ (2 ^ d)

lemma setBit0_lt {k d h' : ℕ} (hk : k < 2 ^ h') (hd : d < h') : setBit0 k d < 2 ^ h' := by
 dsimp only [setBit0]
 split_ifs
 · exact Nat.xor_lt_two_pow hk (Nat.pow_lt_pow_right (by omega) hd)
 · exact hk

lemma setBit1_lt {k d h' : ℕ} (hk : k < 2 ^ h') (hd : d < h') : setBit1 k d < 2 ^ h' := by
 dsimp only [setBit1]
 split_ifs
 · exact hk
 · exact Nat.xor_lt_two_pow hk (Nat.pow_lt_pow_right (by omega) hd)

lemma testBit_setBit0 (k d q : ℕ) : (setBit0 k d).testBit q = if q = d then false else k.testBit q := by
 by_cases hqd : q = d
 · subst hqd
   by_cases hkd : k.testBit q <;> simp [setBit0, hkd, Nat.testBit_xor, Nat.testBit_two_pow_self]
 · by_cases hkd : k.testBit d <;> simp [setBit0, hkd, hqd, Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm hqd]

lemma testBit_setBit1 (k d q : ℕ) : (setBit1 k d).testBit q = if q = d then true else k.testBit q := by
 by_cases hqd : q = d
 · subst hqd
   by_cases hkd : k.testBit q <;> simp [setBit1, hkd, Nat.testBit_xor, Nat.testBit_two_pow_self]
 · by_cases hkd : k.testBit d <;> simp [setBit1, hkd, hqd, Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm hqd]

def bm : ℕ → ℕ → ℕ → ℕ
 | 0, c, _ => c
 | d + 1, c, s => if s.testBit d then setBit1 (bm d c s) d else setBit0 (bm d c s) d

lemma bflyMid_lt {c s h' : ℕ} (hc : c < 2 ^ h') : ∀ d ≤ h', bm d c s < 2 ^ h'
 | 0, _ => hc
 | d + 1, hd => by
   have ih := @bflyMid_lt c s h' hc d (by omega)
   dsimp only [bm]
   split_ifs
   · exact setBit1_lt ih (by omega)
   · exact setBit0_lt ih (by omega)

lemma testBit_bflyMid (c s q : ℕ) : ∀ d : ℕ,
   (bm d c s).testBit q = if q < d then s.testBit q else c.testBit q
 | 0 => by simp [bm]
 | d + 1 => by
   dsimp only [bm]
   cases hsd : s.testBit d
   · simp only [Bool.false_eq_true, ↓reduceIte, testBit_setBit0, testBit_bflyMid c s q d]
     by_cases hqd : q = d <;> by_cases hlt : q < d <;> simp [hqd, hlt, hsd] <;> try omega
   · simp only [↓reduceIte, testBit_setBit1, testBit_bflyMid c s q d]
     by_cases hqd : q = d <;> by_cases hlt : q < d <;> simp [hqd, hlt, hsd] <;> try omega

lemma bflyMid_eq {c s h' : ℕ} (hc : c < 2 ^ h') (hs : s < 2 ^ h') : bm h' c s = s := by
 apply Nat.eq_of_testBit_eq
 intro q
 rw [testBit_bflyMid]
 split_ifs with hq
 · rfl
 · have hqle : h' ≤ q := by omega
   rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hqle)),
       Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) hqle))]

lemma bflyMid_step (d c s : ℕ) :
   bm d c s = if c.testBit d then setBit1 (bm (d + 1) c s) d else setBit0 (bm (d + 1) c s) d := by
 apply Nat.eq_of_testBit_eq
 intro q
 split_ifs with hcd
 · rw [testBit_setBit1, testBit_bflyMid, testBit_bflyMid]
   by_cases hqd : q = d
   · subst hqd; simp [hcd]
   · split_ifs with h1 h2 <;> simp_all <;> omega
 · rw [testBit_setBit0, testBit_bflyMid, testBit_bflyMid]
   by_cases hqd : q = d
   · subst hqd; simp [hcd]
   · split_ifs with h1 h2 <;> simp_all <;> omega

def db : ℕ → ℕ → ℕ → Bool
 | 0, _, _ => false
 | d + 1, c, s => db d c s ^^ (c.testBit d && s.testBit d)

lemma dotBool_congr_lt {c s1 s2 : ℕ} : ∀ d : ℕ,
   (∀ q < d, s1.testBit q = s2.testBit q) → db d c s1 = db d c s2
 | 0, _ => rfl
 | d + 1, h => by
   simp only [db, dotBool_congr_lt d (fun q hq => h q (by omega)), h d (by omega)]

def AF (d c k : ℕ) : Prop := ∀ q : ℕ, d ≤ q → c.testBit q = k.testBit q

lemma agreeFrom_zero_iff (c k : ℕ) : AF 0 c k ↔ c = k := by
 constructor
 · intro h; exact Nat.eq_of_testBit_eq fun q => h q (Nat.zero_le q)
 · rintro rfl q _; rfl

lemma agreeFrom_top {h' c k : ℕ} (hc : c < 2 ^ h') (hk : k < 2 ^ h') : AF h' c k := by
 intro q hq
 rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hq)),
     Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) hq))]

lemma agreeFrom_setBit0 {d c k : ℕ} :
   AF d c (setBit0 k d) ↔ AF (d + 1) c k ∧ c.testBit d = false := by
 constructor
 · intro h
   refine ⟨fun q hq => ?_, ?_⟩
   · have h1 := h q (by omega)
     rw [testBit_setBit0, if_neg (by omega)] at h1
     exact h1
   · have h1 := h d le_rfl
     rw [testBit_setBit0, if_pos rfl] at h1
     exact h1
 · rintro ⟨h, hcd⟩ q hq
   rw [testBit_setBit0]
   split_ifs with hqd
   · subst hqd; exact hcd
   · exact h q (by omega)

lemma agreeFrom_setBit1 {d c k : ℕ} :
   AF d c (setBit1 k d) ↔ AF (d + 1) c k ∧ c.testBit d = true := by
 constructor
 · intro h
   refine ⟨fun q hq => ?_, ?_⟩
   · have h1 := h q (by omega)
     rw [testBit_setBit1, if_neg (by omega)] at h1
     exact h1
   · have h1 := h d le_rfl
     rw [testBit_setBit1, if_pos rfl] at h1
     exact h1
 · rintro ⟨h, hcd⟩ q hq
   rw [testBit_setBit1]
   split_ifs with hqd
   · subst hqd; exact hcd
   · exact h q (by omega)

def ag {V : Type} (m base : ℕ) (k : Fin m) (b : Bool) : LN V :=
 (Sum.inr (base + 2 * k.val + if b then 1 else 0), true)

lemma validLit_allocGrid (V : Type) (m base : ℕ) (k : Fin m) (b : Bool) :
   VL (base + 2 * m) (ag (V := V) m base k b) := by
 intro j hj
 simp only [ag, Sum.inr.injEq] at hj
 cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hj <;> omega

lemma litEval_allocGrid {V : Type} (α : Sum V ℕ → Bool) (m base : ℕ) (k : Fin m) (b : Bool) :
   lEv α (ag m base k b) = α (Sum.inr (base + 2 * k.val + if b then 1 else 0)) := by
 simp [ag, lEv]

def bbfi {V : Type} [DecidableEq V] (m : ℕ)
   (S : Fin m → Bool) (iso const : Fin m → LN V)
   (w0 : Fin m → Bool → LN V) : ℕ → St V → St V
 | k, st =>
   if hk : k < m then
     let kf : Fin m := ⟨k, hk⟩
     let st1 := if S kf then
       let p0 := fv st
       let p1 := fv p0.2
       ei2 p1.1 (w0 kf true)
         (ei2 p0.1 (w0 kf false)
           (ei3 (iso kf) (const kf) p1.1
             (ei3 (iso kf) (negL (const kf)) p0.1 p1.2)))
     else st
     bbfi m S iso const w0 (k + 1) st1
   else st
termination_by k => m - k

lemma bbfi_cm {V : Type} [DecidableEq V] (m : ℕ)
   (S : Fin m → Bool) (iso const : Fin m → LN V)
   (w0 : Fin m → Bool → LN V) :
   ∀ (r k : ℕ) (_ : m - k = r) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bbfi m S iso const w0 k st).2
 | 0, k, hr, st, C, hC => by
   have hge : ¬ (k < m) := by omega
   unfold bbfi
   simp only [hge, ↓reduceDIte]
   exact hC
 | r + 1, k, hr, st, C, hC => by
   have hk : k < m := by omega
   have hr1 : m - (k + 1) = r := by omega
   unfold bbfi
   simp only [hk, ↓reduceDIte]
   apply bbfi_cm m S iso const w0 r (k + 1) hr1
   split_ifs
   · simp only [ei2, ei3, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
   · exact hC

lemma bbfi_pr {V : Type} [DecidableEq V] (m : ℕ)
   (S : Fin m → Bool) (iso const : Fin m → LN V)
   (w0 : Fin m → Bool → LN V) :
   ∀ (r k : ℕ) (_ : m - k = r) (st : St V),
     VS st →
     (∀ c, VL st.1 (iso c) ∧ VL st.1 (const c) ∧
       VL st.1 (w0 c false) ∧ VL st.1 (w0 c true)) →
     let st' := bbfi m S iso const w0 k st
     VS st' ∧
     st.1 ≤ st'.1 ∧
     st'.1 ≤ st.1 + 2 * r ∧
     st'.2.length ≤ st.2.length + 4 * r ∧
     (∀ C ∈ st.2, C ∈ st'.2) ∧
     ∀ c : Fin m, k ≤ c.val → S c = true →
       ∃ a0 a1 : LN V,
         {negL (iso c), negL (negL (const c)), a0} ∈ st'.2 ∧
         {negL (iso c), negL (const c), a1} ∈ st'.2 ∧
         {negL a0, w0 c false} ∈ st'.2 ∧
         {negL a1, w0 c true} ∈ st'.2
 | 0, k, hr, st, hst, _ => by
   have hge : ¬ (k < m) := by omega
   unfold bbfi
   simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by omega, by omega, fun _ h => h, fun c hc => by exfalso; omega⟩
 | r + 1, k, hr, st, hst, hw => by
   have hk : k < m := by omega
   have hr1 : m - (k + 1) = r := by omega
   unfold bbfi
   simp only [hk, ↓reduceDIte]
   set kf : Fin m := ⟨k, hk⟩
   set st1 := if S kf then
     let p0 := fv st
     let p1 := fv p0.2
     ei2 p1.1 (w0 kf true)
       (ei2 p0.1 (w0 kf false)
         (ei3 (iso kf) (const kf) p1.1
           (ei3 (iso kf) (negL (const kf)) p0.1 p1.2)))
   else st
   have hst1_1 : st1.1 ≤ st.1 + 2 := by
     dsimp only [st1]; split_ifs <;> simp [fv, ei2, ei3, addCl]
   have hle1 : st.1 ≤ st1.1 := by
     dsimp only [st1]; split_ifs <;> simp [fv, ei2, ei3, addCl]; omega
   have hlen1 : st1.2.length ≤ st.2.length + 4 := by
     dsimp only [st1]; split_ifs <;> simp [fv, ei2, ei3, addCl]
   have hst1v : VS st1 := by
     dsimp only [st1]
     split_ifs
     · set p0 := fv st
       set p1 := fv p0.2
       have hp0 : VS p0.2 := validSt_fresh hst
       have hp1 : VS p1.2 := validSt_fresh hp0
       have hp1_1 : p1.2.1 = st.1 + 2 := rfl
       have h0v : VL (st.1 + 2) p0.1 := (validLit_fresh st).mono (by omega)
       have h1v : VL (st.1 + 2) p1.1 := by change VL (p0.2.1 + 1) p1.1; exact validLit_fresh p0.2
       have hw' := hw kf
       exact validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp3 (validSt_emitImp3 hp1
         (hw'.1.mono (by rw [hp1_1]; omega)) (validLit_negL.2 (hw'.2.1.mono (by rw [hp1_1]; omega)))
         (h0v.mono (by rw [hp1_1])))
         (hw'.1.mono (by dsimp only [ei3, addCl]; rw [hp1_1]; omega))
         (hw'.2.1.mono (by dsimp only [ei3, addCl]; rw [hp1_1]; omega))
         (h1v.mono (by dsimp only [ei3, addCl]; rw [hp1_1])))
         (h0v.mono (by dsimp only [ei3, addCl]; rw [hp1_1]))
         (hw'.2.2.1.mono (by dsimp only [ei3, addCl]; rw [hp1_1]; omega)))
         (h1v.mono (by dsimp only [ei2, ei3, addCl]; rw [hp1_1]))
         (hw'.2.2.2.mono (by dsimp only [ei2, ei3, addCl]; rw [hp1_1]; omega))
     · exact hst
   have hw1 : ∀ c, VL st1.1 (iso c) ∧ VL st1.1 (const c) ∧
       VL st1.1 (w0 c false) ∧ VL st1.1 (w0 c true) :=
     fun c => ⟨(hw c).1.mono hle1, (hw c).2.1.mono hle1, (hw c).2.2.1.mono hle1, (hw c).2.2.2.mono hle1⟩
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ := bbfi_pr m S iso const w0 r (k + 1) hr1 st1 hst1v hw1
   refine ⟨r1, le_trans hle1 r2, by omega, by omega, fun C hC => r5 C ?_, fun c hc hSc => ?_⟩
   · dsimp only [st1]; split_ifs
     · simp only [ei2, ei3, addCl, List.mem_cons]
       exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
     · exact hC
   · by_cases heq : k = c.val
     · have hceq : kf = c := Fin.ext heq
       have hS_kf : S kf = true := by rw [hceq]; exact hSc
       dsimp only [st1] at r5
       rw [if_pos hS_kf] at r5
       set p0 := fv st
       set p1 := fv p0.2
       have hc1 : ({negL (iso kf), negL (negL (const kf)), p0.1} : CN V) ∈
           (bbfi m S iso const w0 (k + 1)
             (ei2 p1.1 (w0 kf true) (ei2 p0.1 (w0 kf false)
               (ei3 (iso kf) (const kf) p1.1 (ei3 (iso kf) (negL (const kf)) p0.1 p1.2))))).2 :=
         r5 _ (by simp [ei2, ei3, addCl, p0, p1, fv])
       have hc2 : ({negL (iso kf), negL (const kf), p1.1} : CN V) ∈
           (bbfi m S iso const w0 (k + 1)
             (ei2 p1.1 (w0 kf true) (ei2 p0.1 (w0 kf false)
               (ei3 (iso kf) (const kf) p1.1 (ei3 (iso kf) (negL (const kf)) p0.1 p1.2))))).2 :=
         r5 _ (by simp [ei2, ei3, addCl, p0, p1, fv])
       have hc3 : ({negL p0.1, w0 kf false} : CN V) ∈
           (bbfi m S iso const w0 (k + 1)
             (ei2 p1.1 (w0 kf true) (ei2 p0.1 (w0 kf false)
               (ei3 (iso kf) (const kf) p1.1 (ei3 (iso kf) (negL (const kf)) p0.1 p1.2))))).2 :=
         r5 _ (by simp [ei2, ei3, addCl, p0, p1, fv])
       have hc4 : ({negL p1.1, w0 kf true} : CN V) ∈
           (bbfi m S iso const w0 (k + 1)
             (ei2 p1.1 (w0 kf true) (ei2 p0.1 (w0 kf false)
               (ei3 (iso kf) (const kf) p1.1 (ei3 (iso kf) (negL (const kf)) p0.1 p1.2))))).2 :=
         r5 _ (by simp [ei2, ei3, addCl, p0, p1, fv])
       rw [← hceq]
       dsimp only [st1]; rw [if_pos hS_kf]
       exact ⟨p0.1, p1.1, hc1, hc2, hc3, hc4⟩
     · exact r6 c (by omega) hSc

lemma bbfi_sat {V : Type} [DecidableEq V] (m : ℕ)
   (S : Fin m → Bool) (iso const : Fin m → LN V)
   (w0 : Fin m → Bool → LN V) (constVal : Fin m → Bool) :
   ∀ (r k : ℕ) (_ : m - k = r) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ c, VL st.1 (iso c) ∧ VL st.1 (const c) ∧
       VL st.1 (w0 c false) ∧ VL st.1 (w0 c true)) →
     (∀ c, lEv α (iso c) = true → lEv α (const c) = constVal c) →
     (∀ c b, lEv α (w0 c b) = (S c && decide (constVal c = b))) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ q < st.1, α' (Sum.inr q) = α (Sum.inr q)) ∧
       (∀ C ∈ (bbfi m S iso const w0 k st).2, ClauseSat α' C)
 | 0, k, hr, st, α, _, _, _, _, hsat => by
   have hge : ¬ (k < m) := by omega
   unfold bbfi
   simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat⟩
 | r + 1, k, hr, st, α, hst, hw, hic, hwv, hsat => by
   have hk : k < m := by omega
   have hr1 : m - (k + 1) = r := by omega
   unfold bbfi
   simp only [hk, ↓reduceDIte]
   set kf : Fin m := ⟨k, hk⟩
   by_cases hSk : S kf = true
   · simp only [hSk, ↓reduceIte]
     set p0 := fv st
     set p1 := fv p0.2
     set st1 := ei2 p1.1 (w0 kf true)
       (ei2 p0.1 (w0 kf false)
         (ei3 (iso kf) (const kf) p1.1
           (ei3 (iso kf) (negL (const kf)) p0.1 p1.2)))
     let α1 : Sum V ℕ → Bool := fun z =>
       match z with
       | Sum.inl v => α (Sum.inl v)
       | Sum.inr q =>
         if q = st.1 then decide (constVal kf = false)
         else if q = st.1 + 1 then decide (constVal kf = true)
         else α (Sum.inr q)
     have hα1_lt : ∀ q < st.1, α1 (Sum.inr q) = α (Sum.inr q) := by
       intro q hq; simp [α1, show q ≠ st.1 by omega, show q ≠ st.1 + 1 by omega]
     have hα1_inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
     have hsat_st : ∀ C ∈ st.2, ClauseSat α1 C := fun C hC =>
       (cscl hα1_inl hα1_lt (hst C hC).2).2 (hsat C hC)
     have hp0v : lEv α1 p0.1 = decide (constVal kf = false) := by
       simp [p0, fv, lEv, α1]
     have hp1v : lEv α1 p1.1 = decide (constVal kf = true) := by
       have h1 : p0.2.1 = st.1 + 1 := rfl
       have hne : ¬ (st.1 + 1 = st.1) := by omega
       simp [p1, p0, fv, lEv, α1, h1, hne]
     have hsat1 : ∀ C ∈ st1.2, ClauseSat α1 C := by
       simp only [st1, ei2, ei3, addCl, List.mem_cons, forall_eq_or_imp,
         clauseSat_imp2, clauseSat_imp3, litEval_negL]
       refine ⟨?_, ?_, ?_, ?_, hsat_st⟩
       · intro h1
         rw [hp1v] at h1
         rw [lecl hα1_inl hα1_lt (hw kf).2.2.2, hwv kf true, hSk, Bool.true_and]
         exact h1
       · intro h0
         rw [hp0v] at h0
         rw [lecl hα1_inl hα1_lt (hw kf).2.2.1, hwv kf false, hSk, Bool.true_and]
         exact h0
       · intro hi hc
         rw [lecl hα1_inl hα1_lt (hw kf).1] at hi
         rw [lecl hα1_inl hα1_lt (hw kf).2.1] at hc
         rw [hic kf hi] at hc
         rw [hp1v, hc]; rfl
       · intro hi hc
         rw [lecl hα1_inl hα1_lt (hw kf).1] at hi
         rw [lecl hα1_inl hα1_lt (hw kf).2.1] at hc
         rw [hic kf hi] at hc
         rw [hp0v]
         cases hc0 : constVal kf <;> simp [hc0] at hc ⊢
     have hp0st : VS p0.2 := validSt_fresh hst
     have hp1st : VS p1.2 := validSt_fresh hp0st
     have hp1_1 : p1.2.1 = st.1 + 2 := rfl
     have h0v : VL p1.2.1 p0.1 := (validLit_fresh st).mono (by rw [hp1_1]; exact Nat.le_succ _)
     have h1v : VL p1.2.1 p1.1 := by change VL (p0.2.1 + 1) p1.1; exact validLit_fresh p0.2
     have hst1_1 : st1.1 = st.1 + 2 := rfl
     have hst1v : VS st1 :=
       validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp3 (validSt_emitImp3 hp1st
         ((hw kf).1.mono (by rw [hp1_1]; omega)) (validLit_negL.2 ((hw kf).2.1.mono (by rw [hp1_1]; omega))) h0v)
         ((hw kf).1.mono (by dsimp only [ei3, addCl]; rw [hp1_1]; omega))
         ((hw kf).2.1.mono (by dsimp only [ei3, addCl]; rw [hp1_1]; omega))
         (h1v.mono (by dsimp only [ei3, addCl]; omega)))
         (h0v.mono (by dsimp only [ei3, addCl]; omega))
         ((hw kf).2.2.1.mono (by dsimp only [ei3, addCl]; rw [hp1_1]; omega)))
         (h1v.mono (by dsimp only [ei2, ei3, addCl]; omega))
         ((hw kf).2.2.2.mono (by dsimp only [ei2, ei3, addCl]; rw [hp1_1]; omega))
     have hw1 : ∀ c, VL st1.1 (iso c) ∧ VL st1.1 (const c) ∧
         VL st1.1 (w0 c false) ∧ VL st1.1 (w0 c true) := fun c =>
       ⟨(hw c).1.mono (by rw [hst1_1]; omega), (hw c).2.1.mono (by rw [hst1_1]; omega),
       (hw c).2.2.1.mono (by rw [hst1_1]; omega), (hw c).2.2.2.mono (by rw [hst1_1]; omega)⟩
     have hic1 : ∀ c, lEv α1 (iso c) = true → lEv α1 (const c) = constVal c := by
       intro c hi
       rw [lecl hα1_inl hα1_lt (hw c).1] at hi
       rw [lecl hα1_inl hα1_lt (hw c).2.1]
       exact hic c hi
     have hwv1 : ∀ c b, lEv α1 (w0 c b) = (S c && decide (constVal c = b)) := by
       intro c b
       cases b
       · rw [lecl hα1_inl hα1_lt (hw c).2.2.1]; exact hwv c false
       · rw [lecl hα1_inl hα1_lt (hw c).2.2.2]; exact hwv c true
     obtain ⟨α', h'inl, h'lt, h'sat⟩ :=
       bbfi_sat m S iso const w0 constVal r (k + 1) hr1 st1 α1 hst1v hw1 hic1 hwv1 hsat1
     exact ⟨α', fun v => (h'inl v).trans (hα1_inl v), fun q hq => (h'lt q (by omega)).trans (hα1_lt q hq), h'sat⟩
   · simp only [hSk, ↓reduceIte]
     exact bbfi_sat m S iso const w0 constVal r (k + 1) hr1 st α hst hw hic hwv hsat

def bbls {V : Type} [DecidableEq V] (h' d : ℕ) (hd : d < h')
   (wCur wNext : Fin (2 ^ h') → Bool → LN V) : ℕ → St V → St V
 | k, st =>
   if hk : k < 2 ^ h' then
     let kf : Fin (2 ^ h') := ⟨k, hk⟩
     let k0 : Fin (2 ^ h') := ⟨setBit0 k d, setBit0_lt hk hd⟩
     let k1 : Fin (2 ^ h') := ⟨setBit1 k d, setBit1_lt hk hd⟩
     let st1 := ei2 (wCur k0 false) (wNext kf false)
       (ei2 (wCur k0 true) (wNext kf true)
         (ei2 (wCur k1 (false ^^ k.testBit d)) (wNext kf false)
           (ei2 (wCur k1 (true ^^ k.testBit d)) (wNext kf true) st)))
     bbls h' d hd wCur wNext (k + 1) st1
   else st
termination_by k => 2 ^ h' - k

lemma bbls_pr {V : Type} [DecidableEq V] (h' d : ℕ) (hd : d < h')
   (wCur wNext : Fin (2 ^ h') → Bool → LN V) :
   ∀ (r k : ℕ) (_ : 2 ^ h' - k = r) (st : St V),
     VS st →
     (∀ c b, VL st.1 (wCur c b) ∧ VL st.1 (wNext c b)) →
     let st' := bbls h' d hd wCur wNext k st
     VS st' ∧
     st'.1 = st.1 ∧
     st'.2.length ≤ st.2.length + 4 * r ∧
     (∀ C ∈ st.2, C ∈ st'.2) ∧
     ∀ (kf : Fin (2 ^ h')), k ≤ kf.val → ∀ bit : Bool,
       {negL (wCur ⟨setBit0 kf.val d, setBit0_lt kf.2 hd⟩ bit), wNext kf bit} ∈ st'.2 ∧
       {negL (wCur ⟨setBit1 kf.val d, setBit1_lt kf.2 hd⟩ (bit ^^ kf.val.testBit d)), wNext kf bit} ∈ st'.2
 | 0, k, hr, st, hst, _ => by
   have hge : ¬ (k < 2 ^ h') := by omega
   unfold bbls
   simp only [hge, ↓reduceDIte]
   exact ⟨hst, trivial, by omega, fun _ h => h, fun kf hkf => by exfalso; omega⟩
 | r + 1, k, hr, st, hst, hw => by
   have hk : k < 2 ^ h' := by omega
   have hr1 : 2 ^ h' - (k + 1) = r := by omega
   unfold bbls
   simp only [hk, ↓reduceDIte]
   set kf : Fin (2 ^ h') := ⟨k, hk⟩
   set k0 : Fin (2 ^ h') := ⟨setBit0 k d, setBit0_lt hk hd⟩
   set k1 : Fin (2 ^ h') := ⟨setBit1 k d, setBit1_lt hk hd⟩
   set st1 := ei2 (wCur k0 false) (wNext kf false)
     (ei2 (wCur k0 true) (wNext kf true)
       (ei2 (wCur k1 (false ^^ k.testBit d)) (wNext kf false)
         (ei2 (wCur k1 (true ^^ k.testBit d)) (wNext kf true) st)))
   have hst1v : VS st1 := validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp2 hst
     (hw k1 (true ^^ k.testBit d)).1 (hw kf true).2)
     (hw k1 (false ^^ k.testBit d)).1 (hw kf false).2)
     (hw k0 true).1 (hw kf true).2)
     (hw k0 false).1 (hw kf false).2
   have hst1_1 : st1.1 = st.1 := rfl
   have hlen1 : st1.2.length = st.2.length + 4 := rfl
   have hsub1 : ∀ C ∈ st.2, C ∈ st1.2 := fun C hC => by
     simp only [st1, ei2, addCl, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
   have hw1 : ∀ c b, VL st1.1 (wCur c b) ∧ VL st1.1 (wNext c b) := fun c b => by
     rw [hst1_1]; exact hw c b
   obtain ⟨r1, r2, r3, r4, r5⟩ := bbls_pr h' d hd wCur wNext r (k + 1) hr1 st1 hst1v hw1
   refine ⟨r1, r2.trans hst1_1, by omega, fun C hC => r4 C (hsub1 C hC), fun kf' hkf' bit => ?_⟩
   by_cases heq : k = kf'.val
   · have hkeq : kf = kf' := Fin.ext heq
     subst hkeq
     cases bit
     · refine ⟨r4 {negL (wCur k0 false), wNext kf false} (by simp [st1, ei2, addCl, kf]),
               r4 {negL (wCur k1 (false ^^ kf.val.testBit d)), wNext kf false} (by simp [st1, ei2, addCl, kf])⟩
     · refine ⟨r4 {negL (wCur k0 true), wNext kf true} (by simp [st1, ei2, addCl, kf]),
               r4 {negL (wCur k1 (true ^^ kf.val.testBit d)), wNext kf true} (by simp [st1, ei2, addCl, kf])⟩
   · exact r5 kf' (by omega) bit

lemma bbls_sat {V : Type} [DecidableEq V] (h' d : ℕ) (hd : d < h')
   (wCur wNext : Fin (2 ^ h') → Bool → LN V) (α : Sum V ℕ → Bool) :
   ∀ (r k : ℕ) (_ : 2 ^ h' - k = r) (st : St V),
     (∀ kf : Fin (2 ^ h'), ∀ bit : Bool,
       lEv α (wNext kf bit) =
         (lEv α (wCur ⟨setBit0 kf.val d, setBit0_lt kf.2 hd⟩ bit) ||
         lEv α (wCur ⟨setBit1 kf.val d, setBit1_lt kf.2 hd⟩ (bit ^^ kf.val.testBit d)))) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∀ C ∈ (bbls h' d hd wCur wNext k st).2, ClauseSat α C
 | 0, k, hr, st, _, hsat => by
   have hge : ¬ (k < 2 ^ h') := by omega
   unfold bbls
   simp only [hge, ↓reduceDIte]
   exact hsat
 | r + 1, k, hr, st, hrel, hsat => by
   have hk : k < 2 ^ h' := by omega
   have hr1 : 2 ^ h' - (k + 1) = r := by omega
   unfold bbls
   simp only [hk, ↓reduceDIte]
   apply bbls_sat h' d hd wCur wNext α r (k + 1) hr1 _ hrel
   simp only [ei2, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp2]
   have h0 := hrel ⟨k, hk⟩ false
   have h1 := hrel ⟨k, hk⟩ true
   refine ⟨fun h => by rw [h0, h]; rfl, fun h => by rw [h1, h]; rfl,
     fun h => by rw [h0, h, Bool.or_true], fun h => by rw [h1, h, Bool.or_true], hsat⟩

open Classical in
noncomputable def bflyVal (h' : ℕ) (S : Fin (2 ^ h') → Bool) (constVal : Fin (2 ^ h') → Bool)
   (d k : ℕ) (bit : Bool) : Bool :=
 decide (∃ c : Fin (2 ^ h'), AF d c.val k ∧ S c = true ∧ (constVal c ^^ db d c.val k) = bit)

open Classical in
lemma bflyVal_zero {h' : ℕ} (S : Fin (2 ^ h') → Bool) (constVal : Fin (2 ^ h') → Bool)
   (k : Fin (2 ^ h')) (bit : Bool) :
   bflyVal h' S constVal 0 k.val bit = (S k && decide (constVal k = bit)) := by
 rw [Bool.eq_iff_iff]
 simp only [bflyVal, decide_eq_true_eq, Bool.and_eq_true, db, Bool.xor_false]
 constructor
 · rintro ⟨c, hag, hSc, hbit⟩
   have hceq : c = k := Fin.ext ((agreeFrom_zero_iff c.val k.val).1 hag)
   subst hceq
   exact ⟨hSc, hbit⟩
 · rintro ⟨hSc, hbit⟩
   exact ⟨k, (agreeFrom_zero_iff k.val k.val).2 rfl, hSc, hbit⟩

open Classical in
lemma bflyVal_step {h' : ℕ} (S : Fin (2 ^ h') → Bool) (constVal : Fin (2 ^ h') → Bool)
   (d : ℕ) (k : Fin (2 ^ h')) (bit : Bool) :
   bflyVal h' S constVal (d + 1) k.val bit =
     (bflyVal h' S constVal d (setBit0 k.val d) bit ||
     bflyVal h' S constVal d (setBit1 k.val d) (bit ^^ k.val.testBit d)) := by
 rw [Bool.eq_iff_iff]
 simp only [bflyVal, Bool.or_eq_true, decide_eq_true_eq]
 constructor
 · rintro ⟨c, hag, hSc, hbit⟩
   have hdot_k : db d c.val k.val = db d c.val (setBit0 k.val d) :=
     dotBool_congr_lt d fun q hq => by rw [testBit_setBit0, if_neg (by omega)]
   have hdot_k1 : db d c.val k.val = db d c.val (setBit1 k.val d) :=
     dotBool_congr_lt d fun q hq => by rw [testBit_setBit1, if_neg (by omega)]
   cases hcd : c.val.testBit d with
   | false =>
     left
     refine ⟨c, agreeFrom_setBit0.2 ⟨hag, hcd⟩, hSc, ?_⟩
     simp only [db, hcd, Bool.false_and, Bool.xor_false] at hbit
     rw [← hdot_k]
     exact hbit
   | true =>
     right
     refine ⟨c, agreeFrom_setBit1.2 ⟨hag, hcd⟩, hSc, ?_⟩
     simp only [db, hcd, Bool.true_and] at hbit
     rw [← hdot_k1]
     rw [← hbit]
     cases (constVal c) <;> cases (db d c.val k.val) <;> cases (k.val.testBit d) <;> rfl
 · rintro (⟨c, hag, hSc, hbit⟩ | ⟨c, hag, hSc, hbit⟩)
   · obtain ⟨hag1, hcd⟩ := agreeFrom_setBit0.1 hag
     have hdot : db d c.val (setBit0 k.val d) = db d c.val k.val :=
       dotBool_congr_lt d fun q hq => by rw [testBit_setBit0, if_neg (by omega)]
     refine ⟨c, hag1, hSc, ?_⟩
     simp only [db, hcd, Bool.false_and, Bool.xor_false, ← hdot]
     exact hbit
   · obtain ⟨hag1, hcd⟩ := agreeFrom_setBit1.1 hag
     have hdot : db d c.val (setBit1 k.val d) = db d c.val k.val :=
       dotBool_congr_lt d fun q hq => by rw [testBit_setBit1, if_neg (by omega)]
     refine ⟨c, hag1, hSc, ?_⟩
     simp only [db, hcd, Bool.true_and, ← hdot]
     rw [← Bool.xor_assoc, hbit]
     cases bit <;> cases k.val.testBit d <;> rfl

lemma bbls_cm {V : Type} [DecidableEq V] (h' d : ℕ) (hd : d < h')
   (wCur wNext : Fin (2 ^ h') → Bool → LN V) :
   ∀ (r k : ℕ) (_ : 2 ^ h' - k = r) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bbls h' d hd wCur wNext k st).2
 | 0, k, hr, st, C, hC => by
   have hge : ¬ (k < 2 ^ h') := by omega
   unfold bbls
   simp only [hge, ↓reduceDIte]
   exact hC
 | r + 1, k, hr, st, C, hC => by
   have hk : k < 2 ^ h' := by omega
   have hr1 : 2 ^ h' - (k + 1) = r := by omega
   unfold bbls
   simp only [hk, ↓reduceDIte]
   apply bbls_cm h' d hd wCur wNext r (k + 1) hr1
   simp only [ei2, addCl, List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (Or.inr hC)))

def bbl {V : Type} [DecidableEq V] (h' : ℕ) :
   ℕ → (Fin (2 ^ h') → Bool → LN V) → St V →
   (Fin (2 ^ h') → Bool → LN V) × St V
 | d, wCur, st =>
   if hd : d < h' then
     let wNext := ag (2 ^ h') st.1
     let st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
     let st2 := bbls h' d hd wCur wNext 0 st1
     bbl h' (d + 1) wNext st2
   else (wCur, st)
termination_by d => h' - d

lemma bbl_cm {V : Type} [DecidableEq V] (h' : ℕ) :
   ∀ (m d : ℕ) (_ : h' - d = m)
     (wCur : Fin (2 ^ h') → Bool → LN V) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bbl h' d wCur st).2.2
 | 0, d, hm, wCur, st, C, hC => by
   have hge : ¬ (d < h') := by omega
   unfold bbl
   simp only [hge, ↓reduceDIte]
   exact hC
 | m + 1, d, hm, wCur, st, C, hC => by
   have hd : d < h' := by omega
   have hm1 : h' - (d + 1) = m := by omega
   unfold bbl
   simp only [hd, ↓reduceDIte]
   apply bbl_cm h' m (d + 1) hm1
   exact bbls_cm h' d hd _ _ (2 ^ h') 0 (Nat.sub_zero _) _ C hC

lemma bbl_pr {V : Type} [DecidableEq V] (h' : ℕ) :
   ∀ (m d : ℕ) (_ : h' - d = m)
     (wCur : Fin (2 ^ h') → Bool → LN V) (st : St V),
     VS st →
     (∀ c b, VL st.1 (wCur c b)) →
     let res := bbl h' d wCur st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + m * (2 * 2 ^ h') ∧
     res.2.2.length ≤ st.2.length + m * (4 * 2 ^ h') ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ c b, VL res.2.1 (res.1 c b))
 | 0, d, hm, wCur, st, hst, hw => by
   have hge : ¬ (d < h') := by omega
   unfold bbl
   simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, hw⟩
 | m + 1, d, hm, wCur, st, hst, hw => by
   have hd : d < h' := by omega
   have hm1 : h' - (d + 1) = m := by omega
   unfold bbl
   simp only [hd, ↓reduceDIte]
   set wNext := ag (2 ^ h') st.1
   set st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
   have hst1v : VS st1 := fun C hC =>
     ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_add_right _ _)⟩
   have hw1 : ∀ c b, VL st1.1 (wCur c b) ∧ VL st1.1 (wNext c b) := fun c b =>
     ⟨(hw c b).mono (Nat.le_add_right _ _), validLit_allocGrid V (2 ^ h') st.1 c b⟩
   obtain ⟨hst2v, h2_1, h2len, h2sub, _⟩ :=
     bbls_pr h' d hd wCur wNext (2 ^ h') 0 (Nat.sub_zero _) st1 hst1v hw1
   set st2 := bbls h' d hd wCur wNext 0 st1
   have hw2 : ∀ c b, VL st2.1 (wNext c b) := fun c b => by
     rw [h2_1]; exact (hw1 c b).2
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ := bbl_pr h' m (d + 1) hm1 wNext st2 hst2v hw2
   refine ⟨r1, ?_, ?_, ?_, ?_, r6⟩
   · have h1 : st.1 ≤ st2.1 := by rw [h2_1]; change st.1 ≤ st.1 + 2 * 2 ^ h'; omega
     exact le_trans h1 r2
   · have h1 : st2.1 = st.1 + 2 * 2 ^ h' := h2_1
     calc (bbl h' (d + 1) wNext st2).2.1
       _ ≤ st2.1 + m * (2 * 2 ^ h') := r3
       _ = st.1 + (m + 1) * (2 * 2 ^ h') := by rw [h1]; ring
   · have h1 : st2.2.length ≤ st.2.length + 4 * 2 ^ h' := h2len
     calc (bbl h' (d + 1) wNext st2).2.2.length
       _ ≤ st2.2.length + m * (4 * 2 ^ h') := r4
       _ ≤ (st.2.length + 4 * 2 ^ h') + m * (4 * 2 ^ h') := Nat.add_le_add_right h1 _
       _ = st.2.length + (m + 1) * (4 * 2 ^ h') := by ring
   · exact fun C hC => r5 C (h2sub C hC)

open Classical in
lemma bbl_sat {V : Type} [DecidableEq V] (h' : ℕ)
   (S : Fin (2 ^ h') → Bool) (constVal : Fin (2 ^ h') → Bool) :
   ∀ (m d : ℕ) (_ : d + m = h')
     (wCur : Fin (2 ^ h') → Bool → LN V) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ c b, VL st.1 (wCur c b)) →
     (∀ c b, lEv α (wCur c b) = bflyVal h' S constVal d c.val b) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ q < st.1, α' (Sum.inr q) = α (Sum.inr q)) ∧
       (∀ C ∈ (bbl h' d wCur st).2.2, ClauseSat α' C) ∧
       ∀ s b, lEv α' ((bbl h' d wCur st).1 s b) = bflyVal h' S constVal h' s.val b
 | 0, d, hm, wCur, st, α, _, _, hval, hsat => by
   have hdeq : d = h' := by omega
   subst hdeq
   have hge : ¬ (d < d) := Nat.lt_irrefl d
   unfold bbl
   simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, hval⟩
 | m + 1, d, hm, wCur, st, α, hst, hw, hval, hsat => by
   have hd : d < h' := by omega
   have hm1 : (d + 1) + m = h' := by omega
   unfold bbl
   simp only [hd, ↓reduceDIte]
   set wNext := ag (2 ^ h') st.1
   set st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
   let α1 : Sum V ℕ → Bool := fun z =>
     match z with
     | Sum.inl v => α (Sum.inl v)
     | Sum.inr q =>
       if hq1 : st.1 ≤ q ∧ q < st.1 + 2 * 2 ^ h' then
         let idx := q - st.1
         let k : Fin (2 ^ h') := ⟨idx / 2, by omega⟩
         let b : Bool := decide (idx % 2 = 1)
         bflyVal h' S constVal (d + 1) k.val b
       else α (Sum.inr q)
   have hα1_lt : ∀ q < st.1, α1 (Sum.inr q) = α (Sum.inr q) := by
     intro q hq
     have hnot : ¬ (st.1 ≤ q ∧ q < st.1 + 2 * 2 ^ h') := by omega
     simp [α1, hnot]
   have hα1_inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
   have hsat_st1 : ∀ C ∈ st1.2, ClauseSat α1 C := fun C hC =>
     (cscl hα1_inl hα1_lt (hst C hC).2).2 (hsat C hC)
   have hwNext_val : ∀ k b, lEv α1 (wNext k b) = bflyVal h' S constVal (d + 1) k.val b := by
     intro k b
     dsimp only [wNext]
     rw [litEval_allocGrid]
     have hbd : st.1 ≤ st.1 + 2 * k.val + (if b then 1 else 0) ∧
         st.1 + 2 * k.val + (if b then 1 else 0) < st.1 + 2 * 2 ^ h' := by
       cases b <;> simp <;> omega
     simp only [α1, hbd, and_self, ↓reduceDIte]
     have hidx : st.1 + 2 * k.val + (if b then 1 else 0) - st.1 = 2 * k.val + (if b then 1 else 0) := by omega
     have hdiv : (2 * k.val + (if b then 1 else 0)) / 2 = k.val := by cases b <;> simp; omega
     have hmod : decide ((2 * k.val + (if b then 1 else 0)) % 2 = 1) = b := by cases b <;> simp
     simp only [hidx, hdiv, hmod]
   have hrel : ∀ kf : Fin (2 ^ h'), ∀ bit : Bool,
       lEv α1 (wNext kf bit) =
         (lEv α1 (wCur ⟨setBit0 kf.val d, setBit0_lt kf.2 hd⟩ bit) ||
         lEv α1 (wCur ⟨setBit1 kf.val d, setBit1_lt kf.2 hd⟩ (bit ^^ kf.val.testBit d))) := by
     intro kf bit
     rw [hwNext_val kf bit, bflyVal_step]
     rw [lecl hα1_inl hα1_lt (hw _ _), lecl hα1_inl hα1_lt (hw _ _)]
     rw [hval _ _, hval _ _]
   have hsat_st2 : ∀ C ∈ (bbls h' d hd wCur wNext 0 st1).2, ClauseSat α1 C :=
     bbls_sat h' d hd wCur wNext α1 (2 ^ h') 0 (Nat.sub_zero _) st1 hrel hsat_st1
   have hst1v : VS st1 := fun C hC => ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_add_right _ _)⟩
   have hw1 : ∀ c b, VL st1.1 (wCur c b) ∧ VL st1.1 (wNext c b) := fun c b =>
     ⟨(hw c b).mono (Nat.le_add_right _ _), validLit_allocGrid V (2 ^ h') st.1 c b⟩
   obtain ⟨hst2v, h2_1, _, _, _⟩ :=
     bbls_pr h' d hd wCur wNext (2 ^ h') 0 (Nat.sub_zero _) st1 hst1v hw1
   set st2 := bbls h' d hd wCur wNext 0 st1
   have hw2 : ∀ c b, VL st2.1 (wNext c b) := fun c b => by
     rw [h2_1]; exact (hw1 c b).2
   obtain ⟨α', h'inl, h'lt, h'sat, h'val⟩ :=
     bbl_sat h' S constVal m (d + 1) hm1 wNext st2 α1 hst2v hw2 hwNext_val hsat_st2
   refine ⟨α', fun v => (h'inl v).trans (hα1_inl v), fun q hq => ?_, h'sat, h'val⟩
   exact (h'lt q (by rw [h2_1]; change q < st.1 + 2 * 2 ^ h'; omega)).trans (hα1_lt q hq)

lemma bbl_up {V : Type} [DecidableEq V] (h' : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V)) (c s : Fin (2 ^ h')) (val0 : Bool) :
   ∀ (m d : ℕ) (_ : d + m = h')
     (wCur : Fin (2 ^ h') → Bool → LN V) (st : St V) (d0 : ℕ),
     VS st →
     (∀ c' b', VL st.1 (wCur c' b')) →
     (∀ C ∈ (bbl h' d wCur st).2.2, C ∈ F) →
     wCur ⟨bm d c.val s.val, bflyMid_lt c.2 d (by omega)⟩ (val0 ^^ db d c.val s.val) ∈
       (upS F)^[d0] seed →
     (bbl h' d wCur st).1 s (val0 ^^ db h' c.val s.val) ∈
       (upS F)^[d0 + m] seed
 | 0, d, hm, wCur, st, d0, _, _, _, hmem => by
   have hdeq : d = h' := by omega
   subst hdeq
   have hge : ¬ (d < d) := Nat.lt_irrefl d
   unfold bbl
   simp only [hge, ↓reduceDIte]
   have hmid : (⟨bm d c.val s.val, bflyMid_lt c.2 d le_rfl⟩ : Fin (2 ^ d)) = s :=
     Fin.ext (bflyMid_eq c.2 s.2)
   rw [hmid] at hmem
   simpa using hmem
 | m + 1, d, hm, wCur, st, d0, hst, hw, hF, hmem => by
   have hd : d < h' := by omega
   have hm1 : (d + 1) + m = h' := by omega
   unfold bbl at hF ⊢
   simp only [hd, ↓reduceDIte] at hF ⊢
   set wNext := ag (2 ^ h') st.1
   set st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
   have hst1v : VS st1 := fun C hC => ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_add_right _ _)⟩
   have hw1 : ∀ c' b', VL st1.1 (wCur c' b') ∧ VL st1.1 (wNext c' b') := fun c' b' =>
     ⟨(hw c' b').mono (Nat.le_add_right _ _), validLit_allocGrid V (2 ^ h') st.1 c' b'⟩
   obtain ⟨hst2v, h2_1, _, _, r5⟩ :=
     bbls_pr h' d hd wCur wNext (2 ^ h') 0 (Nat.sub_zero _) st1 hst1v hw1
   set st2 := bbls h' d hd wCur wNext 0 st1
   have hw2 : ∀ c' b', VL st2.1 (wNext c' b') := fun c' b' => by
     rw [h2_1]; exact (hw1 c' b').2
   have hC_in_F : ∀ C ∈ st2.2, C ∈ F := fun C hC =>
     hF C (bbl_cm h' m (d + 1) (by omega) wNext st2 C hC)
   set kNext : Fin (2 ^ h') := ⟨bm (d + 1) c.val s.val, bflyMid_lt c.2 (d + 1) (by omega)⟩
   let bCur := val0 ^^ db d c.val s.val
   let bNext := val0 ^^ db (d + 1) c.val s.val
   have hnext_mem : wNext kNext bNext ∈ (upS F)^[d0 + 1] seed := by
     rw [Function.iterate_succ_apply']
     have hstep := r5 kNext (Nat.zero_le _) bNext
     cases hcd : c.val.testBit d
     · have hC : ({negL (wCur ⟨setBit0 kNext.val d, setBit0_lt kNext.2 hd⟩ bNext),
           wNext kNext bNext} : CN V) ∈ F := hC_in_F _ hstep.1
       have heqk : (⟨setBit0 kNext.val d, setBit0_lt kNext.2 hd⟩ : Fin (2 ^ h')) =
           ⟨bm d c.val s.val, bflyMid_lt c.2 d (by omega)⟩ := by
         ext; simpa [kNext, hcd] using (bflyMid_step d c.val s.val).symm
       have heqb : bNext = bCur := by
         simp [bNext, bCur, db, hcd]
       have hC' : ({negL (wCur ⟨bm d c.val s.val, bflyMid_lt c.2 d (by omega)⟩ bCur),
           wNext kNext bNext} : CN V) ∈ F := by
         rw [← heqk, ← heqb]; exact hC
       exact upStep_unit2 hC' (by rw [negL_negL]; exact hmem)
     · have hC : ({negL (wCur ⟨setBit1 kNext.val d, setBit1_lt kNext.2 hd⟩ (bNext ^^ kNext.val.testBit d)),
           wNext kNext bNext} : CN V) ∈ F := hC_in_F _ hstep.2
       have heqk : (⟨setBit1 kNext.val d, setBit1_lt kNext.2 hd⟩ : Fin (2 ^ h')) =
           ⟨bm d c.val s.val, bflyMid_lt c.2 d (by omega)⟩ := by
         ext; simpa [kNext, hcd] using (bflyMid_step d c.val s.val).symm
       have hktest : kNext.val.testBit d = s.val.testBit d := by
         simp only [kNext, testBit_bflyMid]
         split_ifs with hlt
         · rfl
         · exfalso; omega
       have heqb : (bNext ^^ kNext.val.testBit d) = bCur := by
         simp only [bNext, bCur, db, hcd, Bool.true_and, hktest]
         cases val0 <;> cases (db d c.val s.val) <;> cases (s.val.testBit d) <;> rfl
       rw [heqk, heqb] at hC
       exact upStep_unit2 hC (by rw [negL_negL]; exact hmem)
   have hrec := bbl_up h' F seed c s val0 m (d + 1) hm1 wNext st2 (d0 + 1) hst2v hw2 hF hnext_mem
   rwa [show (d0 + 1) + m = d0 + (m + 1) by omega] at hrec

def bbf {V : Type} [DecidableEq V] (h' : ℕ)
   (S : Fin (2 ^ h') → Bool) (iso const : Fin (2 ^ h') → LN V)
   (st : St V) : (Fin (2 ^ h') → Bool → LN V) × St V :=
 let w0 := ag (2 ^ h') st.1
 let st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
 let st2 := bbfi (2 ^ h') S iso const w0 0 st1
 bbl h' 0 w0 st2

lemma bbf_pr {V : Type} [DecidableEq V] (h' : ℕ)
   (S : Fin (2 ^ h') → Bool) (iso const : Fin (2 ^ h') → LN V)
   (st : St V) (hst : VS st)
   (hvalid : ∀ c, VL st.1 (iso c) ∧ VL st.1 (const c)) :
   let res := bbf h' S iso const st
   VS res.2 ∧
   st.1 ≤ res.2.1 ∧
   res.2.1 ≤ st.1 + (4 + 2 * h') * 2 ^ h' ∧
   res.2.2.length ≤ st.2.length + (4 + 4 * h') * 2 ^ h' ∧
   (∀ C ∈ st.2, C ∈ res.2.2) ∧
   (∀ s b, VL res.2.1 (res.1 s b)) := by
 dsimp only [bbf]
 set w0 := ag (2 ^ h') st.1
 set st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
 have hst1v : VS st1 := fun C hC => ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_add_right _ _)⟩
 have hw1 : ∀ c, VL st1.1 (iso c) ∧ VL st1.1 (const c) ∧
     VL st1.1 (w0 c false) ∧ VL st1.1 (w0 c true) := fun c =>
   ⟨(hvalid c).1.mono (Nat.le_add_right _ _), (hvalid c).2.mono (Nat.le_add_right _ _),
   validLit_allocGrid V (2 ^ h') st.1 c false, validLit_allocGrid V (2 ^ h') st.1 c true⟩
 obtain ⟨hst2v, h2le, h2_1, h2len, h2sub, _⟩ :=
   bbfi_pr (2 ^ h') S iso const w0 (2 ^ h') 0 (Nat.sub_zero _) st1 hst1v hw1
 set st2 := bbfi (2 ^ h') S iso const w0 0 st1
 have hw2 : ∀ c b, VL st2.1 (w0 c b) := fun c b => by
   cases b
   · exact (hw1 c).2.2.1.mono h2le
   · exact (hw1 c).2.2.2.mono h2le
 obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
   bbl_pr h' h' 0 (Nat.sub_zero _) w0 st2 hst2v hw2
 refine ⟨r1, le_trans (le_trans (Nat.le_add_right _ _) h2le) r2, ?_, ?_, fun C hC => r5 C (h2sub C hC), r6⟩
 · have ha : st2.1 ≤ st.1 + 4 * 2 ^ h' := by
     have h2_1' : st2.1 ≤ st1.1 + 2 * 2 ^ h' := h2_1
     have hst1_1 : st1.1 = st.1 + 2 * 2 ^ h' := rfl
     omega
   calc (bbl h' 0 w0 st2).2.1
     _ ≤ st2.1 + h' * (2 * 2 ^ h') := r3
     _ ≤ (st.1 + 4 * 2 ^ h') + h' * (2 * 2 ^ h') := Nat.add_le_add_right ha _
     _ = st.1 + (4 + 2 * h') * 2 ^ h' := by ring
 · have hb : st2.2.length ≤ st.2.length + 4 * 2 ^ h' := h2len
   calc (bbl h' 0 w0 st2).2.2.length
     _ ≤ st2.2.length + h' * (4 * 2 ^ h') := r4
     _ ≤ (st.2.length + 4 * 2 ^ h') + h' * (4 * 2 ^ h') := Nat.add_le_add_right hb _
     _ = st.2.length + (4 + 4 * h') * 2 ^ h' := by ring

open Classical in
lemma bbf_sat {V : Type} [DecidableEq V] (h' : ℕ)
   (S : Fin (2 ^ h') → Bool) (iso const : Fin (2 ^ h') → LN V)
   (st : St V) (α : Sum V ℕ → Bool) (constVal : Fin (2 ^ h') → Bool)
   (hst : VS st)
   (hvalid : ∀ c, VL st.1 (iso c) ∧ VL st.1 (const c))
   (hic : ∀ c, lEv α (iso c) = true → lEv α (const c) = constVal c)
   (hsat : ∀ C ∈ st.2, ClauseSat α C) :
   ∃ α' : Sum V ℕ → Bool,
     (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
     (∀ q < st.1, α' (Sum.inr q) = α (Sum.inr q)) ∧
     (∀ C ∈ (bbf h' S iso const st).2.2, ClauseSat α' C) ∧
     ∀ s b, lEv α' ((bbf h' S iso const st).1 s b) =
       decide (∃ c : Fin (2 ^ h'), S c = true ∧ (constVal c ^^ db h' c.val s.val) = b) := by
 dsimp only [bbf]
 set w0 := ag (2 ^ h') st.1
 set st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
 let α1 : Sum V ℕ → Bool := fun z =>
   match z with
   | Sum.inl v => α (Sum.inl v)
   | Sum.inr q =>
     if hq1 : st.1 ≤ q ∧ q < st.1 + 2 * 2 ^ h' then
       let idx := q - st.1
       let k : Fin (2 ^ h') := ⟨idx / 2, by omega⟩
       let b : Bool := decide (idx % 2 = 1)
       bflyVal h' S constVal 0 k.val b
     else α (Sum.inr q)
 have hα1_lt : ∀ q < st.1, α1 (Sum.inr q) = α (Sum.inr q) := by
   intro q hq
   have hnot : ¬ (st.1 ≤ q ∧ q < st.1 + 2 * 2 ^ h') := by omega
   simp [α1, hnot]
 have hα1_inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
 have hsat_st1 : ∀ C ∈ st1.2, ClauseSat α1 C := fun C hC =>
   (cscl hα1_inl hα1_lt (hst C hC).2).2 (hsat C hC)
 have hw0_val : ∀ k b, lEv α1 (w0 k b) = (S k && decide (constVal k = b)) := by
   intro k b
   dsimp only [w0]
   rw [litEval_allocGrid]
   have hbd : st.1 ≤ st.1 + 2 * k.val + (if b then 1 else 0) ∧
       st.1 + 2 * k.val + (if b then 1 else 0) < st.1 + 2 * 2 ^ h' := by
     cases b <;> simp <;> omega
   simp only [α1, hbd, and_self, ↓reduceDIte]
   have hidx : st.1 + 2 * k.val + (if b then 1 else 0) - st.1 = 2 * k.val + (if b then 1 else 0) := by omega
   have hdiv : (2 * k.val + (if b then 1 else 0)) / 2 = k.val := by cases b <;> simp; omega
   have hmod : decide ((2 * k.val + (if b then 1 else 0)) % 2 = 1) = b := by cases b <;> simp
   simp only [hidx, hdiv, hmod]
   exact bflyVal_zero S constVal k b
 have hst1v : VS st1 := fun C hC => ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_add_right _ _)⟩
 have hw1 : ∀ c, VL st1.1 (iso c) ∧ VL st1.1 (const c) ∧
     VL st1.1 (w0 c false) ∧ VL st1.1 (w0 c true) := fun c =>
   ⟨(hvalid c).1.mono (Nat.le_add_right _ _), (hvalid c).2.mono (Nat.le_add_right _ _),
   validLit_allocGrid V (2 ^ h') st.1 c false, validLit_allocGrid V (2 ^ h') st.1 c true⟩
 have hic1 : ∀ c, lEv α1 (iso c) = true → lEv α1 (const c) = constVal c := by
   intro c hi
   rw [lecl hα1_inl hα1_lt (hvalid c).1] at hi
   rw [lecl hα1_inl hα1_lt (hvalid c).2]
   exact hic c hi
 obtain ⟨α2, h2inl, h2lt, h2sat⟩ :=
   bbfi_sat (2 ^ h') S iso const w0 constVal (2 ^ h') 0 (Nat.sub_zero _)
     st1 α1 hst1v hw1 hic1 hw0_val hsat_st1
 obtain ⟨hst2v, h2le, h2_1, _, _, _⟩ :=
   bbfi_pr (2 ^ h') S iso const w0 (2 ^ h') 0 (Nat.sub_zero _) st1 hst1v hw1
 set st2 := bbfi (2 ^ h') S iso const w0 0 st1
 have hw2 : ∀ c b, VL st2.1 (w0 c b) := fun c b => by
   cases b
   · exact (hw1 c).2.2.1.mono h2le
   · exact (hw1 c).2.2.2.mono h2le
 have hw2val : ∀ c b, lEv α2 (w0 c b) = bflyVal h' S constVal 0 c.val b := by
   intro c b
   have hlit : lEv α2 (w0 c b) = lEv α1 (w0 c b) := by
     cases b
     · exact lecl h2inl h2lt (hw1 c).2.2.1
     · exact lecl h2inl h2lt (hw1 c).2.2.2
   rw [hlit, hw0_val, bflyVal_zero]
 obtain ⟨α3, h3inl, h3lt, h3sat, h3val⟩ :=
   bbl_sat h' S constVal h' 0 (Nat.zero_add h') w0 st2 α2 hst2v hw2 hw2val h2sat
 refine ⟨α3, fun v => (h3inl v).trans ((h2inl v).trans (hα1_inl v)), fun q hq => ?_, h3sat, fun s b => ?_⟩
 · have hq1 : q < st1.1 := by dsimp only [st1]; omega
   exact (h3lt q (lt_of_lt_of_le hq1 h2le)).trans ((h2lt q hq1).trans (hα1_lt q hq))
 · rw [h3val s b, Bool.eq_iff_iff]
   simp only [bflyVal, decide_eq_true_eq]
   constructor
   · rintro ⟨c, _, hSc, hbit⟩; exact ⟨c, hSc, hbit⟩
   · rintro ⟨c, hSc, hbit⟩; exact ⟨c, agreeFrom_top c.2 s.2, hSc, hbit⟩

lemma bbf_up {V : Type} [DecidableEq V] (h' : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (S : Fin (2 ^ h') → Bool) (iso const : Fin (2 ^ h') → LN V)
   (st : St V) (d0 : ℕ) (c s : Fin (2 ^ h')) (val0 : Bool) :
   VS st →
   (∀ c', VL st.1 (iso c') ∧ VL st.1 (const c')) →
   (∀ C ∈ (bbf h' S iso const st).2.2, C ∈ F) →
   S c = true →
   iso c ∈ (upS F)^[d0] seed →
   fLt (const c) val0 ∈ (upS F)^[d0] seed →
   (bbf h' S iso const st).1 s (val0 ^^ db h' c.val s.val) ∈
     (upS F)^[d0 + 2 + h'] seed := by
 intro hst hvalid hF hSc hiso hconst
 dsimp only [bbf] at hF ⊢
 set w0 := ag (2 ^ h') st.1
 set st1 : St V := (st.1 + 2 * 2 ^ h', st.2)
 have hst1v : VS st1 := fun C hC => ⟨(hst C hC).1, (hst C hC).2.mono (Nat.le_add_right _ _)⟩
 have hw1 : ∀ c', VL st1.1 (iso c') ∧ VL st1.1 (const c') ∧
     VL st1.1 (w0 c' false) ∧ VL st1.1 (w0 c' true) := fun c' =>
   ⟨(hvalid c').1.mono (Nat.le_add_right _ _), (hvalid c').2.mono (Nat.le_add_right _ _),
   validLit_allocGrid V (2 ^ h') st.1 c' false, validLit_allocGrid V (2 ^ h') st.1 c' true⟩
 obtain ⟨hst2v, h2le, _, _, _, r6⟩ :=
   bbfi_pr (2 ^ h') S iso const w0 (2 ^ h') 0 (Nat.sub_zero _) st1 hst1v hw1
 set st2 := bbfi (2 ^ h') S iso const w0 0 st1
 have hF2 : ∀ C ∈ st2.2, C ∈ F := fun C hC =>
   hF C (bbl_cm h' h' 0 (Nat.sub_zero _) w0 st2 C hC)
 obtain ⟨a0, a1, ha0, ha1, hw0_f, hw0_t⟩ := r6 c (Nat.zero_le _) hSc
 have hw0_mem : w0 c val0 ∈ (upS F)^[d0 + 2] seed := by
   cases val0
   · have ha0_mem : a0 ∈ (upS F)^[d0 + 1] seed := by
       rw [Function.iterate_succ_apply']
       exact upStep_unit3 (hF2 _ ha0) (by rw [negL_negL]; exact hiso)
         (by simpa [fLt, negL_negL] using hconst)
     rw [show d0 + 2 = (d0 + 1) + 1 by omega, Function.iterate_succ_apply']
     exact upStep_unit2 (hF2 _ hw0_f) (by rw [negL_negL]; exact ha0_mem)
   · have ha1_mem : a1 ∈ (upS F)^[d0 + 1] seed := by
       rw [Function.iterate_succ_apply']
       exact upStep_unit3 (hF2 _ ha1) (by rw [negL_negL]; exact hiso)
         (by simpa [fLt, negL_negL] using hconst)
     rw [show d0 + 2 = (d0 + 1) + 1 by omega, Function.iterate_succ_apply']
     exact upStep_unit2 (hF2 _ hw0_t) (by rw [negL_negL]; exact ha1_mem)
 have hw2 : ∀ c' b', VL st2.1 (w0 c' b') := fun c' b' => by
   cases b'
   · exact (hw1 c').2.2.1.mono h2le
   · exact (hw1 c').2.2.2.mono h2le
 have hrec := bbl_up h' F seed c s val0 h' 0 (Nat.zero_add h') w0 st2 (d0 + 2)
   hst2v hw2 hF (by simpa [bm, db] using hw0_mem)
 exact hrec

lemma add_one_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k
 | 0 => by simp
 | k + 1 => by
   have ih := add_one_le_two_pow k
   have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
   omega

lemma clog2_bound_mul3 {R h' L : ℕ} (hR : R ≤ 3 * (h' + 1) * (L + 1)) :
   Nat.clog 2 R ≤ 2 + h' + L := by
 rw [Nat.clog_le_iff_le_pow (by omega)]
 have hh := add_one_le_two_pow h'
 have hL := add_one_le_two_pow L
 calc R ≤ 3 * (h' + 1) * (L + 1) := hR
   _ ≤ 4 * (2 ^ h') * (2 ^ L) := by
     apply Nat.mul_le_mul (Nat.mul_le_mul (by omega) hh) hL
   _ = 2 ^ (2 + h' + L) := by
     have : (4 : ℕ) = 2 ^ 2 := rfl
     rw [this, ← pow_add, ← pow_add]

lemma xorList_map_xor {α : Type} : ∀ (L : List α) (f g : α → Bool),
   xl (L.map (fun a => f a ^^ g a)) = (xl (L.map f) ^^ xl (L.map g))
 | [], _, _ => rfl
 | a :: as, f, g => by
   simp only [List.map_cons, xl]
   rw [xorList_map_xor as f g]
   cases f a <;> cases g a <;> cases xl (as.map f) <;> cases xl (as.map g) <;> rfl

lemma xorList_map_and_right {α : Type} : ∀ (L : List α) (f : α → Bool) (z : Bool),
   (xl (L.map f) && z) = xl (L.map (fun a => f a && z))
 | [], _, z => by simp [xl]
 | a :: as, f, z => by
   simp only [List.map_cons, xl]
   rw [← xorList_map_and_right as f z]
   cases f a <;> cases xl (as.map f) <;> cases z <;> rfl

lemma xorList_swap {α β : Type} : ∀ (L1 : List α) (L2 : List β) (g : α → β → Bool),
   xl (L1.map (fun a => xl (L2.map (g a)))) =
     xl (L2.map (fun b => xl (L1.map (fun a => g a b))))
 | [], L2, g => by
   rw [List.map_nil, xl]
   induction L2 with
   | nil => rfl
   | cons b bs ih =>
     simp only [List.map_cons, xl]
     rw [← ih]
     rfl
 | a :: as, L2, g => by
   simp only [List.map_cons, xl]
   rw [xorList_swap as L2 g, ← xorList_map_xor L2 (g a) (fun b => xl (as.map (fun a' => g a' b)))]

lemma xorList_map_if_filter {α : Type} : ∀ (L : List α) (p : α → Bool) (x : α → Bool),
   xl (L.map (fun a => if p a then x a else false)) = xl ((L.filter p).map x)
 | [], _, _ => rfl
 | a :: as, p, x => by
   simp only [List.map_cons, List.filter_cons]
   cases hp : p a
   · simp only [Bool.false_eq_true, ↓reduceIte, xl, Bool.false_xor]
     exact xorList_map_if_filter as p x
   · simp only [↓reduceIte, List.map_cons, xl]
     rw [xorList_map_if_filter as p x]

lemma xorList_split_elem {α : Type} [DecidableEq α] : ∀ (L : List α),
   L.Nodup → ∀ (i : α), i ∈ L → ∀ (f : α → Bool),
     (f i ^^ xl ((L.filter (· ≠ i)).map f)) = xl (L.map f)
 | [], _, i, hi, _ => by cases hi
 | a :: as, hnd, i, hi, f => by
   rw [List.nodup_cons] at hnd
   rcases List.mem_cons.1 hi with rfl | hias
   · have has : as.filter (· ≠ i) = as :=
       List.filter_eq_self.2 (fun y hy => decide_eq_true (by rintro rfl; exact hnd.1 hy))
     rw [List.filter_cons, if_neg (by simp), has]
     rfl
   · have hne : a ≠ i := by rintro rfl; exact hnd.1 hias
     have ih := xorList_split_elem as hnd.2 i hias f
     simp only [List.filter_cons, decide_eq_true hne, ↓reduceIte, List.map_cons, xl]
     rw [← ih]
     cases f i <;> cases f a <;> cases xl (List.map f (List.filter (· ≠ i) as)) <;> rfl

lemma list_ofFn_eq_map_finRange {k : ℕ} (f : Fin k → Bool) :
   List.ofFn f = (List.finRange k).map f := by
 apply List.ext_getElem
 · simp
 · intro i hi1 hi2
   simp

lemma finRange_succ_eq_last (k : ℕ) :
   List.finRange (k + 1) = (List.finRange k).map Fin.castSucc ++ [Fin.last k] := by
 apply List.ext_getElem
 · simp
 · intro idx h1 h2
   by_cases hlt : idx < k
   · simp [List.getElem_append_left, hlt]
   · have heq : idx = k := by simp at h1; omega
     subst heq
     rw [List.getElem_append_right (by simp)]
     apply Fin.ext
     simp

lemma dotBool_eq_xorList (c s : ℕ) : ∀ h' : ℕ,
   db h' c s = xl ((List.finRange h').map (fun q : Fin h' => decide (c.testBit q.val) && s.testBit q.val))
 | 0 => by simp [db, xl]
 | h' + 1 => by
   rw [db, dotBool_eq_xorList c s h', finRange_succ_eq_last h', List.map_append, List.map_map, xorList_append]
   simp only [Function.comp_def, Fin.coe_castSucc, List.map_cons, List.map_nil, xl, Bool.xor_false, Fin.val_last]
   rfl

lemma syndrome_parity_id {h' n : ℕ} (H_row : Fin h' → Fin n → Bool) (c s : Fin (2 ^ h'))
   (x : Fin n → Bool) (i : Fin n)
   (hs : ∀ q : Fin h', s.val.testBit q.val = xl (((List.finRange n).filter (fun j => H_row q j)).map x))
   (hSci : xl (List.ofFn (fun q : Fin h' => decide (c.val.testBit q.val) && H_row q i)) = true) :
   (xl (((List.finRange n).filter (· ≠ i)).map
     (fun j => if xl (List.ofFn (fun q : Fin h' => decide (c.val.testBit q.val) && H_row q j)) then x j else false))
     ^^ db h' c.val s.val) = x i := by
 let S : Fin n → Bool := fun j => xl (List.ofFn (fun q : Fin h' => decide (c.val.testBit q.val) && H_row q j))
 have hS_full : xl ((List.finRange n).map (fun j => if S j then x j else false)) = db h' c.val s.val := by
   have hif : (fun j => if S j then x j else false) = (fun j => S j && x j) := by
     ext j; cases S j <;> rfl
   rw [hif]
   have hmap : ((List.finRange n).map (fun j => S j && x j)) =
       (List.finRange n).map (fun j => xl ((List.finRange h').map
         (fun q => (decide (c.val.testBit q.val) && H_row q j) && x j))) := by
     refine List.map_congr_left fun j _ => ?_
     dsimp only [S]
     rw [list_ofFn_eq_map_finRange, xorList_map_and_right]
   rw [hmap, xorList_swap, dotBool_eq_xorList]
   congr 1
   refine List.map_congr_left fun q _ => ?_
   have hq_if : (fun j : Fin n => (decide (c.val.testBit q.val) && H_row q j) && x j) =
       (fun j => if H_row q j then (if c.val.testBit q.val then x j else false) else false) := by
     ext j; cases c.val.testBit q.val <;> cases H_row q j <;> cases x j <;> rfl
   rw [hq_if, xorList_map_if_filter]
   cases hc : c.val.testBit q.val
   · simp only [Bool.false_eq_true, ↓reduceIte]
     have h0 : ∀ L : List (Fin n), xl (L.map (fun _ => false)) = false := by
       intro L; induction L with
       | nil => rfl
       | cons _ _ ih => simp only [List.map_cons, xl]; rw [ih]; rfl
     exact h0 _
   · simp only [hc, decide_true, Bool.true_and, ↓reduceIte, hs q]
 have hsplit := xorList_split_elem (List.finRange n) (List.nodup_finRange n) i (List.mem_finRange i)
   (fun j => if S j then x j else false)
 have hSi : (if S i then x i else false) = x i := by rw [if_pos hSci]
 rw [hSi, hS_full] at hsplit
 rw [← hsplit]
 cases hx : x i <;>
   cases hy : xl (List.map (fun j => if S j then x j else false) (List.filter (· ≠ i) (List.finRange n))) <;> rfl

def ber {V : Type} [DecidableEq V] {n : ℕ} (m : ℕ) (S : Fin m → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) :
   ℕ → (Fin m → Fin n → LN V × LN V) → St V →
     (Fin m → Fin n → LN V × LN V) × St V
 | k, arr, st =>
   if hk : k < m then
     let kf : Fin m := ⟨k, hk⟩
     let up := bue (S kf) kL xLit tL fL T_n st
     let dn := bde up.1 (tL, fL) up.2
     let arr' : Fin m → Fin n → LN V × LN V :=
       fun c => if c = kf then dn.1 else arr c
     ber m S kL xLit tL fL T_n (k + 1) arr' dn.2
   else (arr, st)
termination_by k => m - k

lemma ber_cm {V : Type} [DecidableEq V] {n : ℕ} (m : ℕ)
   (S : Fin m → Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) (T_n : BTree (Fin n)) :
   ∀ (r k : ℕ) (hr : m - k = r) (arr : Fin m → Fin n → LN V × LN V)
     (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (ber m S kL xLit tL fL T_n k arr st).2.2
 | 0, k, hr, arr, st, C, hC => by
   have hge : ¬ (k < m) := by omega
   unfold ber
   simp only [hge, ↓reduceDIte]
   exact hC
 | r + 1, k, hr, arr, st, C, hC => by
   have hk : k < m := by omega
   have hm1 : m - (k + 1) = r := by omega
   unfold ber
   simp only [hk, ↓reduceDIte]
   apply ber_cm m S kL xLit tL fL T_n r (k + 1) hm1 _ _ C
   apply bde_cm
   apply bue_cm
   exact hC

lemma ber_pr {V : Type} [DecidableEq V] {n : ℕ} (m : ℕ)
   (S : Fin m → Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) (T_n : BTree (Fin n)) :
   ∀ (r k : ℕ) (hr : m - k = r) (arr : Fin m → Fin n → LN V × LN V)
     (st : St V),
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     (∀ c : Fin m, c.val < k → ∀ i, VL st.1 (arr c i).1 ∧ VL st.1 (arr c i).2) →
     let res := ber m S kL xLit tL fL T_n k arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + 6 * T_n.intNodes * r ∧
     res.2.2.length ≤ st.2.length + 21 * T_n.intNodes * r ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ c : Fin m, ∀ i, VL res.2.1 (res.1 c i).1 ∧ VL res.2.1 (res.1 c i).2)
 | 0, k, hr, arr, st, hst, _, _, _, harr => by
   have hge : ¬ (k < m) := by omega
   unfold ber
   simp only [hge, ↓reduceDIte]
   refine ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun c i => harr c (by omega) i⟩
 | r + 1, k, hr, arr, st, hst, hT, hF, hkx, harr => by
   have hk : k < m := by omega
   have hm1 : m - (k + 1) = r := by omega
   unfold ber
   simp only [hk, ↓reduceDIte]
   set kf : Fin m := ⟨k, hk⟩
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, huv1, _, _, hin1⟩ :=
     bue_pr (S kf) kL xLit tL fL T_n st hst hT hF hkx
   set up := bue (S kf) kL xLit tL fL T_n st
   obtain ⟨hst2, hle2, hm2_v, hl2_c, hsub2, hdnw⟩ :=
     bde_pr up.1 (tL, fL) up.2 hst1 huv1 (hT.mono hle1) (hF.mono hle1)
   set dn := bde up.1 (tL, fL) up.2
   let arr' : Fin m → Fin n → LN V × LN V :=
     fun c => if c = kf then dn.1 else arr c
   have hT2 := hT.mono (le_trans hle1 hle2)
   have hF2 := hF.mono (le_trans hle1 hle2)
   have hkx2 : ∀ i, VL dn.2.1 (kL i) ∧ VL dn.2.1 (xLit i) :=
     fun i => ⟨(hkx i).1.mono (le_trans hle1 hle2), (hkx i).2.mono (le_trans hle1 hle2)⟩
   have harr' : ∀ c : Fin m, c.val < k + 1 → ∀ i, VL dn.2.1 (arr' c i).1 ∧ VL dn.2.1 (arr' c i).2 := by
     intro c hc i
     dsimp only [arr']
     split_ifs with heq
     · exact hdnw i
     · have hclt : c.val < k := by
         have hne : c.val ≠ k := fun h => heq (Fin.ext h)
         omega
       exact ⟨(harr c hclt i).1.mono (le_trans hle1 hle2), (harr c hclt i).2.mono (le_trans hle1 hle2)⟩
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     ber_pr m S kL xLit tL fL T_n r (k + 1) hm1 arr' dn.2
       hst2 hT2 hF2 hkx2 harr'
   have hd1 : dn.2.1 ≤ st.1 + 6 * T_n.intNodes := by
     have : up.1.intNodes = T_n.intNodes := hin1
     omega
   have hd2 : dn.2.2.length ≤ st.2.length + 21 * T_n.intNodes := by
     have : up.1.intNodes = T_n.intNodes := hin1
     omega
   refine ⟨r1, le_trans (le_trans hle1 hle2) r2, ?_, ?_, fun C hC => r5 C (hsub2 C (hsub1 C hC)), r6⟩
   · calc (ber m S kL xLit tL fL T_n (k + 1) arr' dn.2).2.1
       _ ≤ dn.2.1 + 6 * T_n.intNodes * r := r3
       _ ≤ (st.1 + 6 * T_n.intNodes) + 6 * T_n.intNodes * r := Nat.add_le_add_right hd1 _
       _ = st.1 + 6 * T_n.intNodes * (r + 1) := by ring
   · calc (ber m S kL xLit tL fL T_n (k + 1) arr' dn.2).2.2.length
       _ ≤ dn.2.2.length + 21 * T_n.intNodes * r := r4
       _ ≤ (st.2.length + 21 * T_n.intNodes) + 21 * T_n.intNodes * r := Nat.add_le_add_right hd2 _
       _ = st.2.length + 21 * T_n.intNodes * (r + 1) := by ring

lemma ber_uc {V : Type} [DecidableEq V] {n : ℕ} (m : ℕ)
   (S : Fin m → Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) (T_n : BTree (Fin n)) :
   ∀ (r k : ℕ) (hr : m - k = r) (arr : Fin m → Fin n → LN V × LN V)
     (st : St V) (c : Fin m), c.val < k →
     (ber m S kL xLit tL fL T_n k arr st).1 c = arr c
 | 0, k, hr, arr, st, c, _ => by
   have hge : ¬ (k < m) := by omega
   unfold ber; simp only [hge, ↓reduceDIte]
 | r + 1, k, hr, arr, st, c, hc => by
   have hk : k < m := by omega
   have hm1 : m - (k + 1) = r := by omega
   unfold ber; simp only [hk, ↓reduceDIte]
   have hne : c ≠ ⟨k, hk⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [ber_uc m S kL xLit tL fL T_n r (k + 1) hm1 _ _ c (by omega)]
   simp [hne]

lemma ber_sat {V : Type} [DecidableEq V] {n : ℕ} (m : ℕ)
   (S : Fin m → Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) (T_n : BTree (Fin n)) (hnd : T_n.leaves.Nodup) :
   ∀ (r k : ℕ) (hr : m - k = r) (arr : Fin m → Fin n → LN V × LN V)
     (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     (∀ c : Fin m, c.val < k → ∀ i, VL st.1 (arr c i).1 ∧ VL st.1 (arr c i).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α tL = true → lEv α fL = false →
     (∀ i, lEv α (kL i) = true) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (ber m S kL xLit tL fL T_n k arr st).2.2, ClauseSat α' C) ∧
       ∀ c : Fin m, k ≤ c.val → ∀ j ∈ T_n.leaves,
         lEv α' ((ber m S kL xLit tL fL T_n k arr st).1 c j).1 = true ∧
         lEv α' ((ber m S kL xLit tL fL T_n k arr st).1 c j).2 =
           xl ((T_n.leaves.filter (· ≠ j)).map (fun q => if S c q then lEv α (xLit q) else false))
 | 0, k, hr, arr, st, α, _, _, _, _, _, hsat, _, _, _ => by
   have hge : ¬ (k < m) := by omega
   unfold ber
   simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun c hc => by exfalso; omega⟩
 | r + 1, k, hr, arr, st, α, hst, hT, hF, hkx, harr, hsat, hTv, hFv, hKv => by
   have hk : k < m := by omega
   have hm1 : m - (k + 1) = r := by omega
   unfold ber
   simp only [hk, ↓reduceDIte]
   set kf : Fin m := ⟨k, hk⟩
   obtain ⟨hst1, hle1, _, _, _, huv1, hlv1, _, _⟩ :=
     bue_pr (S kf) kL xLit tL fL T_n st hst hT hF hkx
   set up := bue (S kf) kL xLit tL fL T_n st
   obtain ⟨α1, h1inl, h1lt, h1sat, h1up⟩ :=
     bue_sat (S kf) kL xLit tL fL T_n st α hst hT hF hkx hsat hTv hFv hKv
   have hT1 := hT.mono hle1
   have hF1 := hF.mono hle1
   have hTv1 : lEv α1 tL = true := (lecl h1inl h1lt hT).trans hTv
   have hFv1 : lEv α1 fL = false := (lecl h1inl h1lt hF).trans hFv
   have hnd1 : up.1.leaves.Nodup := by rw [hlv1]; exact hnd
   obtain ⟨α2, h2inl, h2lt, h2sat, h2dn⟩ :=
     bde_sat (S kf) (fun i => lEv α (xLit i)) up.1 (tL, fL) up.2 α1 false
       hst1 huv1 hT1 hF1 hnd1 h1up hTv1 hFv1 h1sat
   obtain ⟨hst2, hle2, _, _, _, hdnw⟩ :=
     bde_pr up.1 (tL, fL) up.2 hst1 huv1 hT1 hF1
   set dn := bde up.1 (tL, fL) up.2
   let arr' : Fin m → Fin n → LN V × LN V :=
     fun c => if c = kf then dn.1 else arr c
   have hT2 := hT.mono (le_trans hle1 hle2)
   have hF2 := hF.mono (le_trans hle1 hle2)
   have hkx2 : ∀ i, VL dn.2.1 (kL i) ∧ VL dn.2.1 (xLit i) :=
     fun i => ⟨(hkx i).1.mono (le_trans hle1 hle2), (hkx i).2.mono (le_trans hle1 hle2)⟩
   have harr' : ∀ c : Fin m, c.val < k + 1 → ∀ i, VL dn.2.1 (arr' c i).1 ∧ VL dn.2.1 (arr' c i).2 := by
     intro c hc i
     dsimp only [arr']
     split_ifs with heq
     · exact hdnw i
     · have hclt : c.val < k := by
         have hne : c.val ≠ k := fun h => heq (Fin.ext h)
         omega
       exact ⟨(harr c hclt i).1.mono (le_trans hle1 hle2), (harr c hclt i).2.mono (le_trans hle1 hle2)⟩
   have hTv2 : lEv α2 tL = true := (lecl h2inl h2lt hT1).trans hTv1
   have hFv2 : lEv α2 fL = false := (lecl h2inl h2lt hF1).trans hFv1
   have hKv2 : ∀ i, lEv α2 (kL i) = true := fun i =>
     (lecl h2inl h2lt ((hkx i).1.mono hle1)).trans
       ((lecl h1inl h1lt (hkx i).1).trans (hKv i))
   have hxv2 : (fun i => lEv α2 (xLit i)) = (fun i => lEv α (xLit i)) := by
     ext i
     exact (lecl h2inl h2lt ((hkx i).2.mono hle1)).trans (lecl h1inl h1lt (hkx i).2)
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     ber_sat m S kL xLit tL fL T_n hnd r (k + 1) hm1 arr' dn.2 α2
       hst2 hT2 hF2 hkx2 harr' h2sat hTv2 hFv2 hKv2
   refine ⟨α', fun v => (h'inl v).trans ((h2inl v).trans (h1inl v)), fun w hw => ?_, h'sat, fun c hc j hj => ?_⟩
   · exact (h'lt w (lt_of_lt_of_le hw (le_trans hle1 hle2))).trans ((h2lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw))
   · by_cases heq : k = c.val
     · have hceq : c = kf := Fin.ext heq.symm
       subst hceq
       rw [ber_uc m S kL xLit tL fL T_n r (k + 1) hm1 arr' dn.2 kf (by change kf.val < k + 1; omega)]
       dsimp only [arr']
       rw [if_pos rfl]
       have he1 := lecl h'inl h'lt (hdnw j).1
       have he2 := lecl h'inl h'lt (hdnw j).2
       have hj1 : j ∈ up.1.leaves := by rw [hlv1]; exact hj
       obtain ⟨hd1, hd2⟩ := h2dn j hj1
       rw [hlv1] at hd2
       simpa [he1, he2, hd1, hd2]
     · have hk1 : k + 1 ≤ c.val := by omega
       have hxv2_pt : ∀ q, lEv α2 (xLit q) = lEv α (xLit q) := congrFun hxv2
       have h'res' := h'res c hk1 j hj
       simp only [hxv2_pt] at h'res'
       exact h'res'

lemma ber_up {V : Type} [DecidableEq V] {n : ℕ} (m : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (S : Fin m → Fin n → Bool) (kL xLit : Fin n → LN V)
   (tL fL : LN V) (T_n : BTree (Fin n)) (hnd : T_n.leaves.Nodup)
   (x : Fin n → Bool) (j : Fin n) (hj : j ∈ T_n.leaves) :
   ∀ (r k : ℕ) (hr : m - k = r) (arr : Fin m → Fin n → LN V × LN V)
     (st : St V) (c : Fin m),
     k ≤ c.val →
     (∀ C ∈ (ber m S kL xLit tL fL T_n k arr st).2.2, C ∈ F) →
     tL ∈ (upS F)^[1] seed →
     negL fL ∈ (upS F)^[1] seed →
     (∀ q, q ≠ j → S c q = true →
       kL q ∈ (upS F)^[1] seed ∧ fLt (xLit q) (x q) ∈ (upS F)^[1] seed) →
     ((ber m S kL xLit tL fL T_n k arr st).1 c j).1 ∈
         (upS F)^[2 * T_n.depth + 1] seed ∧
     fLt ((ber m S kL xLit tL fL T_n k arr st).1 c j).2
         (xl ((T_n.leaves.filter (· ≠ j)).map (fun q => if S c q then x q else false))) ∈
         (upS F)^[2 * T_n.depth + 1] seed
 | 0, k, hr, _, _, c, hkc, _, _, _, _ => by exfalso; omega
 | r + 1, k, hr, arr, st, c, hkc, hF, hT, hF_lit, hkx => by
   have hk : k < m := by omega
   have hm1 : m - (k + 1) = r := by omega
   unfold ber at hF ⊢
   simp only [hk, ↓reduceDIte] at hF ⊢
   set kf : Fin m := ⟨k, hk⟩
   set up := bue (S kf) kL xLit tL fL T_n st
   set dn := bde up.1 (tL, fL) up.2
   let arr' : Fin m → Fin n → LN V × LN V :=
     fun c' => if c' = kf then dn.1 else arr c'
   by_cases heq : k = c.val
   · have hceq : c = kf := Fin.ext heq.symm
     subst hceq
     rw [ber_uc m S kL xLit tL fL T_n r (k + 1) hm1 arr' dn.2 kf (by change kf.val < k + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hFdn : ∀ C ∈ dn.2.2, C ∈ F := fun C hC =>
       hF C (ber_cm m S kL xLit tL fL T_n r (k + 1) hm1 arr' dn.2 C hC)
     have hFup : ∀ C ∈ up.2.2, C ∈ F := fun C hC =>
       hFdn C (bde_cm up.1 (tL, fL) up.2 C hC)
     have hup_pr := bue_leaves_depth (S kf) kL xLit tL fL T_n st
     have hRl := bue_up F seed (S kf) x j kL xLit tL fL T_n st hFup hT hF_lit hkx
     have hj1 : j ∈ up.1.leaves := by rw [hup_pr.1]; exact hj
     have hnd1 : up.1.leaves.Nodup := by rw [hup_pr.1]; exact hnd
     have hdep1 : up.1.depth ≤ T_n.depth := by rw [hup_pr.2]
     have hT_d : tL ∈ (upS F)^[T_n.depth + 1 + 0] seed :=
       upStep_iter_le F seed (by omega) hT
     have hF_d : fLt fL false ∈ (upS F)^[T_n.depth + 1 + 0] seed := by
       have h1 : negL fL ∈ (upS F)^[T_n.depth + 1 + 0] seed := upStep_iter_le F seed (by omega) hF_lit
       simpa [fLt] using h1
     obtain ⟨hd1, hd2⟩ := bde_up F seed (S kf) x j T_n.depth up.1 (tL, fL) up.2 0 false
       hFdn hRl hj1 hnd1 hdep1 hT_d hF_d
     have hup_leaves : up.1.leaves = T_n.leaves := hup_pr.1
     have hup_depth : up.1.depth = T_n.depth := hup_pr.2
     rw [hup_depth] at hd1 hd2
     rw [hup_leaves] at hd2
     simpa [show T_n.depth + 1 + 0 + T_n.depth = 2 * T_n.depth + 1 by omega] using And.intro hd1 hd2
   · have hk1 : k + 1 ≤ c.val := by omega
     exact ber_up m F seed S kL xLit tL fL T_n hnd x j hj
       r (k + 1) hm1 arr' dn.2 c hk1 hF hT hF_lit hkx

def bfr {V : Type} [DecidableEq V] (n h' : ℕ)
   (S : Fin (2 ^ h') → Fin n → Bool)
   (exclOut : Fin (2 ^ h') → Fin n → LN V × LN V) :
   ℕ → (Fin n → Fin (2 ^ h') → Bool → LN V) → St V →
     (Fin n → Fin (2 ^ h') → Bool → LN V) × St V
 | i, arr, st =>
   if hi : i < n then
     let ifin : Fin n := ⟨i, hi⟩
     let bf := bbf h' (fun c => S c ifin)
       (fun c => (exclOut c ifin).1) (fun c => (exclOut c ifin).2) st
     let arr' : Fin n → Fin (2 ^ h') → Bool → LN V :=
       fun j => if j = ifin then bf.1 else arr j
     bfr n h' S exclOut (i + 1) arr' bf.2
   else (arr, st)
termination_by i => n - i

lemma bbf_cm {V : Type} [DecidableEq V] (h' : ℕ)
   (S : Fin (2 ^ h') → Bool) (iso const : Fin (2 ^ h') → LN V)
   (st : St V) (C : CN V) (hC : C ∈ st.2) :
   C ∈ (bbf h' S iso const st).2.2 := by
 dsimp only [bbf]
 exact bbl_cm h' h' 0 (Nat.sub_zero _) _ _ C
   (bbfi_cm (2 ^ h') S iso const _ (2 ^ h') 0 (Nat.sub_zero _) (st.1 + 2 * 2 ^ h', st.2) C hC)

lemma bfr_cm {V : Type} [DecidableEq V] (n h' : ℕ)
   (S : Fin (2 ^ h') → Fin n → Bool)
   (exclOut : Fin (2 ^ h') → Fin n → LN V × LN V) :
   ∀ (r i : ℕ) (hr : n - i = r) (arr : Fin n → Fin (2 ^ h') → Bool → LN V)
     (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bfr n h' S exclOut i arr st).2.2
 | 0, i, hr, arr, st, C, hC => by
   have hge : ¬ (i < n) := by omega
   unfold bfr; simp only [hge, ↓reduceDIte]; exact hC
 | r + 1, i, hr, arr, st, C, hC => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bfr; simp only [hi, ↓reduceDIte]
   apply bfr_cm n h' S exclOut r (i + 1) hm1 _ _ C
   exact bbf_cm h' _ _ _ st C hC

lemma bfr_uc {V : Type} [DecidableEq V] (n h' : ℕ)
   (S : Fin (2 ^ h') → Fin n → Bool)
   (exclOut : Fin (2 ^ h') → Fin n → LN V × LN V) :
   ∀ (r i : ℕ) (hr : n - i = r) (arr : Fin n → Fin (2 ^ h') → Bool → LN V)
     (st : St V) (j : Fin n), j.val < i →
     (bfr n h' S exclOut i arr st).1 j = arr j
 | 0, i, hr, arr, st, j, _ => by
   have hge : ¬ (i < n) := by omega
   unfold bfr; simp only [hge, ↓reduceDIte]
 | r + 1, i, hr, arr, st, j, hj => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bfr; simp only [hi, ↓reduceDIte]
   have hne : j ≠ ⟨i, hi⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [bfr_uc n h' S exclOut r (i + 1) hm1 _ _ j (by omega)]
   simp [hne]

lemma bfr_pr {V : Type} [DecidableEq V] (n h' : ℕ)
   (S : Fin (2 ^ h') → Fin n → Bool)
   (exclOut : Fin (2 ^ h') → Fin n → LN V × LN V) :
   ∀ (r i : ℕ) (hr : n - i = r) (arr : Fin n → Fin (2 ^ h') → Bool → LN V)
     (st : St V),
     VS st →
     (∀ c j, VL st.1 (exclOut c j).1 ∧ VL st.1 (exclOut c j).2) →
     (∀ j : Fin n, j.val < i → ∀ s b, VL st.1 (arr j s b)) →
     let res := bfr n h' S exclOut i arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + ((4 + 2 * h') * 2 ^ h') * r ∧
     res.2.2.length ≤ st.2.length + ((4 + 4 * h') * 2 ^ h') * r ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ j s b, VL res.2.1 (res.1 j s b))
 | 0, i, hr, arr, st, hst, _, harr => by
   have hge : ¬ (i < n) := by omega
   unfold bfr; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun j => harr j (by omega)⟩
 | r + 1, i, hr, arr, st, hst, hexcl, harr => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bfr; simp only [hi, ↓reduceDIte]
   set ifin : Fin n := ⟨i, hi⟩
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hbfw⟩ :=
     bbf_pr h' (fun c => S c ifin) (fun c => (exclOut c ifin).1)
       (fun c => (exclOut c ifin).2) st hst (fun c => hexcl c ifin)
   set bf := bbf h' (fun c => S c ifin) (fun c => (exclOut c ifin).1)
     (fun c => (exclOut c ifin).2) st
   let arr' : Fin n → Fin (2 ^ h') → Bool → LN V :=
     fun j => if j = ifin then bf.1 else arr j
   have hexcl1 : ∀ c j, VL bf.2.1 (exclOut c j).1 ∧ VL bf.2.1 (exclOut c j).2 :=
     fun c j => ⟨(hexcl c j).1.mono hle1, (hexcl c j).2.mono hle1⟩
   have harr' : ∀ j : Fin n, j.val < i + 1 → ∀ s b, VL bf.2.1 (arr' j s b) := by
     intro j hj s b
     dsimp only [arr']
     split_ifs with heq
     · exact hbfw s b
     · have hjlt : j.val < i := by
         have hne : j.val ≠ i := fun h => heq (Fin.ext h)
         omega
       exact (harr j hjlt s b).mono hle1
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     bfr_pr n h' S exclOut r (i + 1) hm1 arr' bf.2 hst1 hexcl1 harr'
   refine ⟨r1, le_trans hle1 r2, ?_, ?_, fun C hC => r5 C (hsub1 C hC), r6⟩
   · calc (bfr n h' S exclOut (i + 1) arr' bf.2).2.1
       _ ≤ bf.2.1 + ((4 + 2 * h') * 2 ^ h') * r := r3
       _ ≤ (st.1 + (4 + 2 * h') * 2 ^ h') + ((4 + 2 * h') * 2 ^ h') * r := Nat.add_le_add_right hm1_v _
       _ = st.1 + ((4 + 2 * h') * 2 ^ h') * (r + 1) := by ring
   · calc (bfr n h' S exclOut (i + 1) arr' bf.2).2.2.length
       _ ≤ bf.2.2.length + ((4 + 4 * h') * 2 ^ h') * r := r4
       _ ≤ (st.2.length + (4 + 4 * h') * 2 ^ h') + ((4 + 4 * h') * 2 ^ h') * r := Nat.add_le_add_right hl1_c _
       _ = st.2.length + ((4 + 4 * h') * 2 ^ h') * (r + 1) := by ring

open Classical in
lemma bfr_sat {V : Type} [DecidableEq V] (n h' : ℕ)
   (S : Fin (2 ^ h') → Fin n → Bool)
   (exclOut : Fin (2 ^ h') → Fin n → LN V × LN V)
   (constVal : Fin n → Fin (2 ^ h') → Bool) :
   ∀ (r i : ℕ) (hr : n - i = r) (arr : Fin n → Fin (2 ^ h') → Bool → LN V)
     (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ c j, VL st.1 (exclOut c j).1 ∧ VL st.1 (exclOut c j).2) →
     (∀ j : Fin n, j.val < i → ∀ s b, VL st.1 (arr j s b)) →
     (∀ c j, lEv α (exclOut c j).1 = true → lEv α (exclOut c j).2 = constVal j c) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ q < st.1, α' (Sum.inr q) = α (Sum.inr q)) ∧
       (∀ C ∈ (bfr n h' S exclOut i arr st).2.2, ClauseSat α' C) ∧
       ∀ j : Fin n, i ≤ j.val → ∀ s b,
         lEv α' ((bfr n h' S exclOut i arr st).1 j s b) =
           decide (∃ c : Fin (2 ^ h'), S c j = true ∧ (constVal j c ^^ db h' c.val s.val) = b)
 | 0, i, hr, arr, st, α, _, _, _, _, hsat => by
   have hge : ¬ (i < n) := by omega
   unfold bfr; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun j hj => by exfalso; omega⟩
 | r + 1, i, hr, arr, st, α, hst, hexcl, harr, hic, hsat => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bfr; simp only [hi, ↓reduceDIte]
   set ifin : Fin n := ⟨i, hi⟩
   obtain ⟨hst1, hle1, _, _, _, hbfw⟩ :=
     bbf_pr h' (fun c => S c ifin) (fun c => (exclOut c ifin).1)
       (fun c => (exclOut c ifin).2) st hst (fun c => hexcl c ifin)
   obtain ⟨α1, h1inl, h1lt, h1sat, h1bf⟩ :=
     bbf_sat h' (fun c => S c ifin) (fun c => (exclOut c ifin).1)
       (fun c => (exclOut c ifin).2) st α (constVal ifin) hst (fun c => hexcl c ifin)
       (fun c => hic c ifin) hsat
   set bf := bbf h' (fun c => S c ifin) (fun c => (exclOut c ifin).1)
     (fun c => (exclOut c ifin).2) st
   let arr' : Fin n → Fin (2 ^ h') → Bool → LN V :=
     fun j => if j = ifin then bf.1 else arr j
   have hexcl1 : ∀ c j, VL bf.2.1 (exclOut c j).1 ∧ VL bf.2.1 (exclOut c j).2 :=
     fun c j => ⟨(hexcl c j).1.mono hle1, (hexcl c j).2.mono hle1⟩
   have harr' : ∀ j : Fin n, j.val < i + 1 → ∀ s b, VL bf.2.1 (arr' j s b) := by
     intro j hj s b
     dsimp only [arr']
     split_ifs with heq
     · exact hbfw s b
     · have hjlt : j.val < i := by
         have hne : j.val ≠ i := fun h => heq (Fin.ext h)
         omega
       exact (harr j hjlt s b).mono hle1
   have hic1 : ∀ c j, lEv α1 (exclOut c j).1 = true → lEv α1 (exclOut c j).2 = constVal j c := by
     intro c j h1
     rw [lecl h1inl h1lt (hexcl c j).1] at h1
     rw [lecl h1inl h1lt (hexcl c j).2]
     exact hic c j h1
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     bfr_sat n h' S exclOut constVal r (i + 1) hm1 arr' bf.2 α1
       hst1 hexcl1 harr' hic1 h1sat
   refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun q hq => ?_, h'sat, fun j hj s b => ?_⟩
   · exact (h'lt q (lt_of_lt_of_le hq hle1)).trans (h1lt q hq)
   · by_cases heq : i = j.val
     · have hjeq : j = ifin := Fin.ext heq.symm
       subst hjeq
       rw [bfr_uc n h' S exclOut r (i + 1) hm1 arr' bf.2 ifin (by change ifin.val < i + 1; omega)]
       dsimp only [arr']
       rw [if_pos rfl]
       rw [lecl h'inl h'lt (hbfw s b)]
       exact h1bf s b
     · exact h'res j (by omega) s b

lemma bfr_up {V : Type} [DecidableEq V] (n h' : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (S : Fin (2 ^ h') → Fin n → Bool)
   (exclOut : Fin (2 ^ h') → Fin n → LN V × LN V)
   (d0 : ℕ) (c s : Fin (2 ^ h')) (j : Fin n) (val0 : Bool) :
   ∀ (r i : ℕ) (hr : n - i = r) (arr : Fin n → Fin (2 ^ h') → Bool → LN V)
     (st : St V),
     i ≤ j.val →
     VS st →
     (∀ c' j', VL st.1 (exclOut c' j').1 ∧ VL st.1 (exclOut c' j').2) →
     (∀ C ∈ (bfr n h' S exclOut i arr st).2.2, C ∈ F) →
     S c j = true →
     (exclOut c j).1 ∈ (upS F)^[d0] seed →
     fLt (exclOut c j).2 val0 ∈ (upS F)^[d0] seed →
     (bfr n h' S exclOut i arr st).1 j s (val0 ^^ db h' c.val s.val) ∈
       (upS F)^[d0 + 2 + h'] seed
 | 0, i, hr, _, _, hij, _, _, _, _, _, _ => by exfalso; omega
 | r + 1, i, hr, arr, st, hij, hst, hexcl, hF, hScj, hiso, hconst => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bfr at hF ⊢
   simp only [hi, ↓reduceDIte] at hF ⊢
   set ifin : Fin n := ⟨i, hi⟩
   obtain ⟨hst1, hle1, _, _, _, _⟩ :=
     bbf_pr h' (fun c' => S c' ifin) (fun c' => (exclOut c' ifin).1)
       (fun c' => (exclOut c' ifin).2) st hst (fun c' => hexcl c' ifin)
   set bf := bbf h' (fun c' => S c' ifin) (fun c' => (exclOut c' ifin).1)
     (fun c' => (exclOut c' ifin).2) st
   let arr' : Fin n → Fin (2 ^ h') → Bool → LN V :=
     fun j' => if j' = ifin then bf.1 else arr j'
   by_cases heq : i = j.val
   · have hjeq : j = ifin := Fin.ext heq.symm
     subst hjeq
     rw [bfr_uc n h' S exclOut r (i + 1) hm1 arr' bf.2 ifin (by change ifin.val < i + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hFbf : ∀ C ∈ bf.2.2, C ∈ F := fun C hC =>
       hF C (bfr_cm n h' S exclOut r (i + 1) hm1 arr' bf.2 C hC)
     exact bbf_up h' F seed (fun c' => S c' ifin) (fun c' => (exclOut c' ifin).1)
       (fun c' => (exclOut c' ifin).2) st d0 c s val0 hst (fun c' => hexcl c' ifin) hFbf hScj hiso hconst
   · have hexcl1 : ∀ c' j', VL bf.2.1 (exclOut c' j').1 ∧ VL bf.2.1 (exclOut c' j').2 :=
       fun c' j' => ⟨(hexcl c' j').1.mono hle1, (hexcl c' j').2.mono hle1⟩
     exact bfr_up n h' F seed S exclOut d0 c s j val0 r (i + 1) hm1 arr' bf.2
       (by omega) hst1 hexcl1 hF hScj hiso hconst

def bam {V : Type} [DecidableEq V] (n h' R : ℕ)
   (H : Fin R → Fin h' → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) :
   ℕ → (Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) → St V →
     (Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) × St V
 | r, arr, st =>
   if hr : r < R then
     let rf : Fin R := ⟨r, hr⟩
     let S : Fin (2 ^ h') → Fin n → Bool :=
       fun c j => xl (List.ofFn (fun q : Fin h' => decide (c.val.testBit q.val) && H rf q j))
     let dummyExcl : Fin (2 ^ h') → Fin n → LN V × LN V := fun _ _ => (tL, fL)
     let resExcl := ber (2 ^ h') S kL xLit tL fL T_n 0 dummyExcl st
     let dummyW : Fin n → Fin (2 ^ h') → Bool → LN V := fun _ _ _ => tL
     let resBfly := bfr n h' S resExcl.1 0 dummyW resExcl.2
     let arr' : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V :=
       fun r' => if r' = rf then resBfly.1 else arr r'
     bam n h' R H kL xLit tL fL T_n (r + 1) arr' resBfly.2
   else (arr, st)
termination_by r => R - r

lemma bam_cm {V : Type} [DecidableEq V] (n h' R : ℕ)
   (H : Fin R → Fin h' → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) :
   ∀ (m r : ℕ) (_ : R - r = m)
     (arr : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bam n h' R H kL xLit tL fL T_n r arr st).2.2
 | 0, r, hm, arr, st, C, hC => by
   have hge : ¬ (r < R) := by omega
   unfold bam; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, r, hm, arr, st, C, hC => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bam; simp only [hr, ↓reduceDIte]
   apply bam_cm n h' R H kL xLit tL fL T_n m (r + 1) hm1 _ _ C
   apply bfr_cm n h' _ _ n 0 (Nat.sub_zero _) _ _ C
   apply ber_cm (2 ^ h') _ _ _ _ _ _ (2 ^ h') 0 (Nat.sub_zero _) _ _ C hC

lemma bam_uc {V : Type} [DecidableEq V] (n h' R : ℕ)
   (H : Fin R → Fin h' → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) :
   ∀ (m r : ℕ) (_ : R - r = m)
     (arr : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) (st : St V) (rf : Fin R),
     rf.val < r →
     (bam n h' R H kL xLit tL fL T_n r arr st).1 rf = arr rf
 | 0, r, hm, arr, st, rf, _ => by
   have hge : ¬ (r < R) := by omega
   unfold bam; simp only [hge, ↓reduceDIte]
 | m + 1, r, hm, arr, st, rf, hrf => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bam; simp only [hr, ↓reduceDIte]
   have hne : rf ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [bam_uc n h' R H kL xLit tL fL T_n m (r + 1) hm1 _ _ rf (by omega)]
   simp [hne]

lemma bam_pr {V : Type} [DecidableEq V] (n h' R : ℕ)
   (H : Fin R → Fin h' → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) :
   ∀ (m r : ℕ) (_ : R - r = m)
     (arr : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) (st : St V),
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     (∀ rf : Fin R, rf.val < r → ∀ j s b, VL st.1 (arr rf j s b)) →
     let res := bam n h' R H kL xLit tL fL T_n r arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * m ∧
     res.2.2.length ≤ st.2.length + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * m ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ rf j s b, VL res.2.1 (res.1 rf j s b))
 | 0, r, hm, arr, st, hst, _, _, _, harr => by
   have hge : ¬ (r < R) := by omega
   unfold bam; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun rf => harr rf (by omega)⟩
 | m + 1, r, hm, arr, st, hst, hT, hF, hkx, harr => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bam; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   let S : Fin (2 ^ h') → Fin n → Bool :=
     fun c j => xl (List.ofFn (fun q : Fin h' => decide (c.val.testBit q.val) && H rf q j))
   let dummyExcl : Fin (2 ^ h') → Fin n → LN V × LN V := fun _ _ => (tL, fL)
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hexcl1⟩ :=
     ber_pr (2 ^ h') S kL xLit tL fL T_n (2 ^ h') 0 (Nat.sub_zero _)
       dummyExcl st hst hT hF hkx (fun c hc => by exfalso; omega)
   set resExcl := ber (2 ^ h') S kL xLit tL fL T_n 0 dummyExcl st
   let dummyW : Fin n → Fin (2 ^ h') → Bool → LN V := fun _ _ _ => tL
   obtain ⟨hst2, hle2, hm2_v, hl2_c, hsub2, hw2⟩ :=
     bfr_pr n h' S resExcl.1 n 0 (Nat.sub_zero _) dummyW resExcl.2 hst1
       hexcl1 (fun j hj => by exfalso; omega)
   set resBfly := bfr n h' S resExcl.1 0 dummyW resExcl.2
   let arr' : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V :=
     fun r' => if r' = rf then resBfly.1 else arr r'
   have hT2 := hT.mono (le_trans hle1 hle2)
   have hF2 := hF.mono (le_trans hle1 hle2)
   have hkx2 : ∀ i, VL resBfly.2.1 (kL i) ∧ VL resBfly.2.1 (xLit i) :=
     fun i => ⟨(hkx i).1.mono (le_trans hle1 hle2), (hkx i).2.mono (le_trans hle1 hle2)⟩
   have harr' : ∀ r' : Fin R, r'.val < r + 1 → ∀ j s b, VL resBfly.2.1 (arr' r' j s b) := by
     intro r' hr' j s b
     dsimp only [arr']
     split_ifs with heq
     · exact hw2 j s b
     · have hlt : r'.val < r := by
         have hne : r'.val ≠ r := fun h => heq (Fin.ext h)
         omega
       exact (harr r' hlt j s b).mono (le_trans hle1 hle2)
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     bam_pr n h' R H kL xLit tL fL T_n m (r + 1) hm1 arr' resBfly.2
       hst2 hT2 hF2 hkx2 harr'
   refine ⟨r1, le_trans (le_trans hle1 hle2) r2, ?_, ?_, fun C hC => r5 C (hsub2 C (hsub1 C hC)), r6⟩
   · have ha : resBfly.2.1 ≤ st.1 + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) := by
       calc resBfly.2.1 ≤ resExcl.2.1 + ((4 + 2 * h') * 2 ^ h') * n := hm2_v
         _ ≤ (st.1 + 6 * T_n.intNodes * 2 ^ h') + ((4 + 2 * h') * 2 ^ h') * n := Nat.add_le_add_right hm1_v _
         _ = st.1 + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) := by ring
     calc (bam n h' R H kL xLit tL fL T_n (r + 1) arr' resBfly.2).2.1
       _ ≤ resBfly.2.1 + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * m := r3
       _ ≤ (st.1 + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n)) +
           (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * m := Nat.add_le_add_right ha _
       _ = st.1 + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * (m + 1) := by ring
   · have hb : resBfly.2.2.length ≤ st.2.length + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) := by
       calc resBfly.2.2.length ≤ resExcl.2.2.length + ((4 + 4 * h') * 2 ^ h') * n := hl2_c
         _ ≤ (st.2.length + 21 * T_n.intNodes * 2 ^ h') + ((4 + 4 * h') * 2 ^ h') * n := Nat.add_le_add_right hl1_c _
         _ = st.2.length + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) := by ring
     calc (bam n h' R H kL xLit tL fL T_n (r + 1) arr' resBfly.2).2.2.length
       _ ≤ resBfly.2.2.length + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * m := r4
       _ ≤ (st.2.length + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n)) +
           (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * m := Nat.add_le_add_right hb _
       _ = st.2.length + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * (m + 1) := by ring

open Classical in
lemma bam_sat {V : Type} [DecidableEq V] (n h' R : ℕ)
   (H : Fin R → Fin h' → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) (hnd : T_n.leaves.Nodup) (hsub : ∀ j : Fin n, j ∈ T_n.leaves) :
   ∀ (m r : ℕ) (_ : R - r = m)
     (arr : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     (∀ rf : Fin R, rf.val < r → ∀ j s b, VL st.1 (arr rf j s b)) →
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α tL = true → lEv α fL = false →
     (∀ i, lEv α (kL i) = true) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (bam n h' R H kL xLit tL fL T_n r arr st).2.2, ClauseSat α' C) ∧
       ∀ rf : Fin R, r ≤ rf.val → ∀ j s b,
         let S : Fin (2 ^ h') → Fin n → Bool :=
           fun c q => xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q))
         let constVal : Fin n → Fin (2 ^ h') → Bool := fun i c =>
           xl ((T_n.leaves.filter (· ≠ i)).map (fun q => if S c q then lEv α (xLit q) else false))
         lEv α' ((bam n h' R H kL xLit tL fL T_n r arr st).1 rf j s b) =
           decide (∃ c : Fin (2 ^ h'), S c j = true ∧ (constVal j c ^^ db h' c.val s.val) = b)
 | 0, r, hm, arr, st, α, _, _, _, _, _, hsat, _, _, _ => by
   have hge : ¬ (r < R) := by omega
   unfold bam; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun rf hrf => by exfalso; omega⟩
 | m + 1, r, hm, arr, st, α, hst, hT, hF, hkx, harr, hsat, hTv, hFv, hKv => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bam; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   let S : Fin (2 ^ h') → Fin n → Bool :=
     fun c q => xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q))
   let dummyExcl : Fin (2 ^ h') → Fin n → LN V × LN V := fun _ _ => (tL, fL)
   obtain ⟨hst1, hle1, _, _, _, hexcl1⟩ :=
     ber_pr (2 ^ h') S kL xLit tL fL T_n (2 ^ h') 0 (Nat.sub_zero _)
       dummyExcl st hst hT hF hkx (fun c hc => by exfalso; omega)
   obtain ⟨α1, h1inl, h1lt, h1sat, h1excl⟩ :=
     ber_sat (2 ^ h') S kL xLit tL fL T_n hnd (2 ^ h') 0 (Nat.sub_zero _)
       dummyExcl st α hst hT hF hkx (fun c hc => by exfalso; omega) hsat hTv hFv hKv
   set resExcl := ber (2 ^ h') S kL xLit tL fL T_n 0 dummyExcl st
   let constVal : Fin n → Fin (2 ^ h') → Bool := fun j c =>
     xl ((T_n.leaves.filter (· ≠ j)).map (fun q => if S c q then lEv α (xLit q) else false))
   let dummyW : Fin n → Fin (2 ^ h') → Bool → LN V := fun _ _ _ => tL
   obtain ⟨hst2, hle2, _, _, _, hw2⟩ :=
     bfr_pr n h' S resExcl.1 n 0 (Nat.sub_zero _) dummyW resExcl.2 hst1
       hexcl1 (fun j hj => by exfalso; omega)
   obtain ⟨α2, h2inl, h2lt, h2sat, h2bf⟩ :=
     bfr_sat n h' S resExcl.1 constVal n 0 (Nat.sub_zero _) dummyW resExcl.2 α1
       hst1 hexcl1 (fun j hj => by exfalso; omega)
       (fun c j _ => (h1excl c (Nat.zero_le _) j (hsub j)).2) h1sat
   set resBfly := bfr n h' S resExcl.1 0 dummyW resExcl.2
   let arr' : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V :=
     fun r' => if r' = rf then resBfly.1 else arr r'
   have hT2 := hT.mono (le_trans hle1 hle2)
   have hF2 := hF.mono (le_trans hle1 hle2)
   have hkx2 : ∀ i, VL resBfly.2.1 (kL i) ∧ VL resBfly.2.1 (xLit i) :=
     fun i => ⟨(hkx i).1.mono (le_trans hle1 hle2), (hkx i).2.mono (le_trans hle1 hle2)⟩
   have harr' : ∀ r' : Fin R, r'.val < r + 1 → ∀ j s b, VL resBfly.2.1 (arr' r' j s b) := by
     intro r' hr' j s b
     dsimp only [arr']
     split_ifs with heq
     · exact hw2 j s b
     · have hlt : r'.val < r := by
         have hne : r'.val ≠ r := fun h => heq (Fin.ext h)
         omega
       exact (harr r' hlt j s b).mono (le_trans hle1 hle2)
   have hTv2 : lEv α2 tL = true :=
     (lecl h2inl h2lt (hT.mono hle1)).trans ((lecl h1inl h1lt hT).trans hTv)
   have hFv2 : lEv α2 fL = false :=
     (lecl h2inl h2lt (hF.mono hle1)).trans ((lecl h1inl h1lt hF).trans hFv)
   have hKv2 : ∀ i, lEv α2 (kL i) = true := fun i =>
     (lecl h2inl h2lt ((hkx i).1.mono hle1)).trans
       ((lecl h1inl h1lt (hkx i).1).trans (hKv i))
   have hxv2 : ∀ i, lEv α2 (xLit i) = lEv α (xLit i) := fun i =>
     (lecl h2inl h2lt ((hkx i).2.mono hle1)).trans (lecl h1inl h1lt (hkx i).2)
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     bam_sat n h' R H kL xLit tL fL T_n hnd hsub m (r + 1) hm1 arr'
       resBfly.2 α2 hst2 hT2 hF2 hkx2 harr' h2sat hTv2 hFv2 hKv2
   refine ⟨α', fun v => (h'inl v).trans ((h2inl v).trans (h1inl v)), fun w hw => ?_, h'sat, fun rf' hrf' j s b => ?_⟩
   · exact (h'lt w (lt_of_lt_of_le hw (le_trans hle1 hle2))).trans ((h2lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw))
   · by_cases heq : r = rf'.val
     · have hrfeq : rf' = rf := Fin.ext heq.symm
       subst hrfeq
       rw [bam_uc n h' R H kL xLit tL fL T_n m (r + 1) hm1 arr' resBfly.2 rf (by change rf.val < r + 1; omega)]
       dsimp only [arr']
       rw [if_pos rfl]
       rw [lecl h'inl h'lt (hw2 j s b)]
       exact h2bf j (Nat.zero_le _) s b
     · have hrf1 := h'res rf' (by omega) j s b
       simpa only [hxv2] using hrf1

lemma bam_up {V : Type} [DecidableEq V] (n h' R : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (H : Fin R → Fin h' → Fin n → Bool)
   (kL xLit : Fin n → LN V) (tL fL : LN V)
   (T_n : BTree (Fin n)) (hnd : T_n.leaves.Nodup) (x : Fin n → Bool)
   (rf : Fin R) (c s : Fin (2 ^ h')) (j : Fin n) (hj : j ∈ T_n.leaves) :
   ∀ (m r : ℕ) (_ : R - r = m)
     (arr : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V) (st : St V),
     r ≤ rf.val →
     VS st →
     VL st.1 tL → VL st.1 fL →
     (∀ i, VL st.1 (kL i) ∧ VL st.1 (xLit i)) →
     (∀ C ∈ (bam n h' R H kL xLit tL fL T_n r arr st).2.2, C ∈ F) →
     tL ∈ (upS F)^[1] seed →
     negL fL ∈ (upS F)^[1] seed →
     xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p j)) = true →
     (∀ q, q ≠ j →
       xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q)) = true →
       kL q ∈ (upS F)^[1] seed ∧ fLt (xLit q) (x q) ∈ (upS F)^[1] seed) →
     (bam n h' R H kL xLit tL fL T_n r arr st).1 rf j s
       (xl ((T_n.leaves.filter (· ≠ j)).map (fun q =>
         if xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q)) then x q else false))
         ^^ db h' c.val s.val) ∈
       (upS F)^[2 * T_n.depth + 3 + h'] seed
 | 0, r, hm, _, _, hrf, _, _, _, _, _, _, _, _, _ => by exfalso; omega
 | m + 1, r, hm, arr, st, hrf, hst, hT, hF, hkx, hF_all, hT_up, hF_up, hScj, hqx => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bam at hF_all ⊢
   simp only [hr, ↓reduceDIte] at hF_all ⊢
   set rf0 : Fin R := ⟨r, hr⟩
   let S : Fin (2 ^ h') → Fin n → Bool :=
     fun c' q => xl (List.ofFn (fun p : Fin h' => decide (c'.val.testBit p.val) && H rf0 p q))
   let dummyExcl : Fin (2 ^ h') → Fin n → LN V × LN V := fun _ _ => (tL, fL)
   obtain ⟨hst1, hle1, _, _, _, hexcl1⟩ :=
     ber_pr (2 ^ h') S kL xLit tL fL T_n (2 ^ h') 0 (Nat.sub_zero _)
       dummyExcl st hst hT hF hkx (fun c' hc' => by exfalso; omega)
   set resExcl := ber (2 ^ h') S kL xLit tL fL T_n 0 dummyExcl st
   let dummyW : Fin n → Fin (2 ^ h') → Bool → LN V := fun _ _ _ => tL
   obtain ⟨hst2, hle2, _, _, _, _⟩ :=
     bfr_pr n h' S resExcl.1 n 0 (Nat.sub_zero _) dummyW resExcl.2 hst1
       hexcl1 (fun j' hj' => by exfalso; omega)
   set resBfly := bfr n h' S resExcl.1 0 dummyW resExcl.2
   let arr' : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V :=
     fun r' => if r' = rf0 then resBfly.1 else arr r'
   by_cases heq : r = rf.val
   · have hrfeq : rf = rf0 := Fin.ext heq.symm
     subst hrfeq
     rw [bam_uc n h' R H kL xLit tL fL T_n m (r + 1) hm1 arr' resBfly.2 rf0 (by change rf0.val < r + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hF_bf : ∀ C ∈ resBfly.2.2, C ∈ F := fun C hC =>
       hF_all C (bam_cm n h' R H kL xLit tL fL T_n m (r + 1) hm1 arr' resBfly.2 C hC)
     have hF_ex : ∀ C ∈ resExcl.2.2, C ∈ F := fun C hC =>
       hF_bf C (bfr_cm n h' S resExcl.1 n 0 (Nat.sub_zero _) dummyW resExcl.2 C hC)
     obtain ⟨hiso, hconst⟩ := ber_up (2 ^ h') F seed S kL xLit tL fL T_n hnd
       x j hj (2 ^ h') 0 (Nat.sub_zero _) dummyExcl st c (Nat.zero_le _) hF_ex hT_up hF_up hqx
     have hbf := bfr_up n h' F seed S resExcl.1 (2 * T_n.depth + 1) c s j _ n 0 (Nat.sub_zero _)
       dummyW resExcl.2 (Nat.zero_le _) hst1 hexcl1 hF_bf hScj hiso hconst
     rw [show (2 * T_n.depth + 1) + 2 + h' = 2 * T_n.depth + 3 + h' by omega] at hbf
     exact hbf
   · have hT2 := hT.mono (le_trans hle1 hle2)
     have hF2 := hF.mono (le_trans hle1 hle2)
     have hkx2 : ∀ i, VL resBfly.2.1 (kL i) ∧ VL resBfly.2.1 (xLit i) :=
       fun i => ⟨(hkx i).1.mono (le_trans hle1 hle2), (hkx i).2.mono (le_trans hle1 hle2)⟩
     exact bam_up n h' R F seed H kL xLit tL fL T_n hnd x rf c s j hj
       m (r + 1) hm1 arr' resBfly.2 (by omega) hst2 hT2 hF2 hkx2 hF_all hT_up hF_up hScj hqx

def bbi {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) :
   ℕ → St V → St V
 | i, st =>
   if hi : i < n then
     let ifin : Fin n := ⟨i, hi⟩
     let st1 :=
       ei3 (xDual ifin).1 (xDual ifin).2 excl
         (ei2 (wRow ifin false) (xDual ifin).2
           (ei2 (negL (rawIn ifin)) (xDual ifin).2
             (ei2 (wRow ifin true) (xDual ifin).1
               (ei2 (rawIn ifin) (xDual ifin).1 st))))
     bbi n rawIn wRow xDual excl (i + 1) st1
   else st
termination_by i => n - i

lemma bbi_cm {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) :
   ∀ (r i : ℕ) (_ : n - i = r) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bbi n rawIn wRow xDual excl i st).2
 | 0, i, hr, st, C, hC => by
   have hge : ¬ (i < n) := by omega
   unfold bbi; simp only [hge, ↓reduceDIte]; exact hC
 | r + 1, i, hr, st, C, hC => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bbi; simp only [hi, ↓reduceDIte]
   apply bbi_cm n rawIn wRow xDual excl r (i + 1) hm1 _ C
   simp [ei2, ei3, addCl, hC]

lemma bbi_pr {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) :
   ∀ (r i : ℕ) (_ : n - i = r) (st : St V),
     VS st →
     VL st.1 excl →
     (∀ j, VL st.1 (rawIn j) ∧ VL st.1 (wRow j false) ∧ VL st.1 (wRow j true) ∧
       VL st.1 (xDual j).1 ∧ VL st.1 (xDual j).2) →
     let st' := bbi n rawIn wRow xDual excl i st
     VS st' ∧
     st'.1 = st.1 ∧
     st'.2.length ≤ st.2.length + 5 * r ∧
     (∀ C ∈ st.2, C ∈ st'.2) ∧
     ∀ j : Fin n, i ≤ j.val →
       {negL (rawIn j), (xDual j).1} ∈ st'.2 ∧
       {negL (wRow j true), (xDual j).1} ∈ st'.2 ∧
       {negL (negL (rawIn j)), (xDual j).2} ∈ st'.2 ∧
       {negL (wRow j false), (xDual j).2} ∈ st'.2
 | 0, i, hr, st, hst, _, _ => by
   have hge : ¬ (i < n) := by omega
   have heq : bbi n rawIn wRow xDual excl i st = st := by
     unfold bbi; simp only [hge, ↓reduceDIte]
   dsimp only
   rw [heq]
   exact ⟨hst, rfl, by simp, fun _ h => h, fun j hj => by exfalso; omega⟩
 | r + 1, i, hr, st, hst, hex, hv => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bbi; simp only [hi, ↓reduceDIte]
   set ifin : Fin n := ⟨i, hi⟩
   set st1 :=
     ei3 (xDual ifin).1 (xDual ifin).2 excl
       (ei2 (wRow ifin false) (xDual ifin).2
         (ei2 (negL (rawIn ifin)) (xDual ifin).2
           (ei2 (wRow ifin true) (xDual ifin).1
             (ei2 (rawIn ifin) (xDual ifin).1 st))))
   have hst1v : VS st1 :=
     validSt_emitImp3 (validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp2 (validSt_emitImp2 hst
       (hv ifin).1 (hv ifin).2.2.2.1)
       (hv ifin).2.2.1 (hv ifin).2.2.2.1)
       (validLit_negL.2 (hv ifin).1) (hv ifin).2.2.2.2)
       (hv ifin).2.1 (hv ifin).2.2.2.2)
       (hv ifin).2.2.2.1 (hv ifin).2.2.2.2 hex
   have hst1_1 : st1.1 = st.1 := rfl
   have hlen1 : st1.2.length = st.2.length + 5 := rfl
   have hsub1 : ∀ C ∈ st.2, C ∈ st1.2 := fun C hC => by
     simp [st1, ei2, ei3, addCl, hC]
   obtain ⟨r1, r2, r3, r4, r5⟩ := bbi_pr n rawIn wRow xDual excl r (i + 1) hm1 st1
     hst1v hex hv
   refine ⟨r1, r2, by omega, fun C hC => r4 C (hsub1 C hC), fun j hj => ?_⟩
   by_cases heq : i = j.val
   · have hjeq : j = ifin := Fin.ext heq.symm
     subst hjeq
     refine ⟨r4 _ (by simp [st1, ei2, ei3, addCl]),
             r4 _ (by simp [st1, ei2, ei3, addCl]),
             r4 _ (by simp [st1, ei2, ei3, addCl]),
             r4 _ (by simp [st1, ei2, ei3, addCl])⟩
   · exact r5 j (by omega)

lemma bbi_sa {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) (α : Sum V ℕ → Bool) :
   ∀ (r i : ℕ) (_ : n - i = r) (st : St V),
     (∀ C ∈ st.2, ClauseSat α C) →
     (∀ j, lEv α (xDual j).1 = lEv α (rawIn j) ∧ lEv α (xDual j).2 = !(lEv α (rawIn j))) →
     (∀ j b, lEv α (wRow j b) = true → lEv α (rawIn j) = b) →
     ∀ C ∈ (bbi n rawIn wRow xDual excl i st).2, ClauseSat α C
 | 0, i, hr, st, hsat, _, _ => by
   have hge : ¬ (i < n) := by omega
   unfold bbi; simp only [hge, ↓reduceDIte]; exact hsat
 | r + 1, i, hr, st, hsat, hx, hw => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bbi; simp only [hi, ↓reduceDIte]
   apply bbi_sa n rawIn wRow xDual excl α r (i + 1) hm1 _ _ hx hw
   simp only [ei3, ei2, addCl, List.mem_cons, forall_eq_or_imp,
     clauseSat_imp3, clauseSat_imp2, litEval_negL]
   set ifin : Fin n := ⟨i, hi⟩
   refine ⟨?_, ?_, ?_, ?_, ?_, hsat⟩
   · intro h1 h2
     rw [(hx ifin).1] at h1
     rw [(hx ifin).2, h1] at h2
     cases h2
   · intro h
     rw [(hx ifin).2, hw ifin false h]
     rfl
   · intro h
     rw [(hx ifin).2]
     cases hraw : lEv α (rawIn ifin) <;> simp [hraw] at h ⊢
   · intro h
     rw [(hx ifin).1, hw ifin true h]
   · intro h
     rw [(hx ifin).1, h]

lemma bbi_si {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) (α : Sum V ℕ → Bool) :
   ∀ (r i : ℕ) (_ : n - i = r) (st : St V),
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α excl = true →
     (∀ j, lEv α (xDual j).1 = true ∧ lEv α (xDual j).2 = true) →
     ∀ C ∈ (bbi n rawIn wRow xDual excl i st).2, ClauseSat α C
 | 0, i, hr, st, hsat, _, _ => by
   have hge : ¬ (i < n) := by omega
   unfold bbi; simp only [hge, ↓reduceDIte]; exact hsat
 | r + 1, i, hr, st, hsat, hex, hx => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bbi; simp only [hi, ↓reduceDIte]
   apply bbi_si n rawIn wRow xDual excl α r (i + 1) hm1 _ _ hex hx
   simp only [ei3, ei2, addCl, List.mem_cons, forall_eq_or_imp,
     clauseSat_imp3, clauseSat_imp2]
   set ifin : Fin n := ⟨i, hi⟩
   exact ⟨fun _ _ => hex, fun _ => (hx ifin).2, fun _ => (hx ifin).2,
     fun _ => (hx ifin).1, fun _ => (hx ifin).1, hsat⟩

def bpc {V : Type} [DecidableEq V] (n h' : ℕ)
   (H_row : Fin h' → Fin n → Bool) (xDual : Fin n → LN V × LN V)
   (excl : LN V) (s : Fin (2 ^ h')) : ℕ → St V → St V
 | q, st =>
   if hq : q < h' then
     let qf : Fin h' := ⟨q, hq⟩
     let L := (List.finRange n).filter (fun i => H_row qf i)
     let st1 :=
       if hL : L = [] then
         if s.val.testBit q then eu excl st else st
       else
         let T_q := BTree.ofList (L.map xDual) (by simp [hL])
         let res := bdxt T_q st
         ei2 (if s.val.testBit q then res.1.2 else res.1.1) excl res.2
     bpc n h' H_row xDual excl s (q + 1) st1
   else st
termination_by q => h' - q

lemma bpc_cm {V : Type} [DecidableEq V] (n h' : ℕ)
   (H_row : Fin h' → Fin n → Bool) (xDual : Fin n → LN V × LN V)
   (excl : LN V) (s : Fin (2 ^ h')) :
   ∀ (r q : ℕ) (_ : h' - q = r) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bpc n h' H_row xDual excl s q st).2
 | 0, q, hr, st, C, hC => by
   have hge : ¬ (q < h') := by omega
   unfold bpc; simp only [hge, ↓reduceDIte]; exact hC
 | r + 1, q, hr, st, C, hC => by
   have hq : q < h' := by omega
   have hm1 : h' - (q + 1) = r := by omega
   unfold bpc; simp only [hq, ↓reduceDIte]
   apply bpc_cm n h' H_row xDual excl s r (q + 1) hm1 _ C
   by_cases hL : ((List.finRange n).filter (fun i => H_row ⟨q, hq⟩ i)) = []
   · by_cases hs : s.val.testBit q = true <;> simp [hL, hs, eu, addCl, hC]
   · rw [dif_neg hL]
     simp only [ei2, addCl, List.mem_cons]
     exact Or.inr (bdxt_cm _ st C hC)

lemma bpc_pr {V : Type} [DecidableEq V] (n h' : ℕ)
   (H_row : Fin h' → Fin n → Bool) (xDual : Fin n → LN V × LN V)
   (excl : LN V) (s : Fin (2 ^ h')) :
   ∀ (r q : ℕ) (_ : h' - q = r) (st : St V),
     VS st →
     VL st.1 excl →
     (∀ i, VL st.1 (xDual i).1 ∧ VL st.1 (xDual i).2) →
     let st' := bpc n h' H_row xDual excl s q st
     VS st' ∧
     st.1 ≤ st'.1 ∧
     st'.1 ≤ st.1 + 4 * n * r ∧
     st'.2.length ≤ st.2.length + (8 * n + 1) * r ∧
     (∀ C ∈ st.2, C ∈ st'.2)
 | 0, q, hr, st, hst, _, _ => by
   have hge : ¬ (q < h') := by omega
   unfold bpc; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h⟩
 | r + 1, q, hr, st, hst, hex, hx => by
   have hq : q < h' := by omega
   have hm1 : h' - (q + 1) = r := by omega
   unfold bpc; simp only [hq, ↓reduceDIte]
   set qf : Fin h' := ⟨q, hq⟩
   set L := (List.finRange n).filter (fun i => H_row qf i)
   have hLlen : L.length ≤ n := by
     calc L.length ≤ (List.finRange n).length := List.length_filter_le _ _
       _ = n := List.length_finRange
   have hstep : ∃ st1 : St V,
       st1 = (if hL : L = [] then
           if s.val.testBit q then eu excl st else st
         else
           let T_q := BTree.ofList (L.map xDual) (by simp [hL])
           let res := bdxt T_q st
           ei2 (if s.val.testBit q then res.1.2 else res.1.1) excl res.2) ∧
       VS st1 ∧ st.1 ≤ st1.1 ∧ st1.1 ≤ st.1 + 4 * n ∧ st1.2.length ≤ st.2.length + (8 * n + 1) ∧
       (∀ C ∈ st.2, C ∈ st1.2) := by
     by_cases hL : L = []
     · by_cases hs : s.val.testBit q = true
       · refine ⟨eu excl st, by simp [hL, hs], validSt_emitUnit hst hex, le_rfl, by simp [eu, addCl],
           by simp [eu, addCl], fun C hC => by simp [eu, addCl, hC]⟩
       · refine ⟨st, by simp [hL, hs], hst, le_rfl, by omega, by omega, fun _ h => h⟩
     · set T_q := BTree.ofList (L.map xDual) (by simp [hL])
       have hTleaves : T_q.leaves = L.map xDual := BTree.leaves_ofList _ _
       have hTa : ∀ a ∈ T_q.leaves, VL st.1 a.1 ∧ VL st.1 a.2 := by
         intro a ha
         rw [hTleaves] at ha
         rcases List.mem_map.1 ha with ⟨i, _, rfl⟩
         exact hx i
       obtain ⟨hstT, hleT, hmT, hlT, hsubT, hvT1, hvT2⟩ := bdxt_pr T_q st hst hTa
       set res := bdxt T_q st
       have hnodes : T_q.nodes ≤ 2 * n := by
         have hnb := BTree.nodes_ofList (L.map xDual) (by simp [hL])
         change T_q.nodes + 1 ≤ 2 * (L.map xDual).length at hnb
         rw [List.length_map] at hnb
         omega
       set st1 := ei2 (if s.val.testBit q then res.1.2 else res.1.1) excl res.2
       have hst1v : VS st1 := validSt_emitImp2 hstT (by split_ifs <;> assumption) (hex.mono hleT)
       have hm1_v : st1.1 ≤ st.1 + 4 * n := by
         have : st1.1 = res.2.1 := rfl
         omega
       have hl1_c : st1.2.length ≤ st.2.length + (8 * n + 1) := by
         have : st1.2.length = res.2.2.length + 1 := rfl
         omega
       refine ⟨st1, by simp [hL, st1, res, T_q], hst1v, hleT, hm1_v, hl1_c,
         fun C hC => by simp [st1, ei2, addCl, hsubT C hC]⟩
   obtain ⟨st1, hst1_eq, hst1v, hle1, hm1_v, hl1_c, hsub1⟩ := hstep
   rw [← hst1_eq]
   obtain ⟨r1, r2, r3, r4, r5⟩ := bpc_pr n h' H_row xDual excl s r (q + 1) hm1 st1
     hst1v (hex.mono hle1) (fun i => ⟨(hx i).1.mono hle1, (hx i).2.mono hle1⟩)
   refine ⟨r1, le_trans hle1 r2, ?_, ?_, fun C hC => r5 C (hsub1 C hC)⟩
   · calc (bpc n h' H_row xDual excl s (q + 1) st1).1
       _ ≤ st1.1 + 4 * n * r := r3
       _ ≤ (st.1 + 4 * n) + 4 * n * r := Nat.add_le_add_right hm1_v _
       _ = st.1 + 4 * n * (r + 1) := by ring
   · calc (bpc n h' H_row xDual excl s (q + 1) st1).2.length
       _ ≤ st1.2.length + (8 * n + 1) * r := r4
       _ ≤ (st.2.length + (8 * n + 1)) + (8 * n + 1) * r := Nat.add_le_add_right hl1_c _
       _ = st.2.length + (8 * n + 1) * (r + 1) := by ring

lemma bpc_sa {V : Type} [DecidableEq V] (n h' : ℕ)
   (H_row : Fin h' → Fin n → Bool) (xDual : Fin n → LN V × LN V)
   (excl : LN V) (s : Fin (2 ^ h')) :
   ∀ (r q : ℕ) (_ : h' - q = r) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 excl →
     (∀ i, VL st.1 (xDual i).1 ∧ VL st.1 (xDual i).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α excl = false →
     (∀ i, lEv α (xDual i).2 = !(lEv α (xDual i).1)) →
     (∀ qf : Fin h', q ≤ qf.val →
       s.val.testBit qf.val = xl (((List.finRange n).filter (fun i => H_row qf i)).map (fun i => lEv α (xDual i).1))) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bpc n h' H_row xDual excl s q st).2, ClauseSat α' C)
 | 0, q, hr, st, α, _, _, _, hsat, _, _, _ => by
   have hge : ¬ (q < h') := by omega
   unfold bpc; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat⟩
 | r + 1, q, hr, st, α, hst, hex, hx, hsat, hexv, hanti, hs => by
   have hq : q < h' := by omega
   have hm1 : h' - (q + 1) = r := by omega
   unfold bpc; simp only [hq, ↓reduceDIte]
   set qf : Fin h' := ⟨q, hq⟩
   set L := (List.finRange n).filter (fun i => H_row qf i)
   have hsq := hs qf (le_refl q)
   by_cases hL : L = []
   · have hsf : s.val.testBit q = false := by simpa [L, qf, hL, xl] using hsq
     have hL' : ((List.finRange n).filter (fun i => H_row ⟨q, hq⟩ i)) = [] := hL
     rw [dif_pos hL', if_neg (by rw [hsf]; exact Bool.false_ne_true)]
     exact bpc_sa n h' H_row xDual excl s r (q + 1) hm1 st α
       hst hex hx hsat hexv hanti (fun qf' hqf' => hs qf' (by omega))
   · have hL' : ((List.finRange n).filter (fun i => H_row ⟨q, hq⟩ i)) ≠ [] := hL
     rw [dif_neg hL']
     set T_q := BTree.ofList (L.map xDual) (by simp [hL])
     have hTleaves : T_q.leaves = L.map xDual := BTree.leaves_ofList _ _
     have hTa : ∀ a ∈ T_q.leaves, VL st.1 a.1 ∧ VL st.1 a.2 := by
       intro a ha; rw [hTleaves] at ha
       rcases List.mem_map.1 ha with ⟨i, _, rfl⟩; exact hx i
     have hTanti : ∀ a ∈ T_q.leaves, lEv α a.2 = !(lEv α a.1) := by
       intro a ha; rw [hTleaves] at ha
       rcases List.mem_map.1 ha with ⟨i, _, rfl⟩; exact hanti i
     obtain ⟨hstT, hleT, _, _, _, hvT1, hvT2⟩ := bdxt_pr T_q st hst hTa
     obtain ⟨α1, h1inl, h1lt, h1sat, h1v1, h1v2⟩ :=
       bdxt_sa T_q st α hst hTa hTanti hsat
     set res := bdxt T_q st
     have h1xor : xl (T_q.leaves.map (fun a => lEv α a.1)) = s.val.testBit q := by
       rw [hTleaves, List.map_map]
       exact hsq.symm
     rw [h1xor] at h1v1 h1v2
     set st1 := ei2 (if s.val.testBit q then res.1.2 else res.1.1) excl res.2
     have hsat1 : ∀ C ∈ st1.2, ClauseSat α1 C := by
       simp only [st1, ei2, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp2]
       refine ⟨fun h => ?_, h1sat⟩
       cases hsb : s.val.testBit q
       · rw [hsb] at h h1v1; simp only [Bool.false_eq_true, ↓reduceIte] at h; rw [h1v1] at h; cases h
       · rw [hsb] at h h1v2; simp only [↓reduceIte] at h; rw [h1v2] at h; cases h
     have hst1v : VS st1 := validSt_emitImp2 hstT (by split_ifs <;> assumption) (hex.mono hleT)
     have hst1_1 : st1.1 = res.2.1 := rfl
     have hex1 : VL st1.1 excl := hex.mono hleT
     have hx1 : ∀ i, VL st1.1 (xDual i).1 ∧ VL st1.1 (xDual i).2 :=
       fun i => ⟨(hx i).1.mono hleT, (hx i).2.mono hleT⟩
     have hexv1 : lEv α1 excl = false := (lecl h1inl h1lt hex).trans hexv
     have hanti1 : ∀ i, lEv α1 (xDual i).2 = !(lEv α1 (xDual i).1) := fun i => by
       rw [lecl h1inl h1lt (hx i).2, lecl h1inl h1lt (hx i).1, hanti i]
     have hs1 : ∀ qf' : Fin h', q + 1 ≤ qf'.val →
         s.val.testBit qf'.val = xl (((List.finRange n).filter (fun i => H_row qf' i)).map (fun i => lEv α1 (xDual i).1)) := by
       intro qf' hqf'
       rw [hs qf' (by omega)]
       congr 1
       refine List.map_congr_left fun i _ => (lecl h1inl h1lt (hx i).1).symm
     obtain ⟨α', h'inl, h'lt, h'sat⟩ :=
       bpc_sa n h' H_row xDual excl s r (q + 1) hm1 st1 α1
         hst1v hex1 hx1 hsat1 hexv1 hanti1 hs1
     exact ⟨α', fun v => (h'inl v).trans (h1inl v), fun k hk => (h'lt k (lt_of_lt_of_le hk hleT)).trans (h1lt k hk), h'sat⟩

lemma bpc_si {V : Type} [DecidableEq V] (n h' : ℕ)
   (H_row : Fin h' → Fin n → Bool) (xDual : Fin n → LN V × LN V)
   (excl : LN V) (s : Fin (2 ^ h')) :
   ∀ (r q : ℕ) (_ : h' - q = r) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     VL st.1 excl →
     (∀ i, VL st.1 (xDual i).1 ∧ VL st.1 (xDual i).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     lEv α excl = true →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bpc n h' H_row xDual excl s q st).2, ClauseSat α' C)
 | 0, q, hr, st, α, _, _, _, hsat, _ => by
   have hge : ¬ (q < h') := by omega
   unfold bpc; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat⟩
 | r + 1, q, hr, st, α, hst, hex, hx, hsat, hexv => by
   have hq : q < h' := by omega
   have hm1 : h' - (q + 1) = r := by omega
   unfold bpc; simp only [hq, ↓reduceDIte]
   set qf : Fin h' := ⟨q, hq⟩
   set L := (List.finRange n).filter (fun i => H_row qf i)
   by_cases hL : L = []
   · have hL' : ((List.finRange n).filter (fun i => H_row ⟨q, hq⟩ i)) = [] := hL
     by_cases hs : s.val.testBit q = true
     · rw [dif_pos hL', if_pos hs]
       have hsat1 : ∀ C ∈ (eu excl st).2, ClauseSat α C := by
         simp only [eu, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_singleton]
         exact ⟨hexv, hsat⟩
       exact bpc_si n h' H_row xDual excl s r (q + 1) hm1 (eu excl st) α
         (validSt_emitUnit hst hex) hex hx hsat1 hexv
     · rw [dif_pos hL', if_neg hs]
       exact bpc_si n h' H_row xDual excl s r (q + 1) hm1 st α hst hex hx hsat hexv
   · have hL' : ((List.finRange n).filter (fun i => H_row ⟨q, hq⟩ i)) ≠ [] := hL
     rw [dif_neg hL']
     set T_q := BTree.ofList (L.map xDual) (by simp [hL])
     have hTleaves : T_q.leaves = L.map xDual := BTree.leaves_ofList _ _
     have hTa : ∀ a ∈ T_q.leaves, VL st.1 a.1 ∧ VL st.1 a.2 := by
       intro a ha; rw [hTleaves] at ha
       rcases List.mem_map.1 ha with ⟨i, _, rfl⟩; exact hx i
     obtain ⟨hstT, hleT, _, _, _, hvT1, hvT2⟩ := bdxt_pr T_q st hst hTa
     let α1 : Sum V ℕ → Bool := fun w =>
       match w with
       | Sum.inl v => α (Sum.inl v)
       | Sum.inr k => if k < st.1 then α (Sum.inr k) else true
     have h1inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
     have h1lt : ∀ k < st.1, α1 (Sum.inr k) = α (Sum.inr k) := fun k hk => by simp [α1, hk]
     have hsatT : ∀ C ∈ (bdxt T_q st).2.2, ClauseSat α1 C :=
       bdxt_si T_q st α hst hsat
     set res := bdxt T_q st
     have hex1v : lEv α1 excl = true := (lecl h1inl h1lt hex).trans hexv
     set st1 := ei2 (if s.val.testBit q then res.1.2 else res.1.1) excl res.2
     have hsat1 : ∀ C ∈ st1.2, ClauseSat α1 C := by
       simp only [st1, ei2, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp2]
       exact ⟨fun _ => hex1v, hsatT⟩
     have hst1v : VS st1 := validSt_emitImp2 hstT (by split_ifs <;> assumption) (hex.mono hleT)
     have hst1_1 : st1.1 = res.2.1 := rfl
     have hex1 : VL st1.1 excl := hex.mono hleT
     have hx1 : ∀ i, VL st1.1 (xDual i).1 ∧ VL st1.1 (xDual i).2 :=
       fun i => ⟨(hx i).1.mono hleT, (hx i).2.mono hleT⟩
     obtain ⟨α', h'inl, h'lt, h'sat⟩ :=
       bpc_si n h' H_row xDual excl s r (q + 1) hm1 st1 α1
         hst1v hex1 hx1 hsat1 hex1v
     exact ⟨α', fun v => (h'inl v).trans (h1inl v), fun k hk => (h'lt k (lt_of_lt_of_le hk hleT)).trans (h1lt k hk), h'sat⟩

lemma bbi_mem {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) :
   ∀ (r i : ℕ) (_ : n - i = r) (st : St V) (j : Fin n), i ≤ j.val →
     {negL (rawIn j), (xDual j).1} ∈ (bbi n rawIn wRow xDual excl i st).2 ∧
     {negL (wRow j true), (xDual j).1} ∈ (bbi n rawIn wRow xDual excl i st).2 ∧
     {negL (negL (rawIn j)), (xDual j).2} ∈ (bbi n rawIn wRow xDual excl i st).2 ∧
     {negL (wRow j false), (xDual j).2} ∈ (bbi n rawIn wRow xDual excl i st).2
 | 0, i, hr, st, j, hij => by exfalso; omega
 | r + 1, i, hr, st, j, hij => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bbi; simp only [hi, ↓reduceDIte]
   by_cases heq : i = j.val
   · have hjeq : j = ⟨i, hi⟩ := Fin.ext heq.symm
     rw [hjeq]
     have hsub := bbi_cm n rawIn wRow xDual excl r (i + 1) hm1
     exact ⟨hsub _ _ (by simp [ei3, ei2, addCl]),
           hsub _ _ (by simp [ei3, ei2, addCl]),
           hsub _ _ (by simp [ei3, ei2, addCl]),
           hsub _ _ (by simp [ei3, ei2, addCl])⟩
   · exact bbi_mem n rawIn wRow xDual excl r (i + 1) hm1 _ j (by omega)

lemma bbi_up {V : Type} [DecidableEq V] (n : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V)
   (st : St V) (d0 : ℕ) (x' : Fin n → Bool)
   (hF : ∀ C ∈ (bbi n rawIn wRow xDual excl 0 st).2, C ∈ F)
   (hx_in : ∀ j : Fin n,
     fLt (rawIn j) (x' j) ∈ (upS F)^[d0] seed ∨ wRow j (x' j) ∈ (upS F)^[d0] seed) :
   ∀ j : Fin n, lod (xDual j) (x' j) ∈ (upS F)^[d0 + 1] seed := by
 intro j
 obtain ⟨hc1, hc2, hc3, hc4⟩ := bbi_mem n rawIn wRow xDual excl n 0 (Nat.sub_zero _) st j (Nat.zero_le _)
 rw [Function.iterate_succ_apply']
 rcases hx_in j with hraw | hw
 · cases hxb : x' j
   · have h1 := upStep_unit2 (hF _ hc3) (by simpa [fLt, hxb, negL_negL] using hraw)
     simpa [lod, hxb] using h1
   · have h1 := upStep_unit2 (hF _ hc1) (by simpa [fLt, hxb, negL_negL] using hraw)
     simpa [lod, hxb] using h1
 · cases hxb : x' j
   · have h1 := upStep_unit2 (hF _ hc4) (by rw [hxb] at hw; rw [negL_negL]; exact hw)
     simpa [lod, hxb] using h1
   · have h1 := upStep_unit2 (hF _ hc2) (by rw [hxb] at hw; rw [negL_negL]; exact hw)
     simpa [lod, hxb] using h1

open Classical in
lemma bpc_up {V : Type} [DecidableEq V] (n h' : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (H_row : Fin h' → Fin n → Bool) (xDual : Fin n → LN V × LN V)
   (excl : LN V) (s : Fin (2 ^ h')) (d0 : ℕ) (x' : Fin n → Bool)
   (hx_inj : ∀ i j : Fin n, xDual i = xDual j → i = j) (qf : Fin h') :
   ∀ (r q : ℕ) (_ : h' - q = r),
     q ≤ qf.val →
     (∀ st : St V,
       (∀ C ∈ (bpc n h' H_row xDual excl s q st).2, C ∈ F) →
       (∀ i, lod (xDual i) (x' i) ∈ (upS F)^[d0] seed) →
       s.val.testBit qf.val ≠ xl (((List.finRange n).filter (fun i => H_row qf i)).map x') →
       excl ∈ (upS F)^[d0 + Nat.clog 2 (n + 1) + 1] seed)
 | 0, q, hr, hq => by exfalso; omega
 | r + 1, q, hr, hq => by
   intro st hF hx_up hne
   have hq_lt : q < h' := by omega
   have hm1 : h' - (q + 1) = r := by omega
   unfold bpc at hF
   simp only [hq_lt, ↓reduceDIte] at hF
   set qf0 : Fin h' := ⟨q, hq_lt⟩
   set L := (List.finRange n).filter (fun i => H_row qf0 i)
   by_cases heq : q = qf.val
   · have hqeq : qf = qf0 := Fin.ext heq.symm
     rw [hqeq] at hne
     have hsqeq : s.val.testBit qf0.val = s.val.testBit q := rfl
     by_cases hL : L = []
     · have hs_true : s.val.testBit q = true := by
         have hxor0 : xl (L.map x') = false := by simp [hL, xl]
         dsimp only [L] at hxor0
         change s.val.testBit q ≠ xl (((List.finRange n).filter (fun i => H_row qf0 i)).map x') at hne
         rw [hxor0] at hne
         cases hs : s.val.testBit q <;> simp [hs] at hne ⊢
       have hC : ({excl} : CN V) ∈ F := by
         apply hF
         apply bpc_cm n h' H_row xDual excl s r (q + 1) hm1
         rw [dif_pos hL, if_pos hs_true]
         simp [eu, addCl]
       have he1 : excl ∈ (upS F)^[1] seed := by
         rw [Function.iterate_one]; exact upStep_unit1 hC
       exact upStep_iter_le F seed (by omega) he1
     · set T_q := BTree.ofList (L.map xDual) (by simp [hL])
       have hTleaves : T_q.leaves = L.map xDual := BTree.leaves_ofList _ _
       have hTdep : T_q.depth ≤ Nat.clog 2 (n + 1) := by
         have h1 := BTree.depth_ofList (L.map xDual) (by simp [hL])
         change T_q.depth ≤ Nat.clog 2 (L.map xDual).length at h1
         have hLlen : L.length ≤ n := by
           calc L.length ≤ (List.finRange n).length := List.length_filter_le _ _
             _ = n := List.length_finRange
         rw [List.length_map] at h1
         exact le_trans h1 (Nat.clog_mono_right 2 (by omega))
       let val : LN V × LN V → Bool := fun p =>
         if h : ∃ i : Fin n, xDual i = p then x' (Classical.choose h) else false
       have hval_eq : ∀ i : Fin n, val (xDual i) = x' i := by
         intro i
         have hex : ∃ i' : Fin n, xDual i' = xDual i := ⟨i, rfl⟩
         dsimp only [val]
         rw [dif_pos hex]
         have := hx_inj _ _ (Classical.choose_spec hex)
         rw [this]
       have hF_xor : ∀ C ∈ (bdxt T_q st).2.2, C ∈ F := by
         intro C hC
         apply hF
         apply bpc_cm n h' H_row xDual excl s r (q + 1) hm1
         have hL' : ((List.finRange n).filter (fun i => H_row ⟨q, hq_lt⟩ i)) ≠ [] := hL
         rw [dif_neg hL']
         simp [L, qf0, T_q, ei2, addCl, hC]
       have hT_up := bdxt_up F ((upS F)^[d0] seed) val T_q st 0 hF_xor (by
         intro a ha
         rw [hTleaves] at ha
         rcases List.mem_map.1 ha with ⟨i, _, rfl⟩
         rw [Function.iterate_zero_apply, hval_eq i]
         exact hx_up i)
       have hT_up' : lod (bdxt T_q st).1 (xl (L.map x')) ∈
           (upS F)^[d0 + T_q.depth] seed := by
         have hmap : T_q.leaves.map val = L.map x' := by
           rw [hTleaves, List.map_map]
           exact List.map_congr_left fun i _ => hval_eq i
         rw [hmap, ← Function.iterate_add_apply, Nat.add_comm] at hT_up
         simpa using hT_up
       set res := bdxt T_q st
       have hC : ({negL (if s.val.testBit q then res.1.2 else res.1.1), excl} : CN V) ∈ F := by
         apply hF
         apply bpc_cm n h' H_row xDual excl s r (q + 1) hm1
         have hL' : ((List.finRange n).filter (fun i => H_row ⟨q, hq_lt⟩ i)) ≠ [] := hL
         rw [dif_neg hL']
         simp [L, qf0, res, T_q, ei2, addCl]
       have hpre : (if s.val.testBit q then res.1.2 else res.1.1) ∈ (upS F)^[d0 + T_q.depth] seed := by
         cases hsb : s.val.testBit q <;> cases hxb : xl (L.map x')
         · exfalso; exact hne (by rw [hsb, hxb])
         · simpa [lod, hsb, hxb] using hT_up'
         · simpa [lod, hsb, hxb] using hT_up'
         · exfalso; exact hne (by rw [hsb, hxb])
       have hexcl_mem : excl ∈ (upS F)^[d0 + T_q.depth + 1] seed := by
         rw [Function.iterate_succ_apply']
         exact upStep_unit2 hC (by rw [negL_negL]; exact hpre)
       exact upStep_iter_le F seed (by omega) hexcl_mem
   · exact bpc_up n h' F seed H_row xDual excl s d0 x' hx_inj qf r (q + 1) hm1
       (by omega) _ hF hx_up hne

structure BR (n t : ℕ) where
 excl : LN (Fin n ⊕ Fin t)
 xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)
 wiresOut : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)
 stOut : St (Fin n ⊕ Fin t)

def bb (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t)) : BR n t :=
 let pEx := fv st
 let excl := pEx.1
 let base := pEx.2.1
 let xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun i => (ag n base i false, ag n base i true)
 let st2 : St (Fin n ⊕ Fin t) := (base + 2 * n, pEx.2.2)
 let rawIn : Fin n → LN (Fin n ⊕ Fin t) := fun i => (Sum.inl (Sum.inl i), true)
 let stIn := bbi n rawIn wRow xDual excl 0 st2
 let stPar := bpc n h' H_row xDual excl s 0 stIn
 let wires0 : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun u => if hu : u < n then xDual ⟨u, hu⟩ else fd
 let resG := bcg n D gates fd (some excl) 0 wires0 stPar
 let stOut := boc out resG.1 (some excl) 0 resG.2
 ⟨excl, xDual, resG.1, stOut⟩

lemma boc_cm {n t : ℕ} (out : Fin t → ℕ)
   (wires : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (exclOpt : Option (LN (Fin n ⊕ Fin t))) :
   ∀ (m j : ℕ) (_ : t - j = m) (st : St (Fin n ⊕ Fin t)) (C : CN (Fin n ⊕ Fin t)),
     C ∈ st.2 → C ∈ (boc out wires exclOpt j st).2
 | 0, j, hm, st, C, hC => by
   have hge : ¬ (j < t) := by omega
   unfold boc; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, j, hm, st, C, hC => by
   have hj : j < t := by omega
   have hm1 : t - (j + 1) = m := by omega
   unfold boc; simp only [hj, ↓reduceDIte]
   apply boc_cm out wires exclOpt m (j + 1) hm1 _ C
   cases hopt : exclOpt <;> simp [hopt, ei2, ei3, addCl, hC]

lemma bb_cm (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t)) (C : CN (Fin n ⊕ Fin t)) (hC : C ∈ st.2) :
   C ∈ (bb n t h' D gates out H_row wRow fd s st).stOut.2 := by
 dsimp only [bb]
 apply boc_cm out _ (some _) t 0 (Nat.sub_zero _)
 apply bcg_cm n D gates fd (some _) gates.length 0 (Nat.sub_zero _)
 apply bpc_cm n h' H_row _ _ s h' 0 (Nat.sub_zero _)
 apply bbi_cm n _ wRow _ _ n 0 (Nat.sub_zero _)
 exact hC

lemma bb_pr (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t))
   (hst : VS st)
   (hf1 : VL st.1 fd.1) (hf2 : VL st.1 fd.2)
   (hw : ∀ i b, VL st.1 (wRow i b)) :
   let br := bb n t h' D gates out H_row wRow fd s st
   VS br.stOut ∧
   st.1 ≤ br.stOut.1 ∧
   br.stOut.1 ≤ st.1 + (1 + 2 * n + 4 * n * h' + 2 * gates.length) ∧
   br.stOut.2.length ≤ st.2.length + (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) ∧
   (∀ C ∈ st.2, C ∈ br.stOut.2) ∧
   VL br.stOut.1 br.excl ∧
   (∀ i, VL br.stOut.1 (br.xDual i).1 ∧ VL br.stOut.1 (br.xDual i).2) ∧
   (∀ u, VL br.stOut.1 (br.wiresOut u).1 ∧ VL br.stOut.1 (br.wiresOut u).2) := by
 dsimp only [bb]
 set pEx := fv st
 set excl := pEx.1
 set base := pEx.2.1
 set xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun i => (ag n base i false, ag n base i true)
 set st2 : St (Fin n ⊕ Fin t) := (base + 2 * n, pEx.2.2)
 set rawIn : Fin n → LN (Fin n ⊕ Fin t) := fun i => (Sum.inl (Sum.inl i), true)
 have hst2v : VS st2 := fun C hC =>
   ⟨(hst C hC).1, (hst C hC).2.mono (by dsimp only [st2, base, pEx, fv]; omega)⟩
 have hst2_1 : st2.1 = st.1 + 1 + 2 * n := rfl
 have hex2 : VL st2.1 excl := (validLit_fresh st).mono (by rw [hst2_1]; omega)
 have hle02 : st.1 ≤ st2.1 := by omega
 have hv_in : ∀ j, VL st2.1 (rawIn j) ∧ VL st2.1 (wRow j false) ∧ VL st2.1 (wRow j true) ∧
     VL st2.1 (xDual j).1 ∧ VL st2.1 (xDual j).2 := fun j =>
   ⟨validLit_inl _ _ _, (hw j false).mono hle02, (hw j true).mono hle02,
   validLit_allocGrid _ n base j false, validLit_allocGrid _ n base j true⟩
 obtain ⟨hstIn, hIn_1, hIn_len, hIn_sub, _⟩ :=
   bbi_pr n rawIn wRow xDual excl n 0 (Nat.sub_zero _) st2 hst2v hex2 hv_in
 set stIn := bbi n rawIn wRow xDual excl 0 st2
 have hexIn : VL stIn.1 excl := by rw [hIn_1]; exact hex2
 have hxIn : ∀ i, VL stIn.1 (xDual i).1 ∧ VL stIn.1 (xDual i).2 := fun i => by
   rw [hIn_1]; exact ⟨(hv_in i).2.2.2.1, (hv_in i).2.2.2.2⟩
 obtain ⟨hstPar, hPar_le, hPar_1, hPar_len, hPar_sub⟩ :=
   bpc_pr n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn hstIn hexIn hxIn
 set stPar := bpc n h' H_row xDual excl s 0 stIn
 have hle2P : st2.1 ≤ stPar.1 := by rw [← hIn_1]; exact hPar_le
 have hle0P : st.1 ≤ stPar.1 := le_trans hle02 hle2P
 set wires0 : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun u => if hu : u < n then xDual ⟨u, hu⟩ else fd
 have hwires0 : ∀ u, VL stPar.1 (wires0 u).1 ∧ VL stPar.1 (wires0 u).2 := fun u => by
   dsimp only [wires0]
   split_ifs
   · exact ⟨(hv_in _).2.2.2.1.mono hle2P, (hv_in _).2.2.2.2.mono hle2P⟩
   · exact ⟨hf1.mono hle0P, hf2.mono hle0P⟩
 obtain ⟨hstG, hGle, hG_1, hG_len, hG_sub, hGw, _, _⟩ :=
   bcg_pr n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar
     hstPar (hf1.mono hle0P) (hf2.mono hle0P) (fun _ h => by cases h; exact hexIn.mono hPar_le) hwires0
 set resG := bcg n D gates fd (some excl) 0 wires0 stPar
 have hexG : ∀ ex, some excl = some ex → VL resG.2.1 ex := by
   intro _ h; cases h; exact (hexIn.mono hPar_le).mono hGle
 obtain ⟨hstO, hO_1, hO_len, hO_sub, _⟩ :=
   boc_pr out resG.1 (some excl) t 0 (Nat.sub_zero _) resG.2 hstG hexG hGw
 have hO1' : (boc out resG.1 (some excl) 0 resG.2).1 = resG.2.1 := hO_1
 have hG1' : resG.2.1 ≤ stPar.1 + 2 * gates.length := hG_1
 have hPar1' : stPar.1 ≤ stIn.1 + 4 * n * h' := hPar_1
 have hO_len' : (boc out resG.1 (some excl) 0 resG.2).2.length ≤ resG.2.2.length + 2 * t := hO_len
 have hG_len' : resG.2.2.length ≤ stPar.2.length + 5 * gates.length := hG_len
 have hPar_len' : stPar.2.length ≤ stIn.2.length + (8 * n + 1) * h' := hPar_len
 have hIn_len' : stIn.2.length ≤ st2.2.length + 5 * n := hIn_len
 have hst2_len : st2.2.length = st.2.length := rfl
 refine ⟨hstO, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
 · have hle_G : stPar.1 ≤ resG.2.1 := hGle
   omega
 · omega
 · omega
 · intro C hC; exact hO_sub C (hG_sub C (hPar_sub C (hIn_sub C hC)))
 · rw [hO_1]; exact (hexIn.mono hPar_le).mono hGle
 · intro i; rw [hO_1]; exact ⟨((hv_in i).2.2.2.1.mono hle2P).mono hGle, ((hv_in i).2.2.2.2.mono hle2P).mono hGle⟩
 · intro u; rw [hO_1]; exact hGw u

lemma bb_sa (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t)) (α : Sum (Fin n ⊕ Fin t) ℕ → Bool)
   (hst : VS st)
   (hf1 : VL st.1 fd.1) (hf2 : VL st.1 fd.2)
   (hw : ∀ i b, VL st.1 (wRow i b))
   (hsat : ∀ C ∈ st.2, ClauseSat α C)
   (hfval : lEv α fd.1 = false ∧ lEv α fd.2 = true)
   (hww : ∀ i b, lEv α (wRow i b) = true → α (Sum.inl (Sum.inl i)) = b)
   (hs : ∀ q : Fin h', s.val.testBit q.val =
     xl (((List.finRange n).filter (fun i => H_row q i)).map (fun i => α (Sum.inl (Sum.inl i)))))
   (hag : ∀ j : Fin t, α (Sum.inl (Sum.inr j)) =
     ((⟨gates, 0⟩ : BinaryCircuit).wires
       (List.ofFn (fun i : Fin n => α (Sum.inl (Sum.inl i))))).getD (out j) false)
   (hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D) :
   let br := bb n t h' D gates out H_row wRow fd s st
   ∃ α' : Sum (Fin n ⊕ Fin t) ℕ → Bool,
     (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
     (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
     (∀ C ∈ br.stOut.2, ClauseSat α' C) ∧
     lEv α' br.excl = false ∧
     (∀ i, lEv α' (br.xDual i).1 = α (Sum.inl (Sum.inl i)) ∧
           lEv α' (br.xDual i).2 = !(α (Sum.inl (Sum.inl i)))) ∧
     (∀ j : Fin t, lEv α' (br.wiresOut (out j)).1 = α (Sum.inl (Sum.inr j)) ∧
                   lEv α' (br.wiresOut (out j)).2 = !(α (Sum.inl (Sum.inr j)))) := by
 dsimp only [bb]
 set pEx := fv st
 set excl := pEx.1
 set base := pEx.2.1
 set xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun i => (ag n base i false, ag n base i true)
 set st2 : St (Fin n ⊕ Fin t) := (base + 2 * n, pEx.2.2)
 set rawIn : Fin n → LN (Fin n ⊕ Fin t) := fun i => (Sum.inl (Sum.inl i), true)
 let x : Fin n → Bool := fun i => α (Sum.inl (Sum.inl i))
 let α1 : Sum (Fin n ⊕ Fin t) ℕ → Bool := fun z =>
   match z with
   | Sum.inl v => α (Sum.inl v)
   | Sum.inr k =>
     if k < st.1 then α (Sum.inr k)
     else if k = st.1 then false
     else if hk : k - base < 2 * n then
       let idx := (k - base) / 2
       if (k - base) % 2 = 0 then x ⟨idx, by omega⟩ else !(x ⟨idx, by omega⟩)
     else true
 have h1inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
 have h1lt : ∀ k < st.1, α1 (Sum.inr k) = α (Sum.inr k) := fun k hk => by simp [α1, hk]
 have hst2v : VS st2 := fun C hC =>
   ⟨(hst C hC).1, (hst C hC).2.mono (by dsimp only [st2, base, pEx, fv]; omega)⟩
 have hst2_1 : st2.1 = st.1 + 1 + 2 * n := rfl
 have hex2 : VL st2.1 excl := (validLit_fresh st).mono (by rw [hst2_1]; omega)
 have hle02 : st.1 ≤ st2.1 := by omega
 have hv_in : ∀ j, VL st2.1 (rawIn j) ∧ VL st2.1 (wRow j false) ∧ VL st2.1 (wRow j true) ∧
     VL st2.1 (xDual j).1 ∧ VL st2.1 (xDual j).2 := fun j =>
   ⟨validLit_inl _ _ _, (hw j false).mono hle02, (hw j true).mono hle02,
   validLit_allocGrid _ n base j false, validLit_allocGrid _ n base j true⟩
 have hsat2 : ∀ C ∈ st2.2, ClauseSat α1 C := fun C hC =>
   (cscl h1inl h1lt (hst C hC).2).2 (hsat C hC)
 have hex_val : lEv α1 excl = false := by
   simp [excl, pEx, fv, lEv, α1]
 have hxDual_val : ∀ i, lEv α1 (xDual i).1 = x i ∧ lEv α1 (xDual i).2 = !(x i) := by
   intro i
   dsimp only [xDual]
   rw [litEval_allocGrid, litEval_allocGrid]
   simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
   have hbase : base = st.1 + 1 := rfl
   have hc1 : ¬ (base + 2 * i.val < st.1) := by omega
   have hc2 : base + 2 * i.val ≠ st.1 := by omega
   have hc3 : base + 2 * i.val - base < 2 * n := by omega
   have hd1 : ¬ (base + 2 * i.val + 1 < st.1) := by omega
   have hd2 : base + 2 * i.val + 1 ≠ st.1 := by omega
   have hd3 : base + 2 * i.val + 1 - base < 2 * n := by omega
   constructor
   · simp only [α1]
     rw [if_neg hc1, if_neg hc2, dif_pos hc3]
     simp [show (base + 2 * i.val - base) % 2 = 0 by omega]
   · simp only [α1]
     rw [if_neg hd1, if_neg hd2, dif_pos hd3]
     have hidx : (base + 2 * i.val + 1 - base) / 2 = i.val := by omega
     simp [hidx, show (base + 2 * i.val + 1 - base) % 2 ≠ 0 by omega]
 have hsatIn : ∀ C ∈ (bbi n rawIn wRow xDual excl 0 st2).2, ClauseSat α1 C :=
   bbi_sa n rawIn wRow xDual excl α1 n 0 (Nat.sub_zero _) st2 hsat2
     (fun j => by simpa [rawIn, lEv, h1inl] using hxDual_val j)
     (fun j b h => by
       rw [lecl h1inl h1lt (hw j b)] at h
       simpa [rawIn, lEv, h1inl] using hww j b h)
 obtain ⟨hstIn, hIn_1, _, _, _⟩ :=
   bbi_pr n rawIn wRow xDual excl n 0 (Nat.sub_zero _) st2 hst2v hex2 hv_in
 set stIn := bbi n rawIn wRow xDual excl 0 st2
 have hexIn : VL stIn.1 excl := by rw [hIn_1]; exact hex2
 have hxIn : ∀ i, VL stIn.1 (xDual i).1 ∧ VL stIn.1 (xDual i).2 := fun i => by
   rw [hIn_1]; exact ⟨(hv_in i).2.2.2.1, (hv_in i).2.2.2.2⟩
 have hanti1 : ∀ i, lEv α1 (xDual i).2 = !(lEv α1 (xDual i).1) := fun i => by
   rw [(hxDual_val i).1, (hxDual_val i).2]
 have hs1 : ∀ qf : Fin h', 0 ≤ qf.val →
     s.val.testBit qf.val = xl (((List.finRange n).filter (fun i => H_row qf i)).map (fun i => lEv α1 (xDual i).1)) := by
   intro qf _
   rw [hs qf]
   congr 1
   exact List.map_congr_left fun i _ => (hxDual_val i).1.symm
 obtain ⟨α2, h2inl, h2lt, h2sat⟩ :=
   bpc_sa n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn α1
     hstIn hexIn hxIn hsatIn hex_val hanti1 hs1
 obtain ⟨hstPar, hPar_le, _, _, _⟩ :=
   bpc_pr n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn hstIn hexIn hxIn
 set stPar := bpc n h' H_row xDual excl s 0 stIn
 have hle2P : st2.1 ≤ stPar.1 := by rw [← hIn_1]; exact hPar_le
 have hle0P : st.1 ≤ stPar.1 := le_trans hle02 hle2P
 set wires0 : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun u => if hu : u < n then xDual ⟨u, hu⟩ else fd
 have hwires0 : ∀ u, VL stPar.1 (wires0 u).1 ∧ VL stPar.1 (wires0 u).2 := fun u => by
   dsimp only [wires0]
   split_ifs
   · exact ⟨(hv_in _).2.2.2.1.mono hle2P, (hv_in _).2.2.2.2.mono hle2P⟩
   · exact ⟨hf1.mono hle0P, hf2.mono hle0P⟩
 have hexPar : VL stPar.1 excl := hexIn.mono hPar_le
 have hex_val2 : lEv α2 excl = false := (lecl h2inl h2lt hexIn).trans hex_val
 have hfval2 : lEv α2 fd.1 = false ∧ lEv α2 fd.2 = true :=
   ⟨(lecl h2inl h2lt (hf1.mono (le_trans hle02 (by omega)))).trans
       ((lecl h1inl h1lt hf1).trans hfval.1),
   (lecl h2inl h2lt (hf2.mono (le_trans hle02 (by omega)))).trans
       ((lecl h1inl h1lt hf2).trans hfval.2)⟩
 have hlt0 : ∀ u < n + 0, dv n gates u ≤ D →
     lEv α2 (wires0 u).1 = wv n x gates u ∧
     lEv α2 (wires0 u).2 = !(wv n x gates u) := by
   intro u hu _
   have hu' : u < n := by omega
   have hwv : wv n x gates u = x ⟨u, hu'⟩ := by rw [wv]; simp [hu']
   rw [hwv]
   dsimp only [wires0]
   simp only [hu', ↓reduceDIte]
   rw [lecl h2inl h2lt ((hv_in ⟨u, hu'⟩).2.2.2.1.mono (by omega)),
       lecl h2inl h2lt ((hv_in ⟨u, hu'⟩).2.2.2.2.mono (by omega))]
   exact hxDual_val ⟨u, hu'⟩
 have hge0 : ∀ u ≥ n + gates.length, lEv α2 (wires0 u).1 = false ∧ lEv α2 (wires0 u).2 = true := by
   intro u hu
   have hnotn : ¬ (u < n) := by omega
   dsimp only [wires0]
   simp only [hnotn, ↓reduceDIte]
   exact hfval2
 obtain ⟨α3, h3lt, h3inl, h3sat, h3res_lt, h3res_ge⟩ :=
   bcg_sa n D gates fd (some excl) x gates.length 0 (Nat.sub_zero _)
     wires0 stPar α2 hstPar (hf1.mono hle0P) (hf2.mono hle0P) (fun _ h => by cases h; exact hexPar)
     hwires0 h2sat (fun _ h => by cases h; exact hex_val2) hfval2 hlt0 hge0
 obtain ⟨hstG, hGle, _, _, _, hGw, _, _⟩ :=
   bcg_pr n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar
     hstPar (hf1.mono hle0P) (hf2.mono hle0P) (fun _ h => by cases h; exact hexPar) hwires0
 set resG := bcg n D gates fd (some excl) 0 wires0 stPar
 have hwires_eq := (wires_length_and_getD n x gates).2
 have hsat_out : ∀ C ∈ (boc out resG.1 (some excl) 0 resG.2).2, ClauseSat α3 C := by
   refine boc_sat out resG.1 (some excl) α3 t 0 (Nat.sub_zero _) resG.2 h3sat (Or.inr fun jf _ => ?_)
   have hagr : α3 (Sum.inl (Sum.inr jf)) = wv n x gates (out jf) := by
     rw [h3inl, h2inl, h1inl, hag jf, hwires_eq]
   by_cases hlt : out jf < n + gates.length
   · have hres := h3res_lt (out jf) hlt (hD_bound jf)
     rw [hagr]
     exact ⟨fun h => by rw [hres.1] at h; exact h,
           fun h => by rw [hres.2] at h; cases hwv : wv n x gates (out jf) <;> simp [hwv] at h ⊢⟩
   · have hge : out jf ≥ n + gates.length := by omega
     have hres := h3res_ge (out jf) hge
     have hwv : wv n x gates (out jf) = false := by
       rw [wv]; simp [show ¬ (out jf < n) by omega, hlt]
     rw [hagr, hwv]
     exact ⟨(fun h => by rw [hres.1] at h; cases h), fun _ => rfl⟩
 refine ⟨α3, fun v => (h3inl v).trans ((h2inl v).trans (h1inl v)), fun k hk => ?_, hsat_out, ?_, ?_, ?_⟩
 · exact (h3lt k (lt_of_lt_of_le hk hle0P)).trans ((h2lt k (lt_of_lt_of_le hk (by omega))).trans (h1lt k hk))
 · rw [lecl h3inl h3lt hexPar, lecl h2inl h2lt hexIn, hex_val]
 · intro i
   rw [lecl h3inl h3lt ((hv_in i).2.2.2.1.mono hle2P),
       lecl h3inl h3lt ((hv_in i).2.2.2.2.mono hle2P),
       lecl h2inl h2lt ((hv_in i).2.2.2.1.mono (by omega)),
       lecl h2inl h2lt ((hv_in i).2.2.2.2.mono (by omega))]
   exact hxDual_val i
 · intro jf
   have hagr : α (Sum.inl (Sum.inr jf)) = wv n x gates (out jf) := by
     rw [hag jf, hwires_eq]
   rw [hagr]
   by_cases hlt : out jf < n + gates.length
   · exact h3res_lt (out jf) hlt (hD_bound jf)
   · have hge : out jf ≥ n + gates.length := by omega
     have hwv : wv n x gates (out jf) = false := by
       rw [wv]; simp [show ¬ (out jf < n) by omega, hlt]
     rw [hwv]
     exact h3res_ge (out jf) hge

lemma bb_si (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t)) (α : Sum (Fin n ⊕ Fin t) ℕ → Bool)
   (hst : VS st)
   (hf1 : VL st.1 fd.1) (hf2 : VL st.1 fd.2)
   (hw : ∀ i b, VL st.1 (wRow i b))
   (hsat : ∀ C ∈ st.2, ClauseSat α C) :
   let br := bb n t h' D gates out H_row wRow fd s st
   ∃ α' : Sum (Fin n ⊕ Fin t) ℕ → Bool,
     (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
     (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
     (∀ C ∈ br.stOut.2, ClauseSat α' C) ∧
     lEv α' br.excl = true := by
 dsimp only [bb]
 set pEx := fv st
 set excl := pEx.1
 set base := pEx.2.1
 set xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun i => (ag n base i false, ag n base i true)
 set st2 : St (Fin n ⊕ Fin t) := (base + 2 * n, pEx.2.2)
 set rawIn : Fin n → LN (Fin n ⊕ Fin t) := fun i => (Sum.inl (Sum.inl i), true)
 let α1 : Sum (Fin n ⊕ Fin t) ℕ → Bool := fun z =>
   match z with
   | Sum.inl v => α (Sum.inl v)
   | Sum.inr k => if k < st.1 then α (Sum.inr k) else true
 have h1inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
 have h1lt : ∀ k < st.1, α1 (Sum.inr k) = α (Sum.inr k) := fun k hk => by simp [α1, hk]
 have hst2v : VS st2 := fun C hC =>
   ⟨(hst C hC).1, (hst C hC).2.mono (by dsimp only [st2, base, pEx, fv]; omega)⟩
 have hst2_1 : st2.1 = st.1 + 1 + 2 * n := rfl
 have hex2 : VL st2.1 excl := (validLit_fresh st).mono (by rw [hst2_1]; omega)
 have hle02 : st.1 ≤ st2.1 := by omega
 have hv_in : ∀ j, VL st2.1 (rawIn j) ∧ VL st2.1 (wRow j false) ∧ VL st2.1 (wRow j true) ∧
     VL st2.1 (xDual j).1 ∧ VL st2.1 (xDual j).2 := fun j =>
   ⟨validLit_inl _ _ _, (hw j false).mono hle02, (hw j true).mono hle02,
   validLit_allocGrid _ n base j false, validLit_allocGrid _ n base j true⟩
 have hsat2 : ∀ C ∈ st2.2, ClauseSat α1 C := fun C hC =>
   (cscl h1inl h1lt (hst C hC).2).2 (hsat C hC)
 have hex_val : lEv α1 excl = true := by simp [excl, pEx, fv, lEv, α1]
 have hxDual_val : ∀ i, lEv α1 (xDual i).1 = true ∧ lEv α1 (xDual i).2 = true := by
   intro i
   dsimp only [xDual]
   rw [litEval_allocGrid, litEval_allocGrid]
   have hbase : base = st.1 + 1 := rfl
   have hc1 : ¬ (base + 2 * i.val < st.1) := by omega
   have hd1 : ¬ (base + 2 * i.val + 1 < st.1) := by omega
   simp [α1, hc1, hd1]
 have hsatIn : ∀ C ∈ (bbi n rawIn wRow xDual excl 0 st2).2, ClauseSat α1 C :=
   bbi_si n rawIn wRow xDual excl α1 n 0 (Nat.sub_zero _) st2 hsat2 hex_val hxDual_val
 obtain ⟨hstIn, hIn_1, _, _, _⟩ :=
   bbi_pr n rawIn wRow xDual excl n 0 (Nat.sub_zero _) st2 hst2v hex2 hv_in
 set stIn := bbi n rawIn wRow xDual excl 0 st2
 have hexIn : VL stIn.1 excl := by rw [hIn_1]; exact hex2
 have hxIn : ∀ i, VL stIn.1 (xDual i).1 ∧ VL stIn.1 (xDual i).2 := fun i => by
   rw [hIn_1]; exact ⟨(hv_in i).2.2.2.1, (hv_in i).2.2.2.2⟩
 obtain ⟨α2, h2inl, h2lt, h2sat⟩ :=
   bpc_si n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn α1
     hstIn hexIn hxIn hsatIn hex_val
 obtain ⟨hstPar, hPar_le, _, _, _⟩ :=
   bpc_pr n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn hstIn hexIn hxIn
 set stPar := bpc n h' H_row xDual excl s 0 stIn
 have hle2P : st2.1 ≤ stPar.1 := by rw [← hIn_1]; exact hPar_le
 have hle0P : st.1 ≤ stPar.1 := le_trans hle02 hle2P
 set wires0 : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun u => if hu : u < n then xDual ⟨u, hu⟩ else fd
 have hwires0 : ∀ u, VL stPar.1 (wires0 u).1 ∧ VL stPar.1 (wires0 u).2 := fun u => by
   dsimp only [wires0]
   split_ifs
   · exact ⟨(hv_in _).2.2.2.1.mono hle2P, (hv_in _).2.2.2.2.mono hle2P⟩
   · exact ⟨hf1.mono hle0P, hf2.mono hle0P⟩
 have hexPar : VL stPar.1 excl := hexIn.mono hPar_le
 have hex_val2 : lEv α2 excl = true := (lecl h2inl h2lt hexIn).trans hex_val
 obtain ⟨α3, h3lt, h3inl, h3sat⟩ :=
   bcg_si n D gates fd excl gates.length 0 (Nat.sub_zero _)
     wires0 stPar α2 hstPar (hf1.mono hle0P) (hf2.mono hle0P) hexPar hwires0 h2sat hex_val2
 obtain ⟨hstG, hGle, _, _, _, _, _, _⟩ :=
   bcg_pr n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar
     hstPar (hf1.mono hle0P) (hf2.mono hle0P) (fun _ h => by cases h; exact hexPar) hwires0
 set resG := bcg n D gates fd (some excl) 0 wires0 stPar
 have hex_val3 : lEv α3 excl = true := (lecl h3inl h3lt hexPar).trans hex_val2
 have hsat_out : ∀ C ∈ (boc out resG.1 (some excl) 0 resG.2).2, ClauseSat α3 C :=
   boc_sat out resG.1 (some excl) α3 t 0 (Nat.sub_zero _) resG.2 h3sat
     (Or.inl ⟨excl, rfl, hex_val3⟩)
 refine ⟨α3, fun v => (h3inl v).trans ((h2inl v).trans (h1inl v)), fun k hk => ?_, hsat_out, hex_val3⟩
 exact (h3lt k (lt_of_lt_of_le hk hle0P)).trans ((h2lt k (lt_of_lt_of_le hk (by omega))).trans (h1lt k hk))

lemma bb_up (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t))
   (F : Finset (CN (Fin n ⊕ Fin t))) (seed : Set (LN (Fin n ⊕ Fin t)))
   (d0 : ℕ) (x' : Fin n → Bool)
   (hst : VS st) (hf1 : VL st.1 fd.1) (hf2 : VL st.1 fd.2)
   (hw : ∀ i b, VL st.1 (wRow i b))
   (hF : ∀ C ∈ (bb n t h' D gates out H_row wRow fd s st).stOut.2, C ∈ F)
   (hx_in : ∀ j : Fin n,
     fLt (Sum.inl (Sum.inl j), true) (x' j) ∈ (upS F)^[d0] seed ∨
       wRow j (x' j) ∈ (upS F)^[d0] seed)
   (hf_up : fd.2 ∈ (upS F)^[1] seed) :
   let br := bb n t h' D gates out H_row wRow fd s st
   (∀ i, lod (br.xDual i) (x' i) ∈ (upS F)^[d0 + 1] seed) ∧
   (∀ q : Fin h',
     s.val.testBit q.val ≠ xl (((List.finRange n).filter (fun i => H_row q i)).map x') →
     br.excl ∈ (upS F)^[d0 + 1 + Nat.clog 2 (n + 1) + 1] seed) ∧
   (∀ u < n + gates.length, dv n gates u ≤ D →
     lod (br.wiresOut u) (wv n x' gates u) ∈ (upS F)^[d0 + 1 + dv n gates u] seed) ∧
   (∀ j : Fin t, dv n gates (out j) ≤ D →
     lod (br.wiresOut (out j)) (wv n x' gates (out j)) ∈ (upS F)^[d0 + 1 + D] seed) ∧
   (∀ j : Fin t, ∀ sign : Bool,
     dv n gates (out j) ≤ D →
     (Sum.inl (Sum.inr j), sign) ∈ seed →
     wv n x' gates (out j) ≠ sign →
     br.excl ∈ (upS F)^[d0 + 1 + D + 1] seed) := by
 dsimp only [bb] at hF ⊢
 set pEx := fv st
 set excl := pEx.1
 set base := pEx.2.1
 set xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun i => (ag n base i false, ag n base i true)
 set st2 : St (Fin n ⊕ Fin t) := (base + 2 * n, pEx.2.2)
 set rawIn : Fin n → LN (Fin n ⊕ Fin t) := fun i => (Sum.inl (Sum.inl i), true)
 set stIn := bbi n rawIn wRow xDual excl 0 st2
 set stPar := bpc n h' H_row xDual excl s 0 stIn
 set wires0 : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun u => if hu : u < n then xDual ⟨u, hu⟩ else fd
 set resG := bcg n D gates fd (some excl) 0 wires0 stPar
 have hst2v : VS st2 := fun C hC =>
   ⟨(hst C hC).1, (hst C hC).2.mono (by dsimp only [st2, base, pEx, fv]; omega)⟩
 have hst2_1 : st2.1 = st.1 + 1 + 2 * n := rfl
 have hex2 : VL st2.1 excl := (validLit_fresh st).mono (by rw [hst2_1]; omega)
 have hle02 : st.1 ≤ st2.1 := by omega
 have hv_in : ∀ j, VL st2.1 (rawIn j) ∧ VL st2.1 (wRow j false) ∧ VL st2.1 (wRow j true) ∧
     VL st2.1 (xDual j).1 ∧ VL st2.1 (xDual j).2 := fun j =>
   ⟨validLit_inl _ _ _, (hw j false).mono hle02, (hw j true).mono hle02,
   validLit_allocGrid _ n base j false, validLit_allocGrid _ n base j true⟩
 obtain ⟨hstIn, hIn_1, _, _, _⟩ :=
   bbi_pr n rawIn wRow xDual excl n 0 (Nat.sub_zero _) st2 hst2v hex2 hv_in
 have hexIn : VL stIn.1 excl := by rw [hIn_1]; exact hex2
 have hxIn : ∀ i, VL stIn.1 (xDual i).1 ∧ VL stIn.1 (xDual i).2 := fun i => by
   rw [hIn_1]; exact ⟨(hv_in i).2.2.2.1, (hv_in i).2.2.2.2⟩
 obtain ⟨hstPar, hPar_le, _, _, _⟩ :=
   bpc_pr n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn hstIn hexIn hxIn
 have hle2P : st2.1 ≤ stPar.1 := by rw [← hIn_1]; exact hPar_le
 have hle0P : st.1 ≤ stPar.1 := le_trans hle02 hle2P
 have hwires0 : ∀ u, VL stPar.1 (wires0 u).1 ∧ VL stPar.1 (wires0 u).2 := fun u => by
   dsimp only [wires0]
   split_ifs
   · exact ⟨(hv_in _).2.2.2.1.mono hle2P, (hv_in _).2.2.2.2.mono hle2P⟩
   · exact ⟨hf1.mono hle0P, hf2.mono hle0P⟩
 have hexPar : VL stPar.1 excl := hexIn.mono hPar_le
 obtain ⟨hstG, _, _, _, _, hGw, _, hGge⟩ :=
   bcg_pr n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar
     hstPar (hf1.mono hle0P) (hf2.mono hle0P) (fun _ h => by cases h; exact hexPar) hwires0
 have hexG : ∀ ex, some excl = some ex → VL resG.2.1 ex := by
   intro ex h; cases h
   exact hexPar.mono (by omega)
 obtain ⟨_, _, _, _, hOmem⟩ :=
   boc_pr out resG.1 (some excl) t 0 (Nat.sub_zero _) resG.2 hstG hexG hGw
 have hF_G : ∀ C ∈ resG.2.2, C ∈ F := fun C hC =>
   hF C (boc_cm out resG.1 (some excl) t 0 (Nat.sub_zero _) resG.2 C hC)
 have hF_Par : ∀ C ∈ stPar.2, C ∈ F := fun C hC =>
   hF_G C (bcg_cm n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar C hC)
 have hF_In : ∀ C ∈ stIn.2, C ∈ F := fun C hC =>
   hF_Par C (bpc_cm n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn C hC)
 have hxDual_up : ∀ j : Fin n, lod (xDual j) (x' j) ∈ (upS F)^[d0 + 1] seed :=
   bbi_up n F seed rawIn wRow xDual excl st2 d0 x' hF_In hx_in
 have hx_inj : ∀ i j : Fin n, xDual i = xDual j → i = j := by
   intro i j h
   have h1 := congrArg (fun p => p.1.1) h
   simp only [xDual, ag, Sum.inr.injEq, ↓reduceIte, Bool.false_eq_true] at h1
   exact Fin.ext (by omega)
 have hpar_up : ∀ q : Fin h',
     s.val.testBit q.val ≠ xl (((List.finRange n).filter (fun i => H_row q i)).map x') →
     excl ∈ (upS F)^[d0 + 1 + Nat.clog 2 (n + 1) + 1] seed := fun q hne =>
   bpc_up n h' F seed H_row xDual excl s (d0 + 1) x' hx_inj q h' 0 (Nat.sub_zero _)
     (Nat.zero_le _) stIn hF_Par hxDual_up hne
 have hup_gates : ∀ u < n + gates.length, dv n gates u ≤ D →
     lod (resG.1 u) (wv n x' gates u) ∈ (upS F)^[d0 + 1 + dv n gates u] seed := by
   have hf_d0 : lod fd false ∈ (upS F)^[d0 + 1 + 0] seed := by
     have h1 : fd.2 ∈ (upS F)^[d0 + 1 + 0] seed := upStep_iter_le F seed (by omega) hf_up
     simpa [lod] using h1
   refine bcg_up n D gates fd (some excl) x' F
     (fun d => (upS F)^[d0 + 1 + d] seed)
     (fun d => upStep_iter_le F seed (by omega))
     (fun d => by rw [show d0 + 1 + (d + 1) = (d0 + 1 + d) + 1 by omega, Function.iterate_succ_apply'])
     gates.length 0 (Nat.sub_zero _) wires0 stPar hF_G hf_d0 ?_
   intro u hu _
   have hu' : u < n := by omega
   have hdep0 : dv n gates u = 0 := by rw [dv]; simp [hu']
   have hwv : wv n x' gates u = x' ⟨u, hu'⟩ := by rw [wv]; simp [hu']
   rw [hdep0, hwv]
   dsimp only [wires0]
   simp only [hu', ↓reduceDIte]
   exact hxDual_up ⟨u, hu'⟩
 have hup_out : ∀ j : Fin t, dv n gates (out j) ≤ D →
     lod (resG.1 (out j)) (wv n x' gates (out j)) ∈ (upS F)^[d0 + 1 + D] seed := by
   intro j hjD
   by_cases hlt : out j < n + gates.length
   · exact upStep_iter_le F seed (by omega) (hup_gates (out j) hlt hjD)
   · have hge : out j ≥ n + gates.length := by omega
     have hwv : wv n x' gates (out j) = false := by
       rw [wv]; simp [show ¬ (out j < n) by omega, hlt]
     have hres_eq : resG.1 (out j) = wires0 (out j) := hGge (out j) hge
     have hnotn : ¬ (out j < n) := by omega
     rw [hwv, hres_eq]
     dsimp only [wires0]
     simp only [hnotn, ↓reduceDIte, lod, Bool.false_eq_true]
     exact upStep_iter_le F seed (by omega) hf_up
 refine ⟨hxDual_up, hpar_up, hup_gates, hup_out, fun j sign hjD hseed hne => ?_⟩
 have hom := hOmem j (Nat.zero_le _)
 simp only at hom
 have hseed' : (Sum.inl (Sum.inr j), sign) ∈ (upS F)^[d0 + 1 + D] seed := by
   have h0 : (Sum.inl (Sum.inr j), sign) ∈ (upS F)^[0] seed := by simpa using hseed
   exact upStep_iter_le F seed (Nat.zero_le _) h0
 have hout_mem := hup_out j hjD
 rw [show d0 + 1 + D + 1 = (d0 + 1 + D) + 1 by omega, Function.iterate_succ_apply']
 cases hsign : sign
 · have htrue : wv n x' gates (out j) = true := by
     cases hw : wv n x' gates (out j) <;> simp [hw, hsign] at hne ⊢
   have h1 : (resG.1 (out j)).1 ∈ (upS F)^[d0 + 1 + D] seed := by
     simpa [lod, htrue] using hout_mem
   have hC : ({negL (resG.1 (out j)).1, negL (Sum.inl (Sum.inr j), false), excl} :
       CN (Fin n ⊕ Fin t)) ∈ F := hF _ hom.1
   exact upStep_unit3 hC (by rw [negL_negL]; exact h1)
     (by rw [negL_negL, ← hsign]; exact hseed')
 · have hfalse : wv n x' gates (out j) = false := by
     cases hw : wv n x' gates (out j) <;> simp [hw, hsign] at hne ⊢
   have h2 : (resG.1 (out j)).2 ∈ (upS F)^[d0 + 1 + D] seed := by
     simpa [lod, hfalse] using hout_mem
   have hC : ({negL (resG.1 (out j)).2, negL (Sum.inl (Sum.inr j), true), excl} :
       CN (Fin n ⊕ Fin t)) ∈ F := hF _ hom.2
   exact upStep_unit3 hC (by rw [negL_negL]; exact h2)
     (by rw [negL_negL, ← hsign]; exact hseed')

def bbr (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ℕ → (Fin (2 ^ h') → BR n t) → St (Fin n ⊕ Fin t) →
     (Fin (2 ^ h') → BR n t) × St (Fin n ⊕ Fin t)
 | s, arr, st =>
   if hs : s < 2 ^ h' then
     let sf : Fin (2 ^ h') := ⟨s, hs⟩
     let br := bb n t h' D gates out H_row (fun i => wRow i sf) fd sf st
     let arr' : Fin (2 ^ h') → BR n t := fun s' => if s' = sf then br else arr s'
     bbr n t h' D gates out H_row wRow fd (s + 1) arr' br.stOut
   else (arr, st)
termination_by s => 2 ^ h' - s

lemma bbr_cm (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ∀ (m s : ℕ) (_ : 2 ^ h' - s = m) (arr : Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (C : CN (Fin n ⊕ Fin t)),
     C ∈ st.2 → C ∈ (bbr n t h' D gates out H_row wRow fd s arr st).2.2
 | 0, s, hm, arr, st, C, hC => by
   have hge : ¬ (s < 2 ^ h') := by omega
   unfold bbr; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, s, hm, arr, st, C, hC => by
   have hs : s < 2 ^ h' := by omega
   have hm1 : 2 ^ h' - (s + 1) = m := by omega
   unfold bbr; simp only [hs, ↓reduceDIte]
   apply bbr_cm n t h' D gates out H_row wRow fd m (s + 1) hm1 _ _ C
   exact bb_cm n t h' D gates out H_row _ fd ⟨s, hs⟩ st C hC

lemma bbr_uc (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ∀ (m s : ℕ) (_ : 2 ^ h' - s = m) (arr : Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (sf : Fin (2 ^ h')), sf.val < s →
     (bbr n t h' D gates out H_row wRow fd s arr st).1 sf = arr sf
 | 0, s, hm, arr, st, sf, _ => by
   have hge : ¬ (s < 2 ^ h') := by omega
   unfold bbr; simp only [hge, ↓reduceDIte]
 | m + 1, s, hm, arr, st, sf, hsf => by
   have hs : s < 2 ^ h' := by omega
   have hm1 : 2 ^ h' - (s + 1) = m := by omega
   unfold bbr; simp only [hs, ↓reduceDIte]
   have hne : sf ≠ ⟨s, hs⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [bbr_uc n t h' D gates out H_row wRow fd m (s + 1) hm1 _ _ sf (by omega)]
   simp [hne]

lemma bbr_pr (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ∀ (m s : ℕ) (_ : 2 ^ h' - s = m) (arr : Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t)),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ i s' b, VL st.1 (wRow i s' b)) →
     (∀ sf : Fin (2 ^ h'), sf.val < s →
       VL st.1 (arr sf).excl ∧
       (∀ i, VL st.1 ((arr sf).xDual i).1 ∧ VL st.1 ((arr sf).xDual i).2) ∧
       (∀ u, VL st.1 ((arr sf).wiresOut u).1 ∧ VL st.1 ((arr sf).wiresOut u).2)) →
     let res := bbr n t h' D gates out H_row wRow fd s arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + (1 + 2 * n + 4 * n * h' + 2 * gates.length) * m ∧
     res.2.2.length ≤ st.2.length + (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * m ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ sf : Fin (2 ^ h'),
       VL res.2.1 (res.1 sf).excl ∧
       (∀ i, VL res.2.1 ((res.1 sf).xDual i).1 ∧ VL res.2.1 ((res.1 sf).xDual i).2) ∧
       (∀ u, VL res.2.1 ((res.1 sf).wiresOut u).1 ∧ VL res.2.1 ((res.1 sf).wiresOut u).2))
 | 0, s, hm, arr, st, hst, _, _, _, harr => by
   have hge : ¬ (s < 2 ^ h') := by omega
   unfold bbr; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun sf => harr sf (by omega)⟩
 | m + 1, s, hm, arr, st, hst, hf1, hf2, hw, harr => by
   have hs : s < 2 ^ h' := by omega
   have hm1 : 2 ^ h' - (s + 1) = m := by omega
   unfold bbr; simp only [hs, ↓reduceDIte]
   set sf : Fin (2 ^ h') := ⟨s, hs⟩
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hex1, hx1, hw1⟩ :=
     bb_pr n t h' D gates out H_row (fun i => wRow i sf) fd sf st hst hf1 hf2 (fun i b => hw i sf b)
   set br := bb n t h' D gates out H_row (fun i => wRow i sf) fd sf st
   let arr' : Fin (2 ^ h') → BR n t := fun s' => if s' = sf then br else arr s'
   have harr' : ∀ sf' : Fin (2 ^ h'), sf'.val < s + 1 →
       VL br.stOut.1 (arr' sf').excl ∧
       (∀ i, VL br.stOut.1 ((arr' sf').xDual i).1 ∧ VL br.stOut.1 ((arr' sf').xDual i).2) ∧
       (∀ u, VL br.stOut.1 ((arr' sf').wiresOut u).1 ∧ VL br.stOut.1 ((arr' sf').wiresOut u).2) := by
     intro sf' hsf'
     dsimp only [arr']
     split_ifs with heq
     · exact ⟨hex1, hx1, hw1⟩
     · have hlt : sf'.val < s := by have hne : sf'.val ≠ s := fun h => heq (Fin.ext h); omega
       exact ⟨(harr sf' hlt).1.mono hle1,
             fun i => ⟨((harr sf' hlt).2.1 i).1.mono hle1, ((harr sf' hlt).2.1 i).2.mono hle1⟩,
             fun u => ⟨((harr sf' hlt).2.2 u).1.mono hle1, ((harr sf' hlt).2.2 u).2.mono hle1⟩⟩
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     bbr_pr n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut
       hst1 (hf1.mono hle1) (hf2.mono hle1) (fun i s' b => (hw i s' b).mono hle1) harr'
   refine ⟨r1, le_trans hle1 r2, ?_, ?_, fun C hC => r5 C (hsub1 C hC), r6⟩
   · calc (bbr n t h' D gates out H_row wRow fd (s + 1) arr' br.stOut).2.1
       _ ≤ br.stOut.1 + (1 + 2 * n + 4 * n * h' + 2 * gates.length) * m := r3
       _ ≤ (st.1 + (1 + 2 * n + 4 * n * h' + 2 * gates.length)) +
           (1 + 2 * n + 4 * n * h' + 2 * gates.length) * m := Nat.add_le_add_right hm1_v _
       _ = st.1 + (1 + 2 * n + 4 * n * h' + 2 * gates.length) * (m + 1) := by ring
   · calc (bbr n t h' D gates out H_row wRow fd (s + 1) arr' br.stOut).2.2.length
       _ ≤ br.stOut.2.length + (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * m := r4
       _ ≤ (st.2.length + (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t)) +
           (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * m := Nat.add_le_add_right hl1_c _
       _ = st.2.length + (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * (m + 1) := by ring

lemma bbr_sat (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D) :
   ∀ (m s : ℕ) (_ : 2 ^ h' - s = m) (arr : Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (α : Sum (Fin n ⊕ Fin t) ℕ → Bool),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ i s' b, VL st.1 (wRow i s' b)) →
     (∀ sf : Fin (2 ^ h'), sf.val < s →
       VL st.1 (arr sf).excl ∧
       (∀ i, VL st.1 ((arr sf).xDual i).1 ∧ VL st.1 ((arr sf).xDual i).2) ∧
       (∀ u, VL st.1 ((arr sf).wiresOut u).1 ∧ VL st.1 ((arr sf).wiresOut u).2)) →
     (∀ C ∈ st.2, ClauseSat α C) →
     (lEv α fd.1 = false ∧ lEv α fd.2 = true) →
     (∀ sf : Fin (2 ^ h'), (∀ q : Fin h', sf.val.testBit q.val =
       xl (((List.finRange n).filter (fun i => H_row q i)).map (fun i => α (Sum.inl (Sum.inl i))))) →
       ∀ i b, lEv α (wRow i sf b) = true → α (Sum.inl (Sum.inl i)) = b) →
     (∀ j : Fin t, α (Sum.inl (Sum.inr j)) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => α (Sum.inl (Sum.inl i))))).getD (out j) false) →
     ∃ α' : Sum (Fin n ⊕ Fin t) ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bbr n t h' D gates out H_row wRow fd s arr st).2.2, ClauseSat α' C) ∧
       ∀ sf : Fin (2 ^ h'), s ≤ sf.val →
         let br := (bbr n t h' D gates out H_row wRow fd s arr st).1 sf
         (lEv α' br.excl = decide (∃ q : Fin h', sf.val.testBit q.val ≠
           xl (((List.finRange n).filter (fun i => H_row q i)).map (fun i => α (Sum.inl (Sum.inl i)))))) ∧
         (lEv α' br.excl = false →
           (∀ i, lEv α' (br.xDual i).1 = α (Sum.inl (Sum.inl i)) ∧
                 lEv α' (br.xDual i).2 = !(α (Sum.inl (Sum.inl i)))) ∧
           (∀ j : Fin t, lEv α' (br.wiresOut (out j)).1 = α (Sum.inl (Sum.inr j)) ∧
                         lEv α' (br.wiresOut (out j)).2 = !(α (Sum.inl (Sum.inr j)))))
 | 0, s, hm, arr, st, α, _, _, _, _, _, hsat, _, _, _ => by
   have hge : ¬ (s < 2 ^ h') := by omega
   unfold bbr; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun sf hsf => by exfalso; omega⟩
 | m + 1, s, hm, arr, st, α, hst, hf1, hf2, hw, harr, hsat, hfval, hww, hag => by
   have hs : s < 2 ^ h' := by omega
   have hm1 : 2 ^ h' - (s + 1) = m := by omega
   unfold bbr; simp only [hs, ↓reduceDIte]
   set sf : Fin (2 ^ h') := ⟨s, hs⟩
   obtain ⟨hst1, hle1, _, _, _, hex1, hx1, hw1⟩ :=
     bb_pr n t h' D gates out H_row (fun i => wRow i sf) fd sf st hst hf1 hf2 (fun i b => hw i sf b)
   set br := bb n t h' D gates out H_row (fun i => wRow i sf) fd sf st
   let arr' : Fin (2 ^ h') → BR n t := fun s' => if s' = sf then br else arr s'
   have harr' : ∀ sf' : Fin (2 ^ h'), sf'.val < s + 1 →
       VL br.stOut.1 (arr' sf').excl ∧
       (∀ i, VL br.stOut.1 ((arr' sf').xDual i).1 ∧ VL br.stOut.1 ((arr' sf').xDual i).2) ∧
       (∀ u, VL br.stOut.1 ((arr' sf').wiresOut u).1 ∧ VL br.stOut.1 ((arr' sf').wiresOut u).2) := by
     intro sf' hsf'
     dsimp only [arr']
     split_ifs with heq
     · exact ⟨hex1, hx1, hw1⟩
     · have hlt : sf'.val < s := by have hne : sf'.val ≠ s := fun h => heq (Fin.ext h); omega
       exact ⟨(harr sf' hlt).1.mono hle1,
             fun i => ⟨((harr sf' hlt).2.1 i).1.mono hle1, ((harr sf' hlt).2.1 i).2.mono hle1⟩,
             fun u => ⟨((harr sf' hlt).2.2 u).1.mono hle1, ((harr sf' hlt).2.2 u).2.mono hle1⟩⟩
   by_cases hsyn : ∀ q : Fin h', sf.val.testBit q.val =
       xl (((List.finRange n).filter (fun i => H_row q i)).map (fun i => α (Sum.inl (Sum.inl i))))
   · obtain ⟨α1, h1inl, h1lt, h1sat, h1ex, h1x, h1w⟩ :=
       bb_sa n t h' D gates out H_row (fun i => wRow i sf) fd sf st α
         hst hf1 hf2 (fun i b => hw i sf b) hsat hfval (hww sf hsyn) hsyn hag hD_bound
     have hfval1 : lEv α1 fd.1 = false ∧ lEv α1 fd.2 = true :=
       ⟨(lecl h1inl h1lt hf1).trans hfval.1, (lecl h1inl h1lt hf2).trans hfval.2⟩
     have hww1 : ∀ sf' : Fin (2 ^ h'), (∀ q : Fin h', sf'.val.testBit q.val =
         xl (((List.finRange n).filter (fun i => H_row q i)).map (fun i => α1 (Sum.inl (Sum.inl i))))) →
         ∀ i b, lEv α1 (wRow i sf' b) = true → α1 (Sum.inl (Sum.inl i)) = b := by
       intro sf' hsyn' i b hwb
       rw [h1inl]
       apply hww sf' (fun q => by rw [hsyn' q]; congr 1; exact List.map_congr_left fun j _ => h1inl _) i b
       rw [← lecl h1inl h1lt (hw i sf' b)]
       exact hwb
     have hag1 : ∀ j : Fin t, α1 (Sum.inl (Sum.inr j)) =
         ((⟨gates, 0⟩ : BinaryCircuit).wires
           (List.ofFn (fun i : Fin n => α1 (Sum.inl (Sum.inl i))))).getD (out j) false := by
       intro j; rw [h1inl, hag j]; congr 2; exact congrArg List.ofFn (funext fun i => (h1inl _).symm)
     obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
       bbr_sat n t h' D gates out H_row wRow fd hD_bound m (s + 1) hm1 arr' br.stOut α1
         hst1 (hf1.mono hle1) (hf2.mono hle1) (fun i s' b => (hw i s' b).mono hle1) harr' h1sat hfval1 hww1 hag1
     refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun k hk => (h'lt k (lt_of_lt_of_le hk hle1)).trans (h1lt k hk),
       h'sat, fun sf' hsf' => ?_⟩
     by_cases heq : s = sf'.val
     · have hsfeq : sf' = sf := Fin.ext heq.symm
       subst hsfeq
       rw [bbr_uc n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut sf (by change sf.val < s + 1; omega)]
       dsimp only [arr']
       rw [if_pos rfl]
       have hex_eq : lEv α' br.excl = false := (lecl h'inl h'lt hex1).trans h1ex
       refine ⟨?_, ?_⟩
       · rw [hex_eq]; symm; rw [decide_eq_false_iff_not]; push_neg; exact hsyn
       · intro _
         refine ⟨fun i => ?_, fun j => ?_⟩
         · rw [lecl h'inl h'lt (hx1 i).1, lecl h'inl h'lt (hx1 i).2]
           exact h1x i
         · rw [lecl h'inl h'lt (hw1 (out j)).1, lecl h'inl h'lt (hw1 (out j)).2]
           exact h1w j
     · have hr := h'res sf' (by omega)
       simpa only [h1inl] using hr
   · obtain ⟨α1, h1inl, h1lt, h1sat, h1ex⟩ :=
       bb_si n t h' D gates out H_row (fun i => wRow i sf) fd sf st α
         hst hf1 hf2 (fun i b => hw i sf b) hsat
     have hfval1 : lEv α1 fd.1 = false ∧ lEv α1 fd.2 = true :=
       ⟨(lecl h1inl h1lt hf1).trans hfval.1, (lecl h1inl h1lt hf2).trans hfval.2⟩
     have hww1 : ∀ sf' : Fin (2 ^ h'), (∀ q : Fin h', sf'.val.testBit q.val =
         xl (((List.finRange n).filter (fun i => H_row q i)).map (fun i => α1 (Sum.inl (Sum.inl i))))) →
         ∀ i b, lEv α1 (wRow i sf' b) = true → α1 (Sum.inl (Sum.inl i)) = b := by
       intro sf' hsyn' i b hwb
       rw [h1inl]
       apply hww sf' (fun q => by rw [hsyn' q]; congr 1; exact List.map_congr_left fun j _ => h1inl _) i b
       rw [← lecl h1inl h1lt (hw i sf' b)]
       exact hwb
     have hag1 : ∀ j : Fin t, α1 (Sum.inl (Sum.inr j)) =
         ((⟨gates, 0⟩ : BinaryCircuit).wires
           (List.ofFn (fun i : Fin n => α1 (Sum.inl (Sum.inl i))))).getD (out j) false := by
       intro j; rw [h1inl, hag j]; congr 2; exact congrArg List.ofFn (funext fun i => (h1inl _).symm)
     obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
       bbr_sat n t h' D gates out H_row wRow fd hD_bound m (s + 1) hm1 arr' br.stOut α1
         hst1 (hf1.mono hle1) (hf2.mono hle1) (fun i s' b => (hw i s' b).mono hle1) harr' h1sat hfval1 hww1 hag1
     refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun k hk => (h'lt k (lt_of_lt_of_le hk hle1)).trans (h1lt k hk),
       h'sat, fun sf' hsf' => ?_⟩
     by_cases heq : s = sf'.val
     · have hsfeq : sf' = sf := Fin.ext heq.symm
       subst hsfeq
       rw [bbr_uc n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut sf (by change sf.val < s + 1; omega)]
       dsimp only [arr']
       rw [if_pos rfl]
       have hex_eq : lEv α' br.excl = true := (lecl h'inl h'lt hex1).trans h1ex
       refine ⟨?_, fun h => by rw [hex_eq] at h; cases h⟩
       rw [hex_eq]; symm; rw [decide_eq_true_iff]; push_neg at hsyn; exact hsyn
     · have hr := h'res sf' (by omega)
       simpa only [h1inl] using hr

lemma bbr_up (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (F : Finset (CN (Fin n ⊕ Fin t))) (seed : Set (LN (Fin n ⊕ Fin t)))
   (d0 : ℕ) (x' : Fin n → Bool) (sf : Fin (2 ^ h')) :
   ∀ (m s : ℕ) (_ : 2 ^ h' - s = m) (arr : Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t)),
     s ≤ sf.val →
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ i s' b, VL st.1 (wRow i s' b)) →
     (∀ C ∈ (bbr n t h' D gates out H_row wRow fd s arr st).2.2, C ∈ F) →
     (∀ j : Fin n,
       fLt (Sum.inl (Sum.inl j), true) (x' j) ∈ (upS F)^[d0] seed ∨
         wRow j sf (x' j) ∈ (upS F)^[d0] seed) →
     fd.2 ∈ (upS F)^[1] seed →
     let br := (bbr n t h' D gates out H_row wRow fd s arr st).1 sf
     (∀ i, lod (br.xDual i) (x' i) ∈ (upS F)^[d0 + 1] seed) ∧
     (∀ q : Fin h',
       sf.val.testBit q.val ≠ xl (((List.finRange n).filter (fun i => H_row q i)).map x') →
       br.excl ∈ (upS F)^[d0 + 1 + Nat.clog 2 (n + 1) + 1] seed) ∧
     (∀ u < n + gates.length, dv n gates u ≤ D →
       lod (br.wiresOut u) (wv n x' gates u) ∈ (upS F)^[d0 + 1 + dv n gates u] seed) ∧
     (∀ j : Fin t, dv n gates (out j) ≤ D →
       lod (br.wiresOut (out j)) (wv n x' gates (out j)) ∈ (upS F)^[d0 + 1 + D] seed) ∧
     (∀ j : Fin t, ∀ sign : Bool,
       dv n gates (out j) ≤ D →
       (Sum.inl (Sum.inr j), sign) ∈ seed →
       wv n x' gates (out j) ≠ sign →
       br.excl ∈ (upS F)^[d0 + 1 + D + 1] seed)
 | 0, s, hm, _, _, hsf, _, _, _, _, _, _, _ => by exfalso; omega
 | m + 1, s, hm, arr, st, hsf, hst, hf1, hf2, hw, hF, hx_in, hf_up => by
   have hs : s < 2 ^ h' := by omega
   have hm1 : 2 ^ h' - (s + 1) = m := by omega
   unfold bbr at hF ⊢
   simp only [hs, ↓reduceDIte] at hF ⊢
   set sf0 : Fin (2 ^ h') := ⟨s, hs⟩
   obtain ⟨hst1, hle1, _, _, _, _, _, _⟩ :=
     bb_pr n t h' D gates out H_row (fun i => wRow i sf0) fd sf0 st hst hf1 hf2 (fun i b => hw i sf0 b)
   set br := bb n t h' D gates out H_row (fun i => wRow i sf0) fd sf0 st
   let arr' : Fin (2 ^ h') → BR n t := fun s' => if s' = sf0 then br else arr s'
   by_cases heq : s = sf.val
   · have hsfeq : sf = sf0 := Fin.ext heq.symm
     rw [hsfeq] at hx_in ⊢
     rw [bbr_uc n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut sf0 (by change sf0.val < s + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hFbr : ∀ C ∈ br.stOut.2, C ∈ F := fun C hC =>
       hF C (bbr_cm n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut C hC)
     exact bb_up n t h' D gates out H_row (fun i => wRow i sf0) fd sf0 st F seed d0 x'
       hst hf1 hf2 (fun i b => hw i sf0 b) hFbr hx_in hf_up
   · exact bbr_up n t h' D gates out H_row wRow fd F seed d0 x' sf m (s + 1) hm1
       arr' br.stOut (by omega) hst1 (hf1.mono hle1) (hf2.mono hle1) (fun i s' b => (hw i s' b).mono hle1)
       hF hx_in hf_up

def bab (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ℕ → (Fin R → Fin (2 ^ h') → BR n t) → St (Fin n ⊕ Fin t) →
     (Fin R → Fin (2 ^ h') → BR n t) × St (Fin n ⊕ Fin t)
 | r, arr, st =>
   if hr : r < R then
     let rf : Fin R := ⟨r, hr⟩
     let dummyRow : Fin (2 ^ h') → BR n t := fun _ => ⟨fd.1, fun _ => fd, fun _ => fd, st⟩
     let rowRes := bbr n t h' D gates out (H rf) (wMat rf) fd 0 dummyRow st
     let arr' : Fin R → Fin (2 ^ h') → BR n t := fun r' => if r' = rf then rowRes.1 else arr r'
     bab n t h' R D gates out H wMat fd (r + 1) arr' rowRes.2
   else (arr, st)
termination_by r => R - r

lemma bab_cm (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ∀ (m r : ℕ) (_ : R - r = m) (arr : Fin R → Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (C : CN (Fin n ⊕ Fin t)),
     C ∈ st.2 → C ∈ (bab n t h' R D gates out H wMat fd r arr st).2.2
 | 0, r, hm, arr, st, C, hC => by
   have hge : ¬ (r < R) := by omega
   unfold bab; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, r, hm, arr, st, C, hC => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bab; simp only [hr, ↓reduceDIte]
   apply bab_cm n t h' R D gates out H wMat fd m (r + 1) hm1 _ _ C
   apply bbr_cm n t h' D gates out _ _ fd (2 ^ h') 0 (Nat.sub_zero _) _ st C hC

lemma bab_uc (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ∀ (m r : ℕ) (_ : R - r = m) (arr : Fin R → Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (rf : Fin R), rf.val < r →
     (bab n t h' R D gates out H wMat fd r arr st).1 rf = arr rf
 | 0, r, hm, arr, st, rf, _ => by
   have hge : ¬ (r < R) := by omega
   unfold bab; simp only [hge, ↓reduceDIte]
 | m + 1, r, hm, arr, st, rf, hrf => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bab; simp only [hr, ↓reduceDIte]
   have hne : rf ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [bab_uc n t h' R D gates out H wMat fd m (r + 1) hm1 _ _ rf (by omega)]
   simp [hne]

lemma bab_pr (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t)) :
   ∀ (m r : ℕ) (_ : R - r = m) (arr : Fin R → Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t)),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ rf i s' b, VL st.1 (wMat rf i s' b)) →
     (∀ rf : Fin R, rf.val < r → ∀ sf : Fin (2 ^ h'),
       VL st.1 (arr rf sf).excl ∧
       (∀ i, VL st.1 ((arr rf sf).xDual i).1 ∧ VL st.1 ((arr rf sf).xDual i).2) ∧
       (∀ u, VL st.1 ((arr rf sf).wiresOut u).1 ∧ VL st.1 ((arr rf sf).wiresOut u).2)) →
     let res := bab n t h' R D gates out H wMat fd r arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * m ∧
     res.2.2.length ≤ st.2.length + ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * m ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ rf : Fin R, ∀ sf : Fin (2 ^ h'),
       VL res.2.1 (res.1 rf sf).excl ∧
       (∀ i, VL res.2.1 ((res.1 rf sf).xDual i).1 ∧ VL res.2.1 ((res.1 rf sf).xDual i).2) ∧
       (∀ u, VL res.2.1 ((res.1 rf sf).wiresOut u).1 ∧ VL res.2.1 ((res.1 rf sf).wiresOut u).2))
 | 0, r, hm, arr, st, hst, _, _, _, harr => by
   have hge : ¬ (r < R) := by omega
   unfold bab; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun rf => harr rf (by omega)⟩
 | m + 1, r, hm, arr, st, hst, hf1, hf2, hw, harr => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bab; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   let dummyRow : Fin (2 ^ h') → BR n t := fun _ => ⟨fd.1, fun _ => fd, fun _ => fd, st⟩
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hrow1⟩ :=
     bbr_pr n t h' D gates out (H rf) (wMat rf) fd (2 ^ h') 0 (Nat.sub_zero _)
       dummyRow st hst hf1 hf2 (fun i s' b => hw rf i s' b) (fun sf hsf => by exfalso; omega)
   set rowRes := bbr n t h' D gates out (H rf) (wMat rf) fd 0 dummyRow st
   let arr' : Fin R → Fin (2 ^ h') → BR n t := fun r' => if r' = rf then rowRes.1 else arr r'
   have harr' : ∀ rf' : Fin R, rf'.val < r + 1 → ∀ sf : Fin (2 ^ h'),
       VL rowRes.2.1 (arr' rf' sf).excl ∧
       (∀ i, VL rowRes.2.1 ((arr' rf' sf).xDual i).1 ∧ VL rowRes.2.1 ((arr' rf' sf).xDual i).2) ∧
       (∀ u, VL rowRes.2.1 ((arr' rf' sf).wiresOut u).1 ∧ VL rowRes.2.1 ((arr' rf' sf).wiresOut u).2) := by
     intro rf' hrf' sf
     dsimp only [arr']
     split_ifs with heq
     · exact hrow1 sf
     · have hlt : rf'.val < r := by have hne : rf'.val ≠ r := fun h => heq (Fin.ext h); omega
       exact ⟨(harr rf' hlt sf).1.mono hle1,
             fun i => ⟨((harr rf' hlt sf).2.1 i).1.mono hle1, ((harr rf' hlt sf).2.1 i).2.mono hle1⟩,
             fun u => ⟨((harr rf' hlt sf).2.2 u).1.mono hle1, ((harr rf' hlt sf).2.2 u).2.mono hle1⟩⟩
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     bab_pr n t h' R D gates out H wMat fd m (r + 1) hm1 arr' rowRes.2
       hst1 (hf1.mono hle1) (hf2.mono hle1) (fun rf' i s' b => (hw rf' i s' b).mono hle1) harr'
   refine ⟨r1, le_trans hle1 r2, ?_, ?_, fun C hC => r5 C (hsub1 C hC), r6⟩
   · calc (bab n t h' R D gates out H wMat fd (r + 1) arr' rowRes.2).2.1
       _ ≤ rowRes.2.1 + ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * m := r3
       _ ≤ (st.1 + (1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') +
           ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * m := Nat.add_le_add_right hm1_v _
       _ = st.1 + ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * (m + 1) := by ring
   · calc (bab n t h' R D gates out H wMat fd (r + 1) arr' rowRes.2).2.2.length
       _ ≤ rowRes.2.2.length + ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * m := r4
       _ ≤ (st.2.length + (5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') +
           ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * m := Nat.add_le_add_right hl1_c _
       _ = st.2.length + ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * (m + 1) := by ring

lemma bab_sat (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D) :
   ∀ (m r : ℕ) (_ : R - r = m) (arr : Fin R → Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (α : Sum (Fin n ⊕ Fin t) ℕ → Bool),
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ rf i s' b, VL st.1 (wMat rf i s' b)) →
     (∀ rf : Fin R, rf.val < r → ∀ sf : Fin (2 ^ h'),
       VL st.1 (arr rf sf).excl ∧
       (∀ i, VL st.1 ((arr rf sf).xDual i).1 ∧ VL st.1 ((arr rf sf).xDual i).2) ∧
       (∀ u, VL st.1 ((arr rf sf).wiresOut u).1 ∧ VL st.1 ((arr rf sf).wiresOut u).2)) →
     (∀ C ∈ st.2, ClauseSat α C) →
     (lEv α fd.1 = false ∧ lEv α fd.2 = true) →
     (∀ rf : Fin R, ∀ sf : Fin (2 ^ h'), (∀ q : Fin h', sf.val.testBit q.val =
       xl (((List.finRange n).filter (fun i => H rf q i)).map (fun i => α (Sum.inl (Sum.inl i))))) →
       ∀ i b, lEv α (wMat rf i sf b) = true → α (Sum.inl (Sum.inl i)) = b) →
     (∀ j : Fin t, α (Sum.inl (Sum.inr j)) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => α (Sum.inl (Sum.inl i))))).getD (out j) false) →
     ∃ α' : Sum (Fin n ⊕ Fin t) ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ k < st.1, α' (Sum.inr k) = α (Sum.inr k)) ∧
       (∀ C ∈ (bab n t h' R D gates out H wMat fd r arr st).2.2, ClauseSat α' C) ∧
       ∀ rf : Fin R, r ≤ rf.val → ∀ sf : Fin (2 ^ h'),
         let br := (bab n t h' R D gates out H wMat fd r arr st).1 rf sf
         (lEv α' br.excl = decide (∃ q : Fin h', sf.val.testBit q.val ≠
           xl (((List.finRange n).filter (fun i => H rf q i)).map (fun i => α (Sum.inl (Sum.inl i)))))) ∧
         (lEv α' br.excl = false →
           (∀ i, lEv α' (br.xDual i).1 = α (Sum.inl (Sum.inl i)) ∧
                 lEv α' (br.xDual i).2 = !(α (Sum.inl (Sum.inl i)))) ∧
           (∀ j : Fin t, lEv α' (br.wiresOut (out j)).1 = α (Sum.inl (Sum.inr j)) ∧
                         lEv α' (br.wiresOut (out j)).2 = !(α (Sum.inl (Sum.inr j)))))
 | 0, r, hm, arr, st, α, _, _, _, _, _, hsat, _, _, _ => by
   have hge : ¬ (r < R) := by omega
   unfold bab; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun rf hrf => by exfalso; omega⟩
 | m + 1, r, hm, arr, st, α, hst, hf1, hf2, hw, harr, hsat, hfval, hww, hag => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bab; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   let dummyRow : Fin (2 ^ h') → BR n t := fun _ => ⟨fd.1, fun _ => fd, fun _ => fd, st⟩
   obtain ⟨hst1, hle1, _, _, _, hrow1⟩ :=
     bbr_pr n t h' D gates out (H rf) (wMat rf) fd (2 ^ h') 0 (Nat.sub_zero _)
       dummyRow st hst hf1 hf2 (fun i s' b => hw rf i s' b) (fun sf hsf => by exfalso; omega)
   obtain ⟨α1, h1inl, h1lt, h1sat, h1row⟩ :=
     bbr_sat n t h' D gates out (H rf) (wMat rf) fd hD_bound (2 ^ h') 0 (Nat.sub_zero _)
       dummyRow st α hst hf1 hf2 (fun i s' b => hw rf i s' b) (fun sf hsf => by exfalso; omega)
       hsat hfval (hww rf) hag
   set rowRes := bbr n t h' D gates out (H rf) (wMat rf) fd 0 dummyRow st
   let arr' : Fin R → Fin (2 ^ h') → BR n t := fun r' => if r' = rf then rowRes.1 else arr r'
   have harr' : ∀ rf' : Fin R, rf'.val < r + 1 → ∀ sf : Fin (2 ^ h'),
       VL rowRes.2.1 (arr' rf' sf).excl ∧
       (∀ i, VL rowRes.2.1 ((arr' rf' sf).xDual i).1 ∧ VL rowRes.2.1 ((arr' rf' sf).xDual i).2) ∧
       (∀ u, VL rowRes.2.1 ((arr' rf' sf).wiresOut u).1 ∧ VL rowRes.2.1 ((arr' rf' sf).wiresOut u).2) := by
     intro rf' hrf' sf
     dsimp only [arr']
     split_ifs with heq
     · exact hrow1 sf
     · have hlt : rf'.val < r := by have hne : rf'.val ≠ r := fun h => heq (Fin.ext h); omega
       exact ⟨(harr rf' hlt sf).1.mono hle1,
             fun i => ⟨((harr rf' hlt sf).2.1 i).1.mono hle1, ((harr rf' hlt sf).2.1 i).2.mono hle1⟩,
             fun u => ⟨((harr rf' hlt sf).2.2 u).1.mono hle1, ((harr rf' hlt sf).2.2 u).2.mono hle1⟩⟩
   have hfval1 : lEv α1 fd.1 = false ∧ lEv α1 fd.2 = true :=
     ⟨(lecl h1inl h1lt hf1).trans hfval.1, (lecl h1inl h1lt hf2).trans hfval.2⟩
   have hww1 : ∀ rf' : Fin R, ∀ sf : Fin (2 ^ h'), (∀ q : Fin h', sf.val.testBit q.val =
       xl (((List.finRange n).filter (fun i => H rf' q i)).map (fun i => α1 (Sum.inl (Sum.inl i))))) →
       ∀ i b, lEv α1 (wMat rf' i sf b) = true → α1 (Sum.inl (Sum.inl i)) = b := by
     intro rf' sf hsyn' i b hwb
     rw [h1inl]
     apply hww rf' sf (fun q => by rw [hsyn' q]; congr 1; exact List.map_congr_left fun j _ => h1inl _) i b
     rw [← lecl h1inl h1lt (hw rf' i sf b)]
     exact hwb
   have hag1 : ∀ j : Fin t, α1 (Sum.inl (Sum.inr j)) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => α1 (Sum.inl (Sum.inl i))))).getD (out j) false := by
     intro j; rw [h1inl, hag j]; congr 2; exact congrArg List.ofFn (funext fun i => (h1inl _).symm)
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     bab_sat n t h' R D gates out H wMat fd hD_bound m (r + 1) hm1 arr' rowRes.2 α1
       hst1 (hf1.mono hle1) (hf2.mono hle1) (fun rf' i s' b => (hw rf' i s' b).mono hle1) harr'
       h1sat hfval1 hww1 hag1
   refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun k hk => (h'lt k (lt_of_lt_of_le hk hle1)).trans (h1lt k hk),
     h'sat, fun rf' hrf' sf => ?_⟩
   by_cases heq : r = rf'.val
   · have hrfeq : rf' = rf := Fin.ext heq.symm
     subst hrfeq
     rw [bab_uc n t h' R D gates out H wMat fd m (r + 1) hm1 arr' rowRes.2 rf (by change rf.val < r + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hr0 := h1row sf (Nat.zero_le _)
     have hex_eq : lEv α' (rowRes.1 sf).excl = lEv α1 (rowRes.1 sf).excl :=
       lecl h'inl h'lt (hrow1 sf).1
     refine ⟨?_, fun h => ?_⟩
     · rw [hex_eq, hr0.1]
     · rw [hex_eq] at h
       obtain ⟨hx_eq, hw_eq⟩ := hr0.2 h
       refine ⟨fun i => ?_, fun j => ?_⟩
       · rw [lecl h'inl h'lt ((hrow1 sf).2.1 i).1, lecl h'inl h'lt ((hrow1 sf).2.1 i).2]
         exact hx_eq i
       · rw [lecl h'inl h'lt ((hrow1 sf).2.2 (out j)).1, lecl h'inl h'lt ((hrow1 sf).2.2 (out j)).2]
         exact hw_eq j
   · have hr := h'res rf' (by omega) sf
     simpa only [h1inl] using hr

lemma bab_up (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (F : Finset (CN (Fin n ⊕ Fin t))) (seed : Set (LN (Fin n ⊕ Fin t)))
   (d0 : ℕ) (x' : Fin n → Bool) (rf : Fin R) (sf : Fin (2 ^ h')) :
   ∀ (m r : ℕ) (_ : R - r = m) (arr : Fin R → Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t)),
     r ≤ rf.val →
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ rf' i s' b, VL st.1 (wMat rf' i s' b)) →
     (∀ C ∈ (bab n t h' R D gates out H wMat fd r arr st).2.2, C ∈ F) →
     (∀ j : Fin n,
       fLt (Sum.inl (Sum.inl j), true) (x' j) ∈ (upS F)^[d0] seed ∨
         wMat rf j sf (x' j) ∈ (upS F)^[d0] seed) →
     fd.2 ∈ (upS F)^[1] seed →
     let br := (bab n t h' R D gates out H wMat fd r arr st).1 rf sf
     (∀ i, lod (br.xDual i) (x' i) ∈ (upS F)^[d0 + 1] seed) ∧
     (∀ q : Fin h',
       sf.val.testBit q.val ≠ xl (((List.finRange n).filter (fun i => H rf q i)).map x') →
       br.excl ∈ (upS F)^[d0 + 1 + Nat.clog 2 (n + 1) + 1] seed) ∧
     (∀ u < n + gates.length, dv n gates u ≤ D →
       lod (br.wiresOut u) (wv n x' gates u) ∈ (upS F)^[d0 + 1 + dv n gates u] seed) ∧
     (∀ j : Fin t, dv n gates (out j) ≤ D →
       lod (br.wiresOut (out j)) (wv n x' gates (out j)) ∈ (upS F)^[d0 + 1 + D] seed) ∧
     (∀ j : Fin t, ∀ sign : Bool,
       dv n gates (out j) ≤ D →
       (Sum.inl (Sum.inr j), sign) ∈ seed →
       wv n x' gates (out j) ≠ sign →
       br.excl ∈ (upS F)^[d0 + 1 + D + 1] seed)
 | 0, r, hm, _, _, hrf, _, _, _, _, _, _, _ => by exfalso; omega
 | m + 1, r, hm, arr, st, hrf, hst, hf1, hf2, hw, hF, hx_in, hf_up => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bab at hF ⊢
   simp only [hr, ↓reduceDIte] at hF ⊢
   set rf0 : Fin R := ⟨r, hr⟩
   let dummyRow : Fin (2 ^ h') → BR n t := fun _ => ⟨fd.1, fun _ => fd, fun _ => fd, st⟩
   obtain ⟨hst1, hle1, _, _, _, _⟩ :=
     bbr_pr n t h' D gates out (H rf0) (wMat rf0) fd (2 ^ h') 0 (Nat.sub_zero _)
       dummyRow st hst hf1 hf2 (fun i s' b => hw rf0 i s' b) (fun sf' hsf' => by exfalso; omega)
   set rowRes := bbr n t h' D gates out (H rf0) (wMat rf0) fd 0 dummyRow st
   let arr' : Fin R → Fin (2 ^ h') → BR n t := fun r' => if r' = rf0 then rowRes.1 else arr r'
   by_cases heq : r = rf.val
   · have hrfeq : rf = rf0 := Fin.ext heq.symm
     rw [hrfeq] at hx_in ⊢
     rw [bab_uc n t h' R D gates out H wMat fd m (r + 1) hm1 arr' rowRes.2 rf0 (by change rf0.val < r + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hFrow : ∀ C ∈ rowRes.2.2, C ∈ F := fun C hC =>
       hF C (bab_cm n t h' R D gates out H wMat fd m (r + 1) hm1 arr' rowRes.2 C hC)
     exact bbr_up n t h' D gates out (H rf0) (wMat rf0) fd F seed d0 x' sf
       (2 ^ h') 0 (Nat.sub_zero _) dummyRow st (Nat.zero_le _) hst hf1 hf2 (fun i s' b => hw rf0 i s' b)
       hFrow hx_in hf_up
   · exact bab_up n t h' R D gates out H wMat fd F seed d0 x' rf sf
       m (r + 1) hm1 arr' rowRes.2 (by omega) hst1 (hf1.mono hle1) (hf2.mono hle1)
       (fun rf' i s' b => (hw rf' i s' b).mono hle1) hF hx_in hf_up

lemma list_finRange_ne_nil (k : ℕ) (hk : 1 ≤ k) : List.finRange k ≠ [] := by
 intro h
 have := congrArg List.length h
 simp at this
 omega

def brat {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) :
   ℕ → (Fin R → LN V) → St V → (Fin R → LN V) × St V
 | r, arr, st =>
   if hr : r < R then
     let rf : Fin R := ⟨r, hr⟩
     let T_r := BTree.ofList ((List.finRange m).map (lits rf)) (by simp [list_finRange_ne_nil m hm])
     let res := bat T_r st
     let arr' : Fin R → LN V := fun r' => if r' = rf then res.1 else arr r'
     brat R m hm lits (r + 1) arr' res.2
   else (arr, st)
termination_by r => R - r

lemma brat_cm {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → LN V) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (brat R m hm lits r arr st).2.2
 | 0, r, hk, arr, st, C, hC => by
   have hge : ¬ (r < R) := by omega
   unfold brat; simp only [hge, ↓reduceDIte]; exact hC
 | k + 1, r, hk, arr, st, C, hC => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = k := by omega
   unfold brat; simp only [hr, ↓reduceDIte]
   apply brat_cm R m hm lits k (r + 1) hm1 _ _ C
   exact bat_cm _ st C hC

lemma brat_uc {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → LN V) (st : St V) (rf : Fin R),
     rf.val < r → (brat R m hm lits r arr st).1 rf = arr rf
 | 0, r, hk, arr, st, rf, _ => by
   have hge : ¬ (r < R) := by omega
   unfold brat; simp only [hge, ↓reduceDIte]
 | k + 1, r, hk, arr, st, rf, hrf => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = k := by omega
   unfold brat; simp only [hr, ↓reduceDIte]
   have hne : rf ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [brat_uc R m hm lits k (r + 1) hm1 _ _ rf (by omega)]
   simp [hne]

lemma brat_pr {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → LN V) (st : St V),
     VS st →
     (∀ rf s, VL st.1 (lits rf s)) →
     (∀ rf : Fin R, rf.val < r → VL st.1 (arr rf)) →
     let res := brat R m hm lits r arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + (2 * m) * k ∧
     res.2.2.length ≤ st.2.length + (6 * m) * k ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ rf, VL res.2.1 (res.1 rf))
 | 0, r, hk, arr, st, hst, _, harr => by
   have hge : ¬ (r < R) := by omega
   unfold brat; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun rf => harr rf (by omega)⟩
 | k + 1, r, hk, arr, st, hst, hlits, harr => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = k := by omega
   unfold brat; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   set T_r := BTree.ofList ((List.finRange m).map (lits rf)) (by simp [list_finRange_ne_nil m hm])
   have hTl : T_r.leaves = (List.finRange m).map (lits rf) := BTree.leaves_ofList _ _
   have hTa : ∀ a ∈ T_r.leaves, VL st.1 a := by
     intro a ha; rw [hTl] at ha; rcases List.mem_map.1 ha with ⟨s, _, rfl⟩; exact hlits rf s
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hv1⟩ := bat_pr T_r st hst hTa
   set res := bat T_r st
   have hnodes : T_r.nodes ≤ 2 * m := by
     have hnb := BTree.nodes_ofList ((List.finRange m).map (lits rf)) (by simp [list_finRange_ne_nil m hm])
     change T_r.nodes + 1 ≤ 2 * ((List.finRange m).map (lits rf)).length at hnb
     rw [List.length_map, List.length_finRange] at hnb
     omega
   let arr' : Fin R → LN V := fun r' => if r' = rf then res.1 else arr r'
   have harr' : ∀ rf' : Fin R, rf'.val < r + 1 → VL res.2.1 (arr' rf') := by
     intro rf' hrf'
     dsimp only [arr']
     split_ifs with heq
     · exact hv1
     · have hlt : rf'.val < r := by have hne : rf'.val ≠ r := fun h => heq (Fin.ext h); omega
       exact (harr rf' hlt).mono hle1
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     brat_pr R m hm lits k (r + 1) hm1 arr' res.2 hst1
       (fun rf' s => (hlits rf' s).mono hle1) harr'
   refine ⟨r1, le_trans hle1 r2, ?_, ?_, fun C hC => r5 C (hsub1 C hC), r6⟩
   · have ha : res.2.1 ≤ st.1 + 2 * m := by omega
     calc (brat R m hm lits (r + 1) arr' res.2).2.1
       _ ≤ res.2.1 + (2 * m) * k := r3
       _ ≤ (st.1 + 2 * m) + (2 * m) * k := Nat.add_le_add_right ha _
       _ = st.1 + (2 * m) * (k + 1) := by ring
   · have hb : res.2.2.length ≤ st.2.length + 6 * m := by omega
     calc (brat R m hm lits (r + 1) arr' res.2).2.2.length
       _ ≤ res.2.2.length + (6 * m) * k := r4
       _ ≤ (st.2.length + 6 * m) + (6 * m) * k := Nat.add_le_add_right hb _
       _ = st.2.length + (6 * m) * (k + 1) := by ring

lemma brat_sa {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → LN V) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ rf s, VL st.1 (lits rf s)) →
     (∀ rf : Fin R, rf.val < r → VL st.1 (arr rf)) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (brat R m hm lits r arr st).2.2, ClauseSat α' C) ∧
       ∀ rf : Fin R, r ≤ rf.val →
         lEv α' ((brat R m hm lits r arr st).1 rf) =
           (List.finRange m).all (fun s => lEv α (lits rf s))
 | 0, r, hk, arr, st, α, _, _, _, hsat => by
   have hge : ¬ (r < R) := by omega
   unfold brat; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun rf hrf => by exfalso; omega⟩
 | k + 1, r, hk, arr, st, α, hst, hlits, harr, hsat => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = k := by omega
   unfold brat; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   set T_r := BTree.ofList ((List.finRange m).map (lits rf)) (by simp [list_finRange_ne_nil m hm])
   have hTl : T_r.leaves = (List.finRange m).map (lits rf) := BTree.leaves_ofList _ _
   have hTa : ∀ a ∈ T_r.leaves, VL st.1 a := by
     intro a ha; rw [hTl] at ha; rcases List.mem_map.1 ha with ⟨s, _, rfl⟩; exact hlits rf s
   obtain ⟨hst1, hle1, _, _, _, hv1⟩ := bat_pr T_r st hst hTa
   obtain ⟨α1, h1inl, h1lt, h1sat, h1val⟩ := bat_sa T_r st α hst hTa hsat
   set res := bat T_r st
   let arr' : Fin R → LN V := fun r' => if r' = rf then res.1 else arr r'
   have harr' : ∀ rf' : Fin R, rf'.val < r + 1 → VL res.2.1 (arr' rf') := by
     intro rf' hrf'
     dsimp only [arr']
     split_ifs with heq
     · exact hv1
     · have hlt : rf'.val < r := by have hne : rf'.val ≠ r := fun h => heq (Fin.ext h); omega
       exact (harr rf' hlt).mono hle1
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     brat_sa R m hm lits k (r + 1) hm1 arr' res.2 α1
       hst1 (fun rf' s => (hlits rf' s).mono hle1) harr' h1sat
   refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun w hw => (h'lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw),
     h'sat, fun rf' hrf' => ?_⟩
   by_cases heq : r = rf'.val
   · have hrfeq : rf' = rf := Fin.ext heq.symm
     subst hrfeq
     rw [brat_uc R m hm lits k (r + 1) hm1 arr' res.2 rf (by change rf.val < r + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl, lecl h'inl h'lt hv1, h1val, hTl, List.all_map]
     rfl
   · rw [h'res rf' (by omega)]
     congr 1
     ext s
     exact lecl h1inl h1lt (hlits rf' s)

lemma brat_up {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (F : Finset (CN V)) (seed : Set (LN V))
   (lits : Fin R → Fin m → LN V) (d0 : ℕ) (rf : Fin R) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → LN V) (st : St V),
     r ≤ rf.val →
     (∀ C ∈ (brat R m hm lits r arr st).2.2, C ∈ F) →
     (∀ s : Fin m, lits rf s ∈ (upS F)^[d0] seed) →
     (brat R m hm lits r arr st).1 rf ∈ (upS F)^[d0 + Nat.clog 2 m] seed
 | 0, r, hk, _, _, hrf, _, _ => by exfalso; omega
 | k + 1, r, hk, arr, st, hrf, hF, hs_mem => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = k := by omega
   unfold brat at hF ⊢
   simp only [hr, ↓reduceDIte] at hF ⊢
   set rf0 : Fin R := ⟨r, hr⟩
   set T_r := BTree.ofList ((List.finRange m).map (lits rf0)) (by simp [list_finRange_ne_nil m hm])
   set res := bat T_r st
   let arr' : Fin R → LN V := fun r' => if r' = rf0 then res.1 else arr r'
   by_cases heq : r = rf.val
   · have hrfeq : rf = rf0 := Fin.ext heq.symm
     rw [hrfeq] at hs_mem ⊢
     rw [brat_uc R m hm lits k (r + 1) hm1 arr' res.2 rf0 (by change rf0.val < r + 1; omega)]
     dsimp only [arr']
     rw [if_pos rfl]
     have hFr : ∀ C ∈ res.2.2, C ∈ F := fun C hC =>
       hF C (brat_cm R m hm lits k (r + 1) hm1 arr' res.2 C hC)
     have hTl : T_r.leaves = (List.finRange m).map (lits rf0) := BTree.leaves_ofList _ _
     have hdep : T_r.depth ≤ Nat.clog 2 m := by
       have h1 := BTree.depth_ofList ((List.finRange m).map (lits rf0)) (by simp [list_finRange_ne_nil m hm])
       change T_r.depth ≤ Nat.clog 2 (((List.finRange m).map (lits rf0)).length) at h1
       rw [List.length_map, List.length_finRange] at h1
       exact h1
     have hup := bat_up F seed T_r st d0 hFr (fun a ha => by
       rw [hTl] at ha; rcases List.mem_map.1 ha with ⟨s, _, rfl⟩; exact hs_mem s)
     exact upStep_iter_le F seed (Nat.add_le_add_left hdep d0) hup
   · exact brat_up R m hm F seed lits d0 rf k (r + 1) hm1 arr' res.2 (by omega) hF hs_mem

def baog {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) (st : St V) : LN V × St V :=
 let dummy : Fin R → LN V := fun _ => lits ⟨0, hR⟩ ⟨0, hm⟩
 let rowRes := brat R m hm lits 0 dummy st
 let T_or := BTree.ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
 bot T_or rowRes.2

lemma baog_cm {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) (st : St V) (C : CN V) :
   C ∈ st.2 → C ∈ (baog R m hR hm lits st).2.2 := by
 intro hC
 dsimp only [baog]
 apply bot_cm
 exact brat_cm R m hm lits R 0 (Nat.sub_zero _) _ st C hC

lemma baog_pr {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) (st : St V)
   (hst : VS st) (hlits : ∀ r s, VL st.1 (lits r s)) :
   let res := baog R m hR hm lits st
   VS res.2 ∧
   st.1 ≤ res.2.1 ∧
   res.2.1 ≤ st.1 + 2 * R * m + 2 * R ∧
   res.2.2.length ≤ st.2.length + 6 * R * m + 6 * R ∧
   (∀ C ∈ st.2, C ∈ res.2.2) ∧
   VL res.2.1 res.1 := by
 dsimp only [baog]
 set dummy : Fin R → LN V := fun _ => lits ⟨0, hR⟩ ⟨0, hm⟩
 obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hrow1⟩ :=
   brat_pr R m hm lits R 0 (Nat.sub_zero _) dummy st hst hlits (fun rf h => by exfalso; omega)
 set rowRes := brat R m hm lits 0 dummy st
 set T_or := BTree.ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
 have hTl : T_or.leaves = (List.finRange R).map rowRes.1 := BTree.leaves_ofList _ _
 have hTa : ∀ a ∈ T_or.leaves, VL rowRes.2.1 a := by
   intro a ha; rw [hTl] at ha; rcases List.mem_map.1 ha with ⟨rf, _, rfl⟩; exact hrow1 rf
 obtain ⟨hst2, hle2, hm2_v, hl2_c, hsub2, hv2⟩ := bot_pr T_or rowRes.2 hst1 hTa
 have hnodes : T_or.nodes ≤ 2 * R := by
   have hnb := BTree.nodes_ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
   change T_or.nodes + 1 ≤ 2 * ((List.finRange R).map rowRes.1).length at hnb
   rw [List.length_map, List.length_finRange] at hnb
   omega
 refine ⟨hst2, le_trans hle1 hle2, ?_, ?_, fun C hC => hsub2 C (hsub1 C hC), hv2⟩
 · have ha : rowRes.2.1 ≤ st.1 + 2 * R * m := by
     calc rowRes.2.1 ≤ st.1 + (2 * m) * R := hm1_v
       _ = st.1 + 2 * R * m := by ring
   change (bot T_or rowRes.2).2.1 ≤ st.1 + 2 * R * m + 2 * R
   omega
 · have hb : rowRes.2.2.length ≤ st.2.length + 6 * R * m := by
     calc rowRes.2.2.length ≤ st.2.length + (6 * m) * R := hl1_c
       _ = st.2.length + 6 * R * m := by ring
   change (bot T_or rowRes.2).2.2.length ≤ st.2.length + 6 * R * m + 6 * R
   omega

open Classical in
lemma baog_sa {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) (st : St V) (α : Sum V ℕ → Bool)
   (hst : VS st) (hlits : ∀ r s, VL st.1 (lits r s)) (hsat : ∀ C ∈ st.2, ClauseSat α C) :
   ∃ α' : Sum V ℕ → Bool,
     (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
     (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
     (∀ C ∈ (baog R m hR hm lits st).2.2, ClauseSat α' C) ∧
     lEv α' (baog R m hR hm lits st).1 =
       decide (∃ r : Fin R, ∀ s : Fin m, lEv α (lits r s) = true) := by
 dsimp only [baog]
 set dummy : Fin R → LN V := fun _ => lits ⟨0, hR⟩ ⟨0, hm⟩
 obtain ⟨hst1, hle1, _, _, _, hrow1⟩ :=
   brat_pr R m hm lits R 0 (Nat.sub_zero _) dummy st hst hlits (fun rf h => by exfalso; omega)
 obtain ⟨α1, h1inl, h1lt, h1sat, h1row⟩ :=
   brat_sa R m hm lits R 0 (Nat.sub_zero _) dummy st α hst hlits (fun rf h => by exfalso; omega) hsat
 set rowRes := brat R m hm lits 0 dummy st
 set T_or := BTree.ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
 have hTl : T_or.leaves = (List.finRange R).map rowRes.1 := BTree.leaves_ofList _ _
 have hTa : ∀ a ∈ T_or.leaves, VL rowRes.2.1 a := by
   intro a ha; rw [hTl] at ha; rcases List.mem_map.1 ha with ⟨rf, _, rfl⟩; exact hrow1 rf
 obtain ⟨α', h'inl, h'lt, h'sat, h'or⟩ := bot_sa T_or rowRes.2 α1 hst1 hTa h1sat
 refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun w hw => (h'lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw),
   h'sat, ?_⟩
 rw [h'or, hTl, List.any_map, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
 simp only [Function.comp_apply]
 constructor
 · rintro ⟨r, _, hr⟩
   refine ⟨r, fun s => ?_⟩
   have h1 := h1row r (Nat.zero_le _)
   rw [h1, List.all_eq_true] at hr
   exact hr s (List.mem_finRange s)
 · rintro ⟨r, hrs⟩
   refine ⟨r, List.mem_finRange r, ?_⟩
   rw [h1row r (Nat.zero_le _), List.all_eq_true]
   exact fun s _ => hrs s

lemma baog_up {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (F : Finset (CN V)) (seed : Set (LN V))
   (lits : Fin R → Fin m → LN V) (st : St V) (d0 : ℕ)
   (hF : ∀ C ∈ (baog R m hR hm lits st).2.2, C ∈ F)
   (hex : ∃ r : Fin R, ∀ s : Fin m, lits r s ∈ (upS F)^[d0] seed) :
   (baog R m hR hm lits st).1 ∈ (upS F)^[d0 + Nat.clog 2 m + Nat.clog 2 R] seed := by
 dsimp only [baog] at hF ⊢
 set dummy : Fin R → LN V := fun _ => lits ⟨0, hR⟩ ⟨0, hm⟩
 set rowRes := brat R m hm lits 0 dummy st
 set T_or := BTree.ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
 have hFrow : ∀ C ∈ rowRes.2.2, C ∈ F := fun C hC =>
   hF C (bot_cm T_or rowRes.2 C hC)
 obtain ⟨r, hrs⟩ := hex
 have hr_mem : rowRes.1 r ∈ (upS F)^[d0 + Nat.clog 2 m] seed :=
   brat_up R m hm F seed lits d0 r R 0 (Nat.sub_zero _) dummy st (Nat.zero_le _) hFrow hrs
 have hTl : T_or.leaves = (List.finRange R).map rowRes.1 := BTree.leaves_ofList _ _
 have hdep : T_or.depth ≤ Nat.clog 2 R := by
   have h1 := BTree.depth_ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
   change T_or.depth ≤ Nat.clog 2 (((List.finRange R).map rowRes.1).length) at h1
   rw [List.length_map, List.length_finRange] at h1
   exact h1
 have hor := bot_up F seed T_or rowRes.2 (d0 + Nat.clog 2 m) hF
   ⟨rowRes.1 r, by rw [hTl]; exact List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩, hr_mem⟩
 exact upStep_iter_le F seed (by omega) hor

def bor {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) (rf : Fin R) :
   ℕ → (Fin m → LN V) → St V → (Fin m → LN V) × St V
 | s, arr, st =>
   if hs : s < m then
     let sf : Fin m := ⟨s, hs⟩
     let p := fv st
     let ok := p.1
     let st1 := p.2
     let st2 := ec3 (excl rf sf) (vis rf sf) (negL ok) st1
     let st3 := ei2 (vis rf sf) ok st2
     let st4 := ei2 (excl rf sf) ok st3
     let arr' : Fin m → LN V := fun s' => if s' = sf then ok else arr s'
     bor R m excl vis rf (s + 1) arr' st4
   else (arr, st)
termination_by s => m - s

lemma bor_cm {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) (rf : Fin R) :
   ∀ (k s : ℕ) (_ : m - s = k) (arr : Fin m → LN V) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (bor R m excl vis rf s arr st).2.2
 | 0, s, hk, arr, st, C, hC => by
   have hge : ¬ (s < m) := by omega
   unfold bor; simp only [hge, ↓reduceDIte]; exact hC
 | k + 1, s, hk, arr, st, C, hC => by
   have hs : s < m := by omega
   have hk1 : m - (s + 1) = k := by omega
   unfold bor; simp only [hs, ↓reduceDIte]
   apply bor_cm R m excl vis rf k (s + 1) hk1 _ _ C
   simp only [ei2, ec3, addCl, fv, List.mem_cons]
   exact Or.inr (Or.inr (Or.inr hC))

lemma bor_uc {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) (rf : Fin R) :
   ∀ (k s : ℕ) (_ : m - s = k) (arr : Fin m → LN V) (st : St V) (sf : Fin m),
     sf.val < s → (bor R m excl vis rf s arr st).1 sf = arr sf
 | 0, s, hk, arr, st, sf, _ => by
   have hge : ¬ (s < m) := by omega
   unfold bor; simp only [hge, ↓reduceDIte]
 | k + 1, s, hk, arr, st, sf, hsf => by
   have hs : s < m := by omega
   have hk1 : m - (s + 1) = k := by omega
   unfold bor; simp only [hs, ↓reduceDIte]
   have hne : sf ≠ ⟨s, hs⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [bor_uc R m excl vis rf k (s + 1) hk1 _ _ sf (by omega)]
   simp [hne]

lemma bor_pr {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) (rf : Fin R) :
   ∀ (k s : ℕ) (_ : m - s = k) (arr : Fin m → LN V) (st : St V),
     VS st →
     (∀ s' : Fin m, VL st.1 (excl rf s') ∧ VL st.1 (vis rf s')) →
     (∀ s' : Fin m, s'.val < s → VL st.1 (arr s')) →
     let res := bor R m excl vis rf s arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + k ∧
     res.2.2.length ≤ st.2.length + 3 * k ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ s' : Fin m, VL res.2.1 (res.1 s'))
 | 0, s, hk, arr, st, hst, _, harr => by
   have hge : ¬ (s < m) := by omega
   unfold bor; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun s' => harr s' (by omega)⟩
 | k + 1, s, hk, arr, st, hst, hev, harr => by
   have hs : s < m := by omega
   have hk1 : m - (s + 1) = k := by omega
   unfold bor; simp only [hs, ↓reduceDIte]
   set sf : Fin m := ⟨s, hs⟩
   set ok := (fv st).1
   set st1 := (fv st).2
   set st2 := ec3 (excl rf sf) (vis rf sf) (negL ok) st1
   set st3 := ei2 (vis rf sf) ok st2
   set st4 := ei2 (excl rf sf) ok st3
   have hst1 : VS st1 := validSt_fresh hst
   have hok1 : VL st1.1 ok := validLit_fresh st
   have he1 : VL st1.1 (excl rf sf) := (hev sf).1.mono (by simp [st1, fv])
   have hv1 : VL st1.1 (vis rf sf) := (hev sf).2.mono (by simp [st1, fv])
   have hst2 : VS st2 := validSt_emitCl3 hst1 he1 hv1 ((validLit_negL).2 hok1)
   have hst3 : VS st3 := validSt_emitImp2 hst2 hv1 hok1
   have hst4 : VS st4 := validSt_emitImp2 hst3 he1 hok1
   have hst4_1 : st4.1 = st.1 + 1 := rfl
   have hev4 : ∀ s' : Fin m, VL st4.1 (excl rf s') ∧ VL st4.1 (vis rf s') := fun s' =>
     ⟨(hev s').1.mono (by omega), (hev s').2.mono (by omega)⟩
   let arr' : Fin m → LN V := fun s' => if s' = sf then ok else arr s'
   have harr4 : ∀ s' : Fin m, s'.val < s + 1 → VL st4.1 (arr' s') := by
     intro s' hs'
     dsimp only [arr']
     split_ifs with heq
     · exact hok1
     · have hlt : s'.val < s := by
         have hne : s'.val ≠ s := fun h => heq (Fin.ext h)
         omega
       exact (harr s' hlt).mono (by omega)
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     bor_pr R m excl vis rf k (s + 1) hk1 arr' st4 hst4 hev4 harr4
   refine ⟨r1, le_trans (by rw [hst4_1]; omega) r2, ?_, ?_, fun C hC => r5 C ?_, r6⟩
   · calc (bor R m excl vis rf (s + 1) arr' st4).2.1
       _ ≤ st4.1 + k := r3
       _ = st.1 + (k + 1) := by rw [hst4_1]; omega
   · have hl4 : st4.2.length = st.2.length + 3 := by
       simp [st4, st3, st2, st1, ei2, ec3, addCl, fv]
     calc (bor R m excl vis rf (s + 1) arr' st4).2.2.length
       _ ≤ st4.2.length + 3 * k := r4
       _ = st.2.length + 3 * (k + 1) := by rw [hl4]; omega
   · simp only [st4, st3, st2, st1, ei2, ec3, addCl, fv, List.mem_cons]
     exact Or.inr (Or.inr (Or.inr hC))

lemma bor_sat {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) (rf : Fin R) :
   ∀ (k s : ℕ) (_ : m - s = k) (arr : Fin m → LN V) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ s' : Fin m, VL st.1 (excl rf s') ∧ VL st.1 (vis rf s')) →
     (∀ s' : Fin m, s'.val < s → VL st.1 (arr s')) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (bor R m excl vis rf s arr st).2.2, ClauseSat α' C) ∧
       (∀ sf : Fin m, s ≤ sf.val →
         lEv α' ((bor R m excl vis rf s arr st).1 sf) =
           (lEv α (excl rf sf) || lEv α (vis rf sf)))
 | 0, s, hk, arr, st, α, _, _, _, hsat => by
   have hge : ¬ (s < m) := by omega
   unfold bor; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun sf hsf => by exfalso; omega⟩
 | k + 1, s, hk, arr, st, α, hst, hev, harr, hsat => by
   have hs : s < m := by omega
   have hk1 : m - (s + 1) = k := by omega
   unfold bor; simp only [hs, ↓reduceDIte]
   set sf : Fin m := ⟨s, hs⟩
   set ok := (fv st).1
   set st1 := (fv st).2
   set st2 := ec3 (excl rf sf) (vis rf sf) (negL ok) st1
   set st3 := ei2 (vis rf sf) ok st2
   set st4 := ei2 (excl rf sf) ok st3
   let valOk := lEv α (excl rf sf) || lEv α (vis rf sf)
   let α1 : Sum V ℕ → Bool := fun z =>
     match z with
     | Sum.inl v => α (Sum.inl v)
     | Sum.inr w => if w = st.1 then valOk else α (Sum.inr w)
   have hα1_inl : ∀ v, α1 (Sum.inl v) = α (Sum.inl v) := fun _ => rfl
   have hα1_lt : ∀ w < st.1, α1 (Sum.inr w) = α (Sum.inr w) := by
     intro w hw; simp [α1, Nat.ne_of_lt hw]
   have hok_val : lEv α1 ok = valOk := by simp [ok, fv, lEv, α1]
   have he_val : lEv α1 (excl rf sf) = lEv α (excl rf sf) :=
     lecl hα1_inl hα1_lt (hev sf).1
   have hv_val : lEv α1 (vis rf sf) = lEv α (vis rf sf) :=
     lecl hα1_inl hα1_lt (hev sf).2
   have hsat1 : ∀ C ∈ st1.2, ClauseSat α1 C := fun C hC =>
     (cscl hα1_inl hα1_lt (hst C hC).2).2 (hsat C hC)
   have hsat4 : ∀ C ∈ st4.2, ClauseSat α1 C := by
     intro C hC
     simp only [st4, st3, st2, ei2, ec3, addCl, List.mem_cons] at hC
     rcases hC with rfl | rfl | rfl | hC1
     · rw [clauseSat_imp2, he_val, hok_val]; dsimp only [valOk]; cases lEv α (excl rf sf) <;> simp
     · rw [clauseSat_imp2, hv_val, hok_val]; dsimp only [valOk]; cases lEv α (vis rf sf) <;> simp
     · rw [clauseSat_triple, he_val, hv_val, litEval_negL, hok_val]
       dsimp only [valOk]; cases lEv α (excl rf sf) <;> cases lEv α (vis rf sf) <;> simp
     · exact hsat1 C hC1
   have hst1 : VS st1 := validSt_fresh hst
   have hok1 : VL st1.1 ok := validLit_fresh st
   have he1 : VL st1.1 (excl rf sf) := (hev sf).1.mono (by simp [st1, fv])
   have hv1 : VL st1.1 (vis rf sf) := (hev sf).2.mono (by simp [st1, fv])
   have hst4 : VS st4 :=
     validSt_emitImp2 (validSt_emitImp2 (validSt_emitCl3 hst1 he1 hv1 ((validLit_negL).2 hok1)) hv1 hok1) he1 hok1
   have hst4_1 : st4.1 = st.1 + 1 := rfl
   have hev4 : ∀ s' : Fin m, VL st4.1 (excl rf s') ∧ VL st4.1 (vis rf s') := fun s' =>
     ⟨(hev s').1.mono (by omega), (hev s').2.mono (by omega)⟩
   let arr' : Fin m → LN V := fun s' => if s' = sf then ok else arr s'
   have harr4 : ∀ s' : Fin m, s'.val < s + 1 → VL st4.1 (arr' s') := by
     intro s' hs'; dsimp only [arr']; split_ifs with heq
     · exact hok1
     · exact (harr s' (by have hne : s'.val ≠ s := fun h => heq (Fin.ext h); omega)).mono (by omega)
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     bor_sat R m excl vis rf k (s + 1) hk1 arr' st4 α1 hst4 hev4 harr4 hsat4
   refine ⟨α', fun v => (h'inl v).trans (hα1_inl v),
     fun w hw => (h'lt w (by omega)).trans (hα1_lt w hw), h'sat, fun sf' hsf' => ?_⟩
   by_cases heq : s = sf'.val
   · have hsfeq : sf' = sf := Fin.ext heq.symm
     subst hsfeq
     rw [bor_uc R m excl vis rf k (s + 1) hk1 arr' st4 sf (by omega)]
     dsimp only [arr']
     simp only [↓reduceIte]
     rw [lecl h'inl h'lt (by rw [hst4_1]; exact hok1)]
     exact hok_val
   · have hr := h'res sf' (by omega)
     have he_eq : lEv α1 (excl rf sf') = lEv α (excl rf sf') :=
       lecl hα1_inl hα1_lt (hev sf').1
     have hv_eq : lEv α1 (vis rf sf') = lEv α (vis rf sf') :=
       lecl hα1_inl hα1_lt (hev sf').2
     simpa only [he_eq, hv_eq] using hr

lemma bor_up {V : Type} [DecidableEq V] (R m : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (excl vis : Fin R → Fin m → LN V) (rf : Fin R) (d0 : ℕ) (sf : Fin m) :
   ∀ (k s : ℕ) (_ : m - s = k) (arr : Fin m → LN V) (st : St V),
     s ≤ sf.val →
     (∀ C ∈ (bor R m excl vis rf s arr st).2.2, C ∈ F) →
     (excl rf sf ∈ (upS F)^[d0] seed ∨ vis rf sf ∈ (upS F)^[d0] seed) →
     (bor R m excl vis rf s arr st).1 sf ∈ (upS F)^[d0 + 1] seed
 | 0, s, hk, _, _, hsf, _, _ => by exfalso; omega
 | k + 1, s, hk, arr, st, hsf, hF, hor => by
   have hs : s < m := by omega
   have hk1 : m - (s + 1) = k := by omega
   unfold bor at hF ⊢
   simp only [hs, ↓reduceDIte] at hF ⊢
   set sf0 : Fin m := ⟨s, hs⟩
   set ok := (fv st).1
   set st1 := (fv st).2
   set st2 := ec3 (excl rf sf0) (vis rf sf0) (negL ok) st1
   set st3 := ei2 (vis rf sf0) ok st2
   set st4 := ei2 (excl rf sf0) ok st3
   let arr' : Fin m → LN V := fun s' => if s' = sf0 then ok else arr s'
   by_cases heq : s = sf.val
   · have hsfeq : sf = sf0 := Fin.ext heq.symm
     rw [hsfeq] at hor ⊢
     rw [bor_uc R m excl vis rf k (s + 1) hk1 arr' st4 sf0 (by omega)]
     dsimp only [arr']
     simp only [↓reduceIte]
     rw [Function.iterate_succ_apply']
     rcases hor with hex | hvis
     · have hC : ({negL (excl rf sf0), ok} : CN V) ∈ F := by
         apply hF
         apply bor_cm R m excl vis rf k (s + 1) hk1 arr' st4
         simp [st4, ei2, addCl]
       exact upStep_unit2 hC (by simpa [negL_negL] using hex)
     · have hC : ({negL (vis rf sf0), ok} : CN V) ∈ F := by
         apply hF
         apply bor_cm R m excl vis rf k (s + 1) hk1 arr' st4
         simp [st4, st3, ei2, addCl]
       exact upStep_unit2 hC (by simpa [negL_negL] using hvis)
   · exact bor_up R m F seed excl vis rf d0 sf k (s + 1) hk1 arr' st4 (by omega) hF hor

def boa {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) :
   ℕ → (Fin R → Fin m → LN V) → St V → (Fin R → Fin m → LN V) × St V
 | r, arr, st =>
   if hr : r < R then
     let rf : Fin R := ⟨r, hr⟩
     let dummy : Fin m → LN V := fun s => excl rf s
     let resRow := bor R m excl vis rf 0 dummy st
     let arr' : Fin R → Fin m → LN V := fun r' => if r' = rf then resRow.1 else arr r'
     boa R m excl vis (r + 1) arr' resRow.2
   else (arr, st)
termination_by r => R - r

lemma boa_cm {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → Fin m → LN V) (st : St V) (C : CN V),
     C ∈ st.2 → C ∈ (boa R m excl vis r arr st).2.2
 | 0, r, hk, arr, st, C, hC => by
   have hge : ¬ (r < R) := by omega
   unfold boa; simp only [hge, ↓reduceDIte]; exact hC
 | k + 1, r, hk, arr, st, C, hC => by
   have hr : r < R := by omega
   have hk1 : R - (r + 1) = k := by omega
   unfold boa; simp only [hr, ↓reduceDIte]
   apply boa_cm R m excl vis k (r + 1) hk1 _ _ C
   apply bor_cm R m excl vis ⟨r, hr⟩ m 0 (Nat.sub_zero _) _ _ C hC

lemma boa_uc {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → Fin m → LN V) (st : St V) (rf : Fin R),
     rf.val < r → (boa R m excl vis r arr st).1 rf = arr rf
 | 0, r, hk, arr, st, rf, _ => by
   have hge : ¬ (r < R) := by omega
   unfold boa; simp only [hge, ↓reduceDIte]
 | k + 1, r, hk, arr, st, rf, hrf => by
   have hr : r < R := by omega
   have hk1 : R - (r + 1) = k := by omega
   unfold boa; simp only [hr, ↓reduceDIte]
   have hne : rf ≠ ⟨r, hr⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
   rw [boa_uc R m excl vis k (r + 1) hk1 _ _ rf (by omega)]
   simp [hne]

lemma boa_pr {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → Fin m → LN V) (st : St V),
     VS st →
     (∀ r' s', VL st.1 (excl r' s') ∧ VL st.1 (vis r' s')) →
     (∀ r' : Fin R, r'.val < r → ∀ s', VL st.1 (arr r' s')) →
     let res := boa R m excl vis r arr st
     VS res.2 ∧
     st.1 ≤ res.2.1 ∧
     res.2.1 ≤ st.1 + m * k ∧
     res.2.2.length ≤ st.2.length + (3 * m) * k ∧
     (∀ C ∈ st.2, C ∈ res.2.2) ∧
     (∀ r' s', VL res.2.1 (res.1 r' s'))
 | 0, r, hk, arr, st, hst, _, harr => by
   have hge : ¬ (r < R) := by omega
   unfold boa; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h, fun r' => harr r' (by omega)⟩
 | k + 1, r, hk, arr, st, hst, hev, harr => by
   have hr : r < R := by omega
   have hk1 : R - (r + 1) = k := by omega
   unfold boa; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   let dummy : Fin m → LN V := fun s => excl rf s
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hrow1⟩ :=
     bor_pr R m excl vis rf m 0 (Nat.sub_zero _) dummy st hst (hev rf) (fun s' hs' => by exfalso; omega)
   set resRow := bor R m excl vis rf 0 dummy st
   have hev1 : ∀ r' s', VL resRow.2.1 (excl r' s') ∧ VL resRow.2.1 (vis r' s') := fun r' s' =>
     ⟨(hev r' s').1.mono hle1, (hev r' s').2.mono hle1⟩
   let arr' : Fin R → Fin m → LN V := fun r' => if r' = rf then resRow.1 else arr r'
   have harr1 : ∀ r' : Fin R, r'.val < r + 1 → ∀ s', VL resRow.2.1 (arr' r' s') := by
     intro r' hr' s'; dsimp only [arr']; split_ifs with heq
     · exact hrow1 s'
     · exact (harr r' (by have hne : r'.val ≠ r := fun h => heq (Fin.ext h); omega) s').mono hle1
   obtain ⟨r1, r2, r3, r4, r5, r6⟩ :=
     boa_pr R m excl vis k (r + 1) hk1 arr' resRow.2 hst1 hev1 harr1
   refine ⟨r1, le_trans hle1 r2, ?_, ?_, fun C hC => r5 C (hsub1 C hC), r6⟩
   · calc (boa R m excl vis (r + 1) arr' resRow.2).2.1
       _ ≤ resRow.2.1 + m * k := r3
       _ ≤ (st.1 + m) + m * k := Nat.add_le_add_right hm1_v _
       _ = st.1 + m * (k + 1) := by ring
   · calc (boa R m excl vis (r + 1) arr' resRow.2).2.2.length
       _ ≤ resRow.2.2.length + (3 * m) * k := r4
       _ ≤ (st.2.length + 3 * m) + (3 * m) * k := Nat.add_le_add_right hl1_c _
       _ = st.2.length + (3 * m) * (k + 1) := by ring

open Classical in
lemma boa_sat {V : Type} [DecidableEq V] (R m : ℕ)
   (excl vis : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → Fin m → LN V) (st : St V) (α : Sum V ℕ → Bool),
     VS st →
     (∀ r' s', VL st.1 (excl r' s') ∧ VL st.1 (vis r' s')) →
     (∀ r' : Fin R, r'.val < r → ∀ s', VL st.1 (arr r' s')) →
     (∀ C ∈ st.2, ClauseSat α C) →
     ∃ α' : Sum V ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (boa R m excl vis r arr st).2.2, ClauseSat α' C) ∧
       (∀ rf : Fin R, r ≤ rf.val → ∀ sf : Fin m,
         lEv α' ((boa R m excl vis r arr st).1 rf sf) =
           (lEv α (excl rf sf) || lEv α (vis rf sf)))
 | 0, r, hk, arr, st, α, _, _, _, hsat => by
   have hge : ¬ (r < R) := by omega
   unfold boa; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat, fun rf hrf => by exfalso; omega⟩
 | k + 1, r, hk, arr, st, α, hst, hev, harr, hsat => by
   have hr : r < R := by omega
   have hk1 : R - (r + 1) = k := by omega
   unfold boa; simp only [hr, ↓reduceDIte]
   set rf : Fin R := ⟨r, hr⟩
   let dummy : Fin m → LN V := fun s => excl rf s
   obtain ⟨hst1, hle1, _, _, _, hrow1⟩ :=
     bor_pr R m excl vis rf m 0 (Nat.sub_zero _) dummy st hst (hev rf) (fun s' hs' => by exfalso; omega)
   obtain ⟨α1, h1inl, h1lt, h1sat, h1row⟩ :=
     bor_sat R m excl vis rf m 0 (Nat.sub_zero _) dummy st α hst (hev rf) (fun s' hs' => by exfalso; omega) hsat
   set resRow := bor R m excl vis rf 0 dummy st
   have hev1 : ∀ r' s', VL resRow.2.1 (excl r' s') ∧ VL resRow.2.1 (vis r' s') := fun r' s' =>
     ⟨(hev r' s').1.mono hle1, (hev r' s').2.mono hle1⟩
   let arr' : Fin R → Fin m → LN V := fun r' => if r' = rf then resRow.1 else arr r'
   have harr1 : ∀ r' : Fin R, r'.val < r + 1 → ∀ s', VL resRow.2.1 (arr' r' s') := by
     intro r' hr' s'; dsimp only [arr']; split_ifs with heq
     · exact hrow1 s'
     · exact (harr r' (by have hne : r'.val ≠ r := fun h => heq (Fin.ext h); omega) s').mono hle1
   obtain ⟨α', h'inl, h'lt, h'sat, h'res⟩ :=
     boa_sat R m excl vis k (r + 1) hk1 arr' resRow.2 α1 hst1 hev1 harr1 h1sat
   refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun w hw => (h'lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw),
     h'sat, fun rf' hrf' sf => ?_⟩
   by_cases heq : r = rf'.val
   · have hrfeq : rf' = rf := Fin.ext heq.symm
     subst hrfeq
     rw [boa_uc R m excl vis k (r + 1) hk1 arr' resRow.2 rf (by omega)]
     dsimp only [arr']
     simp only [↓reduceIte]
     rw [lecl h'inl h'lt (hrow1 sf)]
     exact h1row sf (Nat.zero_le _)
   · have hrr := h'res rf' (by omega) sf
     have he_eq : lEv α1 (excl rf' sf) = lEv α (excl rf' sf) :=
       lecl h1inl h1lt (hev rf' sf).1
     have hv_eq : lEv α1 (vis rf' sf) = lEv α (vis rf' sf) :=
       lecl h1inl h1lt (hev rf' sf).2
     simpa only [he_eq, hv_eq] using hrr

lemma boa_up {V : Type} [DecidableEq V] (R m : ℕ)
   (F : Finset (CN V)) (seed : Set (LN V))
   (excl vis : Fin R → Fin m → LN V) (d0 : ℕ) (rf : Fin R) (sf : Fin m) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → Fin m → LN V) (st : St V),
     r ≤ rf.val →
     (∀ C ∈ (boa R m excl vis r arr st).2.2, C ∈ F) →
     (excl rf sf ∈ (upS F)^[d0] seed ∨ vis rf sf ∈ (upS F)^[d0] seed) →
     (boa R m excl vis r arr st).1 rf sf ∈ (upS F)^[d0 + 1] seed
 | 0, r, hk, _, _, hrf, _, _ => by exfalso; omega
 | k + 1, r, hk, arr, st, hrf, hF, hor => by
   have hr : r < R := by omega
   have hk1 : R - (r + 1) = k := by omega
   unfold boa at hF ⊢
   simp only [hr, ↓reduceDIte] at hF ⊢
   set rf0 : Fin R := ⟨r, hr⟩
   let dummy : Fin m → LN V := fun s => excl rf0 s
   set resRow := bor R m excl vis rf0 0 dummy st
   let arr' : Fin R → Fin m → LN V := fun r' => if r' = rf0 then resRow.1 else arr r'
   by_cases heq : r = rf.val
   · have hrfeq : rf = rf0 := Fin.ext heq.symm
     rw [hrfeq] at hor ⊢
     rw [boa_uc R m excl vis k (r + 1) hk1 arr' resRow.2 rf0 (by omega)]
     dsimp only [arr']
     simp only [↓reduceIte]
     have hFrow : ∀ C ∈ resRow.2.2, C ∈ F := fun C hC =>
       hF C (boa_cm R m excl vis k (r + 1) hk1 arr' resRow.2 C hC)
     exact bor_up R m F seed excl vis rf0 d0 sf m 0 (Nat.sub_zero _) dummy st (Nat.zero_le _) hFrow hor
   · exact boa_up R m F seed excl vis d0 rf sf k (r + 1) hk1 arr' resRow.2 (by omega) hF hor

def bco {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (excl vis : Fin R → Fin m → LN V) (target : LN V) (st : St V) : St V :=
 let dummy : Fin R → Fin m → LN V := fun _ _ => excl ⟨0, hR⟩ ⟨0, hm⟩
 let okRes := boa R m excl vis 0 dummy st
 let gridRes := baog R m hR hm okRes.1 okRes.2
 ei2 gridRes.1 target gridRes.2

lemma bco_cm {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (excl vis : Fin R → Fin m → LN V) (target : LN V) (st : St V) (C : CN V) :
   C ∈ st.2 → C ∈ (bco R m hR hm excl vis target st).2 := by
 intro hC
 dsimp only [bco]
 simp only [ei2, addCl, List.mem_cons]
 right
 apply baog_cm R m hR hm _ _ C
 exact boa_cm R m excl vis R 0 (Nat.sub_zero _) _ st C hC

lemma bco_pr {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (excl vis : Fin R → Fin m → LN V) (target : LN V) (st : St V)
   (hst : VS st)
   (hev : ∀ r s, VL st.1 (excl r s) ∧ VL st.1 (vis r s))
   (htarg : VL st.1 target) :
   let st' := bco R m hR hm excl vis target st
   VS st' ∧
   st.1 ≤ st'.1 ∧
   st'.1 ≤ st.1 + 3 * R * m + 2 * R ∧
   st'.2.length ≤ st.2.length + 9 * R * m + 6 * R + 1 ∧
   (∀ C ∈ st.2, C ∈ st'.2) := by
 dsimp only [bco]
 let dummy : Fin R → Fin m → LN V := fun _ _ => excl ⟨0, hR⟩ ⟨0, hm⟩
 obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1, hok1⟩ :=
   boa_pr R m excl vis R 0 (Nat.sub_zero _) dummy st hst hev (fun r hr => by exfalso; omega)
 set okRes := boa R m excl vis 0 dummy st
 obtain ⟨hst2, hle2, hm2_v, hl2_c, hsub2, hgrid2⟩ :=
   baog_pr R m hR hm okRes.1 okRes.2 hst1 hok1
 set gridRes := baog R m hR hm okRes.1 okRes.2
 have hst3 : VS (ei2 gridRes.1 target gridRes.2) :=
   validSt_emitImp2 hst2 hgrid2 (htarg.mono (le_trans hle1 hle2))
 refine ⟨hst3, le_trans hle1 hle2, ?_, ?_, fun C hC => by
   simp only [ei2, addCl, List.mem_cons]; exact Or.inr (hsub2 C (hsub1 C hC))⟩
 · have hm1' : okRes.2.1 ≤ st.1 + R * m := by
     calc okRes.2.1 ≤ st.1 + m * R := hm1_v
       _ = st.1 + R * m := by ring
   change (ei2 gridRes.1 target gridRes.2).1 ≤ st.1 + 3 * R * m + 2 * R
   have heq1 : (ei2 gridRes.1 target gridRes.2).1 = gridRes.2.1 := rfl
   rw [heq1]
   calc gridRes.2.1 ≤ okRes.2.1 + 2 * R * m + 2 * R := hm2_v
     _ ≤ (st.1 + R * m) + 2 * R * m + 2 * R := by omega
     _ = st.1 + 3 * R * m + 2 * R := by ring
 · have hl1' : okRes.2.2.length ≤ st.2.length + 3 * R * m := by
     calc okRes.2.2.length ≤ st.2.length + (3 * m) * R := hl1_c
       _ = st.2.length + 3 * R * m := by ring
   change (ei2 gridRes.1 target gridRes.2).2.length ≤ st.2.length + 9 * R * m + 6 * R + 1
   have heq2 : (ei2 gridRes.1 target gridRes.2).2.length = gridRes.2.2.length + 1 := rfl
   rw [heq2]
   calc gridRes.2.2.length + 1 ≤ (okRes.2.2.length + 6 * R * m + 6 * R) + 1 := by omega
     _ ≤ ((st.2.length + 3 * R * m) + 6 * R * m + 6 * R) + 1 := by omega
     _ = st.2.length + 9 * R * m + 6 * R + 1 := by ring

open Classical in
lemma bco_sat {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (excl vis : Fin R → Fin m → LN V) (target : LN V) (st : St V)
   (α : Sum V ℕ → Bool)
   (hst : VS st)
   (hev : ∀ r s, VL st.1 (excl r s) ∧ VL st.1 (vis r s))
   (htarg : VL st.1 target)
   (hsat : ∀ C ∈ st.2, ClauseSat α C)
   (hfalse : lEv α target = false →
     ∀ r : Fin R, ∃ s : Fin m, lEv α (excl r s) = false ∧ lEv α (vis r s) = false) :
   ∃ α' : Sum V ℕ → Bool,
     (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
     (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
     (∀ C ∈ (bco R m hR hm excl vis target st).2, ClauseSat α' C) := by
 dsimp only [bco]
 let dummy : Fin R → Fin m → LN V := fun _ _ => excl ⟨0, hR⟩ ⟨0, hm⟩
 obtain ⟨hst1, hle1, _, _, _, hok1⟩ :=
   boa_pr R m excl vis R 0 (Nat.sub_zero _) dummy st hst hev (fun r hr => by exfalso; omega)
 obtain ⟨α1, h1inl, h1lt, h1sat, h1ok⟩ :=
   boa_sat R m excl vis R 0 (Nat.sub_zero _) dummy st α hst hev (fun r hr => by exfalso; omega) hsat
 set okRes := boa R m excl vis 0 dummy st
 obtain ⟨α', h'inl, h'lt, h'sat, h'grid⟩ :=
   baog_sa R m hR hm okRes.1 okRes.2 α1 hst1 hok1 h1sat
 refine ⟨α', fun v => (h'inl v).trans (h1inl v), fun w hw => (h'lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw), ?_⟩
 intro C hC
 simp only [ei2, addCl, List.mem_cons] at hC
 rcases hC with rfl | hCg
 · rw [clauseSat_imp2]
   intro hgrid
   have ht_eq : lEv α' target = lEv α target :=
     lecl (fun v => (h'inl v).trans (h1inl v))
       (fun w hw => (h'lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw)) htarg
   rw [ht_eq]
   by_cases htf : lEv α target = true
   · exact htf
   · have htf' : lEv α target = false := Bool.eq_false_iff.2 htf
     exfalso
     rw [h'grid, decide_eq_true_iff] at hgrid
     obtain ⟨r, hrs⟩ := hgrid
     obtain ⟨s, hes, hvs⟩ := hfalse htf' r
     have h1 := hrs s
     rw [h1ok r (Nat.zero_le _) s, hes, hvs] at h1
     cases h1
 · exact h'sat C hCg

lemma bco_up {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (F : Finset (CN V)) (seed : Set (LN V))
   (excl vis : Fin R → Fin m → LN V) (target : LN V) (st : St V) (d0 : ℕ)
   (hF : ∀ C ∈ (bco R m hR hm excl vis target st).2, C ∈ F)
   (hex : ∃ r : Fin R, ∀ s : Fin m, excl r s ∈ (upS F)^[d0] seed ∨ vis r s ∈ (upS F)^[d0] seed) :
   target ∈ (upS F)^[d0 + 2 + Nat.clog 2 m + Nat.clog 2 R] seed := by
 dsimp only [bco] at hF
 let dummy : Fin R → Fin m → LN V := fun _ _ => excl ⟨0, hR⟩ ⟨0, hm⟩
 set okRes := boa R m excl vis 0 dummy st
 set gridRes := baog R m hR hm okRes.1 okRes.2
 have hFgrid : ∀ C ∈ gridRes.2.2, C ∈ F := fun C hC =>
   hF C (by simp only [ei2, addCl, List.mem_cons]; exact Or.inr hC)
 have hFok : ∀ C ∈ okRes.2.2, C ∈ F := fun C hC =>
   hFgrid C (baog_cm R m hR hm okRes.1 okRes.2 C hC)
 obtain ⟨r, hrs⟩ := hex
 have hrow_ok : ∀ s : Fin m, okRes.1 r s ∈ (upS F)^[d0 + 1] seed := fun s =>
   boa_up R m F seed excl vis d0 r s R 0 (Nat.sub_zero _) dummy st (Nat.zero_le _) hFok (hrs s)
 have hgrid_mem : gridRes.1 ∈ (upS F)^[(d0 + 1) + Nat.clog 2 m + Nat.clog 2 R] seed :=
   baog_up R m hR hm F seed okRes.1 okRes.2 (d0 + 1) hFgrid ⟨r, hrow_ok⟩
 have hC : ({negL gridRes.1, target} : CN V) ∈ F :=
   hF _ (by dsimp only [gridRes, ei2, addCl]; simp)
 have htarg_mem : target ∈ (upS F)^[((d0 + 1) + Nat.clog 2 m + Nat.clog 2 R) + 1] seed := by
   rw [Function.iterate_succ_apply']
   exact upStep_unit2 hC (by simpa [negL_negL] using hgrid_mem)
 exact upStep_iter_le F seed (by omega) htarg_mem

def bci (n t h' R : ℕ) (hR : 1 ≤ R)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ℕ → St (Fin n ⊕ Fin t) → St (Fin n ⊕ Fin t)
 | k, st =>
   if hk : k < n then
     let i : Fin n := ⟨k, hk⟩
     let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i).2
     let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i).1
     let st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i), false) st
     let st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i), true) st1
     bci n t h' R hR exclGrid br (k + 1) st2
   else st
termination_by k => n - k

lemma bci_cm (n t h' R : ℕ) (hR : 1 ≤ R)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ∀ (m k : ℕ) (_ : n - k = m) (st : St (Fin n ⊕ Fin t)) (C : CN (Fin n ⊕ Fin t)),
     C ∈ st.2 → C ∈ (bci n t h' R hR exclGrid br k st).2
 | 0, k, hm, st, C, hC => by
   have hge : ¬ (k < n) := by omega
   unfold bci; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, k, hm, st, C, hC => by
   have hk : k < n := by omega
   have hm1 : n - (k + 1) = m := by omega
   unfold bci; simp only [hk, ↓reduceDIte]
   apply bci_cm n t h' R hR exclGrid br m (k + 1) hm1 _ C
   apply bco_cm
   apply bco_cm
   exact hC

lemma bci_pr (n t h' R : ℕ) (hR : 1 ≤ R)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ∀ (m k : ℕ) (_ : n - k = m) (st : St (Fin n ⊕ Fin t)),
     VS st →
     (∀ r s, VL st.1 (exclGrid r s)) →
     (∀ r s i, VL st.1 ((br r s).xDual i).1 ∧ VL st.1 ((br r s).xDual i).2) →
     let st' := bci n t h' R hR exclGrid br k st
     VS st' ∧
     st.1 ≤ st'.1 ∧
     st'.1 ≤ st.1 + (6 * R * 2 ^ h' + 4 * R) * m ∧
     st'.2.length ≤ st.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * m ∧
     (∀ C ∈ st.2, C ∈ st'.2)
 | 0, k, hm, st, hst, _, _ => by
   have hge : ¬ (k < n) := by omega
   unfold bci; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h⟩
 | m + 1, k, hm, st, hst, hex, hx => by
   have hk : k < n := by omega
   have hm1 : n - (k + 1) = m := by omega
   unfold bci; simp only [hk, ↓reduceDIte]
   set i : Fin n := ⟨k, hk⟩
   let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i).2
   let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i).1
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i), false) st
       hst (fun r s => ⟨hex r s, (hx r s i).2⟩) (validLit_inl _ _ _)
   set st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i), false) st
   obtain ⟨hst2, hle2, hm2_v, hl2_c, hsub2⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i), true) st1
       hst1 (fun r s => ⟨(hex r s).mono hle1, (hx r s i).1.mono hle1⟩) (validLit_inl _ _ _)
   set st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i), true) st1
   obtain ⟨r1, r2, r3, r4, r5⟩ :=
     bci_pr n t h' R hR exclGrid br m (k + 1) hm1 st2 hst2
       (fun r s => (hex r s).mono (le_trans hle1 hle2))
       (fun r s j => ⟨(hx r s j).1.mono (le_trans hle1 hle2), (hx r s j).2.mono (le_trans hle1 hle2)⟩)
   refine ⟨r1, le_trans (le_trans hle1 hle2) r2, ?_, ?_, fun C hC => r5 C (hsub2 C (hsub1 C hC))⟩
   · calc (bci n t h' R hR exclGrid br (k + 1) st2).1
       _ ≤ st2.1 + (6 * R * 2 ^ h' + 4 * R) * m := r3
       _ ≤ (st1.1 + (3 * R * 2 ^ h' + 2 * R)) + (6 * R * 2 ^ h' + 4 * R) * m := by omega
       _ ≤ ((st.1 + (3 * R * 2 ^ h' + 2 * R)) + (3 * R * 2 ^ h' + 2 * R)) + (6 * R * 2 ^ h' + 4 * R) * m := by omega
       _ = st.1 + (6 * R * 2 ^ h' + 4 * R) * (m + 1) := by ring
   · calc (bci n t h' R hR exclGrid br (k + 1) st2).2.length
       _ ≤ st2.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * m := r4
       _ ≤ (st1.2.length + (9 * R * 2 ^ h' + 6 * R + 1)) + (18 * R * 2 ^ h' + 12 * R + 2) * m := by omega
       _ ≤ ((st.2.length + (9 * R * 2 ^ h' + 6 * R + 1)) + (9 * R * 2 ^ h' + 6 * R + 1)) +
           (18 * R * 2 ^ h' + 12 * R + 2) * m := by omega
       _ = st.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * (m + 1) := by ring

open Classical in
lemma bci_sat (n t h' R : ℕ) (hR : 1 ≤ R)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ∀ (m k : ℕ) (_ : n - k = m) (st : St (Fin n ⊕ Fin t)) (α : Sum (Fin n ⊕ Fin t) ℕ → Bool),
     VS st →
     (∀ r s, VL st.1 (exclGrid r s)) →
     (∀ r s i, VL st.1 ((br r s).xDual i).1 ∧ VL st.1 ((br r s).xDual i).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     (∀ r : Fin R, ∃ s : Fin (2 ^ h'),
       lEv α (exclGrid r s) = false ∧
       ∀ i : Fin n, lEv α ((br r s).xDual i).1 = α (Sum.inl (Sum.inl i)) ∧
                   lEv α ((br r s).xDual i).2 = !(α (Sum.inl (Sum.inl i)))) →
     ∃ α' : Sum (Fin n ⊕ Fin t) ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (bci n t h' R hR exclGrid br k st).2, ClauseSat α' C)
 | 0, k, hm, st, α, _, _, _, hsat, _ => by
   have hge : ¬ (k < n) := by omega
   unfold bci; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat⟩
 | m + 1, k, hm, st, α, hst, hex, hx, hsat, hgood => by
   have hk : k < n := by omega
   have hm1 : n - (k + 1) = m := by omega
   unfold bci; simp only [hk, ↓reduceDIte]
   set i : Fin n := ⟨k, hk⟩
   let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i).2
   let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i).1
   obtain ⟨hst1, hle1, _, _, _⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i), false) st
       hst (fun r s => ⟨hex r s, (hx r s i).2⟩) (validLit_inl _ _ _)
   obtain ⟨α1, h1inl, h1lt, h1sat⟩ :=
     bco_sat R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i), false) st α
       hst (fun r s => ⟨hex r s, (hx r s i).2⟩) (validLit_inl _ _ _) hsat
       (fun hf r => by
         obtain ⟨s, hes, hxs⟩ := hgood r
         refine ⟨s, hes, ?_⟩
         have hval : α (Sum.inl (Sum.inl i)) = true := by simpa [lEv] using hf
         simp [visF, (hxs i).2, hval])
   set st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i), false) st
   obtain ⟨hst2, hle2, _, _, _⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i), true) st1
       hst1 (fun r s => ⟨(hex r s).mono hle1, (hx r s i).1.mono hle1⟩) (validLit_inl _ _ _)
   obtain ⟨α2, h2inl, h2lt, h2sat⟩ :=
     bco_sat R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i), true) st1 α1
       hst1 (fun r s => ⟨(hex r s).mono hle1, (hx r s i).1.mono hle1⟩) (validLit_inl _ _ _) h1sat
       (fun hf r => by
         obtain ⟨s, hes, hxs⟩ := hgood r
         refine ⟨s, (lecl h1inl h1lt (hex r s)).trans hes, ?_⟩
         have hval : α (Sum.inl (Sum.inl i)) = false := by
           simpa [lEv, h1inl] using hf
         rw [lecl h1inl h1lt (hx r s i).1]
         simp [(hxs i).1, hval])
   set st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i), true) st1
   have hgood2 : ∀ r : Fin R, ∃ s : Fin (2 ^ h'),
       lEv α2 (exclGrid r s) = false ∧
       ∀ j : Fin n, lEv α2 ((br r s).xDual j).1 = α2 (Sum.inl (Sum.inl j)) ∧
                   lEv α2 ((br r s).xDual j).2 = !(α2 (Sum.inl (Sum.inl j))) := by
     intro r
     obtain ⟨s, hes, hxs⟩ := hgood r
     refine ⟨s, ?_, fun j => ?_⟩
     · exact (lecl h2inl h2lt ((hex r s).mono hle1)).trans
         ((lecl h1inl h1lt (hex r s)).trans hes)
     · constructor
       · rw [lecl h2inl h2lt ((hx r s j).1.mono hle1), lecl h1inl h1lt (hx r s j).1,
           h2inl, h1inl]
         exact (hxs j).1
       · rw [lecl h2inl h2lt ((hx r s j).2.mono hle1), lecl h1inl h1lt (hx r s j).2,
           h2inl, h1inl]
         exact (hxs j).2
   obtain ⟨α', h'inl, h'lt, h'sat⟩ :=
     bci_sat n t h' R hR exclGrid br m (k + 1) hm1 st2 α2 hst2
       (fun r s => (hex r s).mono (le_trans hle1 hle2))
       (fun r s j => ⟨(hx r s j).1.mono (le_trans hle1 hle2), (hx r s j).2.mono (le_trans hle1 hle2)⟩)
       h2sat hgood2
   refine ⟨α', fun v => (h'inl v).trans ((h2inl v).trans (h1inl v)), fun w hw => ?_, h'sat⟩
   exact (h'lt w (lt_of_lt_of_le hw (le_trans hle1 hle2))).trans ((h2lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw))

lemma bci_up (n t h' R : ℕ) (hR : 1 ≤ R)
   (F : Finset (CN (Fin n ⊕ Fin t))) (seed : Set (LN (Fin n ⊕ Fin t)))
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t)
   (d0 : ℕ) (i : Fin n) (sign : Bool) :
   ∀ (m k : ℕ) (_ : n - k = m) (st : St (Fin n ⊕ Fin t)),
     k ≤ i.val →
     (∀ C ∈ (bci n t h' R hR exclGrid br k st).2, C ∈ F) →
     (∃ r : Fin R, ∀ s : Fin (2 ^ h'),
       exclGrid r s ∈ (upS F)^[d0] seed ∨
         lod ((br r s).xDual i) sign ∈ (upS F)^[d0] seed) →
     (Sum.inl (Sum.inl i), sign) ∈ (upS F)^[d0 + 2 + h' + Nat.clog 2 R] seed
 | 0, k, hm, _, hik, _, _ => by exfalso; omega
 | m + 1, k, hm, st, hik, hF, hex => by
   have hk : k < n := by omega
   have hm1 : n - (k + 1) = m := by omega
   unfold bci at hF
   simp only [hk, ↓reduceDIte] at hF
   set i0 : Fin n := ⟨k, hk⟩
   let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i0).2
   let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).xDual i0).1
   set st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inl i0), false) st
   set st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inl i0), true) st1
   by_cases heq : k = i.val
   · have hieq : i = i0 := Fin.ext heq.symm
     rw [hieq] at hex ⊢
     have hF2 : ∀ C ∈ st2.2, C ∈ F := fun C hC =>
       hF C (bci_cm n t h' R hR exclGrid br m (k + 1) hm1 st2 C hC)
     have hF1 : ∀ C ∈ st1.2, C ∈ F := fun C hC =>
       hF2 C (bco_cm R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT _ st1 C hC)
     have hclog : Nat.clog 2 (2 ^ h') = h' := by simp
     cases hsn : sign
     · have hmem := bco_up R (2 ^ h') hR Nat.one_le_two_pow F seed exclGrid visF
         (Sum.inl (Sum.inl i0), false) st d0 hF1
         (by simpa [visF, lod, hsn] using hex)
       simpa [hclog] using hmem
     · have hmem := bco_up R (2 ^ h') hR Nat.one_le_two_pow F seed exclGrid visT
         (Sum.inl (Sum.inl i0), true) st1 d0 hF2
         (by simpa [visT, lod, hsn] using hex)
       simpa [hclog] using hmem
   · exact bci_up n t h' R hR F seed exclGrid br d0 i sign m (k + 1) hm1 st2 (by omega) hF hex

def bcr (n t h' R : ℕ) (hR : 1 ≤ R) (out : Fin t → ℕ)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ℕ → St (Fin n ⊕ Fin t) → St (Fin n ⊕ Fin t)
 | k, st =>
   if hk : k < t then
     let j : Fin t := ⟨k, hk⟩
     let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j)).2
     let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j)).1
     let st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j), false) st
     let st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j), true) st1
     bcr n t h' R hR out exclGrid br (k + 1) st2
   else st
termination_by k => t - k

lemma bcr_cm (n t h' R : ℕ) (hR : 1 ≤ R) (out : Fin t → ℕ)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ∀ (m k : ℕ) (_ : t - k = m) (st : St (Fin n ⊕ Fin t)) (C : CN (Fin n ⊕ Fin t)),
     C ∈ st.2 → C ∈ (bcr n t h' R hR out exclGrid br k st).2
 | 0, k, hm, st, C, hC => by
   have hge : ¬ (k < t) := by omega
   unfold bcr; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, k, hm, st, C, hC => by
   have hk : k < t := by omega
   have hm1 : t - (k + 1) = m := by omega
   unfold bcr; simp only [hk, ↓reduceDIte]
   apply bcr_cm n t h' R hR out exclGrid br m (k + 1) hm1 _ C
   apply bco_cm
   apply bco_cm
   exact hC

lemma bcr_pr (n t h' R : ℕ) (hR : 1 ≤ R) (out : Fin t → ℕ)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ∀ (m k : ℕ) (_ : t - k = m) (st : St (Fin n ⊕ Fin t)),
     VS st →
     (∀ r s, VL st.1 (exclGrid r s)) →
     (∀ r s j, VL st.1 ((br r s).wiresOut (out j)).1 ∧ VL st.1 ((br r s).wiresOut (out j)).2) →
     let st' := bcr n t h' R hR out exclGrid br k st
     VS st' ∧
     st.1 ≤ st'.1 ∧
     st'.1 ≤ st.1 + (6 * R * 2 ^ h' + 4 * R) * m ∧
     st'.2.length ≤ st.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * m ∧
     (∀ C ∈ st.2, C ∈ st'.2)
 | 0, k, hm, st, hst, _, _ => by
   have hge : ¬ (k < t) := by omega
   unfold bcr; simp only [hge, ↓reduceDIte]
   exact ⟨hst, le_rfl, by simp, by simp, fun _ h => h⟩
 | m + 1, k, hm, st, hst, hex, hw => by
   have hk : k < t := by omega
   have hm1 : t - (k + 1) = m := by omega
   unfold bcr; simp only [hk, ↓reduceDIte]
   set j : Fin t := ⟨k, hk⟩
   let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j)).2
   let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j)).1
   obtain ⟨hst1, hle1, hm1_v, hl1_c, hsub1⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j), false) st
       hst (fun r s => ⟨hex r s, (hw r s j).2⟩) (validLit_inl _ _ _)
   set st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j), false) st
   obtain ⟨hst2, hle2, hm2_v, hl2_c, hsub2⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j), true) st1
       hst1 (fun r s => ⟨(hex r s).mono hle1, (hw r s j).1.mono hle1⟩) (validLit_inl _ _ _)
   set st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j), true) st1
   obtain ⟨r1, r2, r3, r4, r5⟩ :=
     bcr_pr n t h' R hR out exclGrid br m (k + 1) hm1 st2 hst2
       (fun r s => (hex r s).mono (le_trans hle1 hle2))
       (fun r s j' => ⟨(hw r s j').1.mono (le_trans hle1 hle2), (hw r s j').2.mono (le_trans hle1 hle2)⟩)
   refine ⟨r1, le_trans (le_trans hle1 hle2) r2, ?_, ?_, fun C hC => r5 C (hsub2 C (hsub1 C hC))⟩
   · calc (bcr n t h' R hR out exclGrid br (k + 1) st2).1
       _ ≤ st2.1 + (6 * R * 2 ^ h' + 4 * R) * m := r3
       _ ≤ (st1.1 + (3 * R * 2 ^ h' + 2 * R)) + (6 * R * 2 ^ h' + 4 * R) * m := by omega
       _ ≤ ((st.1 + (3 * R * 2 ^ h' + 2 * R)) + (3 * R * 2 ^ h' + 2 * R)) + (6 * R * 2 ^ h' + 4 * R) * m := by omega
       _ = st.1 + (6 * R * 2 ^ h' + 4 * R) * (m + 1) := by ring
   · calc (bcr n t h' R hR out exclGrid br (k + 1) st2).2.length
       _ ≤ st2.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * m := r4
       _ ≤ (st1.2.length + (9 * R * 2 ^ h' + 6 * R + 1)) + (18 * R * 2 ^ h' + 12 * R + 2) * m := by omega
       _ ≤ ((st.2.length + (9 * R * 2 ^ h' + 6 * R + 1)) + (9 * R * 2 ^ h' + 6 * R + 1)) +
           (18 * R * 2 ^ h' + 12 * R + 2) * m := by omega
       _ = st.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * (m + 1) := by ring

open Classical in
lemma bcr_sat (n t h' R : ℕ) (hR : 1 ≤ R) (out : Fin t → ℕ)
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t) :
   ∀ (m k : ℕ) (_ : t - k = m) (st : St (Fin n ⊕ Fin t)) (α : Sum (Fin n ⊕ Fin t) ℕ → Bool),
     VS st →
     (∀ r s, VL st.1 (exclGrid r s)) →
     (∀ r s j, VL st.1 ((br r s).wiresOut (out j)).1 ∧ VL st.1 ((br r s).wiresOut (out j)).2) →
     (∀ C ∈ st.2, ClauseSat α C) →
     (∀ r : Fin R, ∃ s : Fin (2 ^ h'),
       lEv α (exclGrid r s) = false ∧
       ∀ j : Fin t, lEv α ((br r s).wiresOut (out j)).1 = α (Sum.inl (Sum.inr j)) ∧
                   lEv α ((br r s).wiresOut (out j)).2 = !(α (Sum.inl (Sum.inr j)))) →
     ∃ α' : Sum (Fin n ⊕ Fin t) ℕ → Bool,
       (∀ v, α' (Sum.inl v) = α (Sum.inl v)) ∧
       (∀ w < st.1, α' (Sum.inr w) = α (Sum.inr w)) ∧
       (∀ C ∈ (bcr n t h' R hR out exclGrid br k st).2, ClauseSat α' C)
 | 0, k, hm, st, α, _, _, _, hsat, _ => by
   have hge : ¬ (k < t) := by omega
   unfold bcr; simp only [hge, ↓reduceDIte]
   exact ⟨α, fun _ => rfl, fun _ _ => rfl, hsat⟩
 | m + 1, k, hm, st, α, hst, hex, hw, hsat, hgood => by
   have hk : k < t := by omega
   have hm1 : t - (k + 1) = m := by omega
   unfold bcr; simp only [hk, ↓reduceDIte]
   set j : Fin t := ⟨k, hk⟩
   let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j)).2
   let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j)).1
   obtain ⟨hst1, hle1, _, _, _⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j), false) st
       hst (fun r s => ⟨hex r s, (hw r s j).2⟩) (validLit_inl _ _ _)
   obtain ⟨α1, h1inl, h1lt, h1sat⟩ :=
     bco_sat R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j), false) st α
       hst (fun r s => ⟨hex r s, (hw r s j).2⟩) (validLit_inl _ _ _) hsat
       (fun hf r => by
         obtain ⟨s, hes, hws⟩ := hgood r
         refine ⟨s, hes, ?_⟩
         have hval : α (Sum.inl (Sum.inr j)) = true := by simpa [lEv] using hf
         simp [visF, (hws j).2, hval])
   set st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j), false) st
   obtain ⟨hst2, hle2, _, _, _⟩ :=
     bco_pr R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j), true) st1
       hst1 (fun r s => ⟨(hex r s).mono hle1, (hw r s j).1.mono hle1⟩) (validLit_inl _ _ _)
   obtain ⟨α2, h2inl, h2lt, h2sat⟩ :=
     bco_sat R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j), true) st1 α1
       hst1 (fun r s => ⟨(hex r s).mono hle1, (hw r s j).1.mono hle1⟩) (validLit_inl _ _ _) h1sat
       (fun hf r => by
         obtain ⟨s, hes, hws⟩ := hgood r
         refine ⟨s, (lecl h1inl h1lt (hex r s)).trans hes, ?_⟩
         have hval : α (Sum.inl (Sum.inr j)) = false := by
           simpa [lEv, h1inl] using hf
         rw [lecl h1inl h1lt (hw r s j).1]
         simp [(hws j).1, hval])
   set st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j), true) st1
   have hgood2 : ∀ r : Fin R, ∃ s : Fin (2 ^ h'),
       lEv α2 (exclGrid r s) = false ∧
       ∀ j' : Fin t, lEv α2 ((br r s).wiresOut (out j')).1 = α2 (Sum.inl (Sum.inr j')) ∧
                     lEv α2 ((br r s).wiresOut (out j')).2 = !(α2 (Sum.inl (Sum.inr j'))) := by
     intro r
     obtain ⟨s, hes, hws⟩ := hgood r
     refine ⟨s, ?_, fun j' => ?_⟩
     · exact (lecl h2inl h2lt ((hex r s).mono hle1)).trans
         ((lecl h1inl h1lt (hex r s)).trans hes)
     · constructor
       · rw [lecl h2inl h2lt ((hw r s j').1.mono hle1), lecl h1inl h1lt (hw r s j').1,
           h2inl, h1inl]
         exact (hws j').1
       · rw [lecl h2inl h2lt ((hw r s j').2.mono hle1), lecl h1inl h1lt (hw r s j').2,
           h2inl, h1inl]
         exact (hws j').2
   obtain ⟨α', h'inl, h'lt, h'sat⟩ :=
     bcr_sat n t h' R hR out exclGrid br m (k + 1) hm1 st2 α2 hst2
       (fun r s => (hex r s).mono (le_trans hle1 hle2))
       (fun r s j' => ⟨(hw r s j').1.mono (le_trans hle1 hle2), (hw r s j').2.mono (le_trans hle1 hle2)⟩)
       h2sat hgood2
   refine ⟨α', fun v => (h'inl v).trans ((h2inl v).trans (h1inl v)), fun w hw => ?_, h'sat⟩
   exact (h'lt w (lt_of_lt_of_le hw (le_trans hle1 hle2))).trans ((h2lt w (lt_of_lt_of_le hw hle1)).trans (h1lt w hw))

lemma bcr_up (n t h' R : ℕ) (hR : 1 ≤ R) (out : Fin t → ℕ)
   (F : Finset (CN (Fin n ⊕ Fin t))) (seed : Set (LN (Fin n ⊕ Fin t)))
   (exclGrid : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t))
   (br : Fin R → Fin (2 ^ h') → BR n t)
   (d0 : ℕ) (j : Fin t) (sign : Bool) :
   ∀ (m k : ℕ) (_ : t - k = m) (st : St (Fin n ⊕ Fin t)),
     k ≤ j.val →
     (∀ C ∈ (bcr n t h' R hR out exclGrid br k st).2, C ∈ F) →
     (∃ r : Fin R, ∀ s : Fin (2 ^ h'),
       exclGrid r s ∈ (upS F)^[d0] seed ∨
         lod ((br r s).wiresOut (out j)) sign ∈ (upS F)^[d0] seed) →
     (Sum.inl (Sum.inr j), sign) ∈ (upS F)^[d0 + 2 + h' + Nat.clog 2 R] seed
 | 0, k, hm, _, hjk, _, _ => by exfalso; omega
 | m + 1, k, hm, st, hjk, hF, hex => by
   have hk : k < t := by omega
   have hm1 : t - (k + 1) = m := by omega
   unfold bcr at hF
   simp only [hk, ↓reduceDIte] at hF
   set j0 : Fin t := ⟨k, hk⟩
   let visF : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j0)).2
   let visT : Fin R → Fin (2 ^ h') → LN (Fin n ⊕ Fin t) := fun r s => ((br r s).wiresOut (out j0)).1
   set st1 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visF (Sum.inl (Sum.inr j0), false) st
   set st2 := bco R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT (Sum.inl (Sum.inr j0), true) st1
   by_cases heq : k = j.val
   · have hjeq : j = j0 := Fin.ext heq.symm
     rw [hjeq] at hex ⊢
     have hF2 : ∀ C ∈ st2.2, C ∈ F := fun C hC =>
       hF C (bcr_cm n t h' R hR out exclGrid br m (k + 1) hm1 st2 C hC)
     have hF1 : ∀ C ∈ st1.2, C ∈ F := fun C hC =>
       hF2 C (bco_cm R (2 ^ h') hR Nat.one_le_two_pow exclGrid visT _ st1 C hC)
     have hclog : Nat.clog 2 (2 ^ h') = h' := by simp
     cases hsn : sign
     · have hmem := bco_up R (2 ^ h') hR Nat.one_le_two_pow F seed exclGrid visF
         (Sum.inl (Sum.inr j0), false) st d0 hF1
         (by simpa [visF, lod, hsn] using hex)
       simpa [hclog] using hmem
     · have hmem := bco_up R (2 ^ h') hR Nat.one_le_two_pow F seed exclGrid visT
         (Sum.inl (Sum.inr j0), true) st1 d0 hF2
         (by simpa [visT, lod, hsn] using hex)
       simpa [hclog] using hmem
   · exact bcr_up n t h' R hR out F seed exclGrid br d0 j sign m (k + 1) hm1 st2 (by omega) hF hex

def bki (n t : ℕ) (kL : Fin n → LN (Fin n ⊕ Fin t)) :
   ℕ → St (Fin n ⊕ Fin t) → St (Fin n ⊕ Fin t)
 | i, st =>
   if hi : i < n then
     let ifin : Fin n := ⟨i, hi⟩
     let st1 := ei2 (Sum.inl (Sum.inl ifin), false) (kL ifin)
       (ei2 (Sum.inl (Sum.inl ifin), true) (kL ifin) st)
     bki n t kL (i + 1) st1
   else st
termination_by i => n - i

lemma bki_cm (n t : ℕ) (kL : Fin n → LN (Fin n ⊕ Fin t)) :
   ∀ (m i : ℕ) (_ : n - i = m) (st : St (Fin n ⊕ Fin t)) (C : CN (Fin n ⊕ Fin t)),
     C ∈ st.2 → C ∈ (bki n t kL i st).2
 | 0, i, hm, st, C, hC => by
   have hge : ¬ (i < n) := by omega
   unfold bki; simp only [hge, ↓reduceDIte]; exact hC
 | m + 1, i, hm, st, C, hC => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = m := by omega
   unfold bki; simp only [hi, ↓reduceDIte]
   apply bki_cm n t kL m (i + 1) hm1 _ C
   simp [ei2, addCl, hC]

lemma bki_pr (n t : ℕ) (kL : Fin n → LN (Fin n ⊕ Fin t)) :
   ∀ (m i : ℕ) (_ : n - i = m) (st : St (Fin n ⊕ Fin t)),
     VS st →
     (∀ j : Fin n, VL st.1 (kL j)) →
     let st' := bki n t kL i st
     VS st' ∧
     st'.1 = st.1 ∧
     st'.2.length ≤ st.2.length + 2 * m ∧
     (∀ C ∈ st.2, C ∈ st'.2) ∧
     ∀ j : Fin n, i ≤ j.val →
       {negL (Sum.inl (Sum.inl j), true), kL j} ∈ st'.2 ∧
       {negL (Sum.inl (Sum.inl j), false), kL j} ∈ st'.2
 | 0, i, hm, st, hst, _ => by
   have hge : ¬ (i < n) := by omega
   have heq : bki n t kL i st = st := by
     unfold bki; simp only [hge, ↓reduceDIte]
   dsimp only; rw [heq]
   exact ⟨hst, rfl, by simp, fun _ h => h, fun j hj => by exfalso; omega⟩
 | m + 1, i, hm, st, hst, hk => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = m := by omega
   unfold bki; simp only [hi, ↓reduceDIte]
   set ifin : Fin n := ⟨i, hi⟩
   set st1 := ei2 (Sum.inl (Sum.inl ifin), false) (kL ifin)
     (ei2 (Sum.inl (Sum.inl ifin), true) (kL ifin) st)
   have hst1 : VS st1 :=
     validSt_emitImp2 (validSt_emitImp2 hst (validLit_inl _ _ _) (hk ifin))
       (validLit_inl _ _ _) (hk ifin)
   have hsub1 : ∀ C ∈ st.2, C ∈ st1.2 := fun C hC => by simp [st1, ei2, addCl, hC]
   obtain ⟨r1, r2, r3, r4, r5⟩ := bki_pr n t kL m (i + 1) hm1 st1 hst1 hk
   have hlen1 : st1.2.length = st.2.length + 2 := rfl
   refine ⟨r1, r2, by omega, fun C hC => r4 C (hsub1 C hC), fun j hj => ?_⟩
   by_cases heq : i = j.val
   · have hjeq : j = ifin := Fin.ext heq.symm
     subst hjeq
     exact ⟨r4 _ (by simp [st1, ei2, addCl]), r4 _ (by simp [st1, ei2, addCl])⟩
   · exact r5 j (by omega)

lemma bki_sat (n t : ℕ) (kL : Fin n → LN (Fin n ⊕ Fin t))
   (α : Sum (Fin n ⊕ Fin t) ℕ → Bool) :
   ∀ (m i : ℕ) (_ : n - i = m) (st : St (Fin n ⊕ Fin t)),
     (∀ C ∈ st.2, ClauseSat α C) →
     (∀ j : Fin n, lEv α (kL j) = true) →
     ∀ C ∈ (bki n t kL i st).2, ClauseSat α C
 | 0, i, hm, st, hsat, _ => by
   have hge : ¬ (i < n) := by omega
   unfold bki; simp only [hge, ↓reduceDIte]; exact hsat
 | m + 1, i, hm, st, hsat, hk => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = m := by omega
   unfold bki; simp only [hi, ↓reduceDIte]
   apply bki_sat n t kL α m (i + 1) hm1 _ _ hk
   simp only [ei2, addCl, List.mem_cons, forall_eq_or_imp, clauseSat_imp2]
   exact ⟨fun _ => hk ⟨i, hi⟩, fun _ => hk ⟨i, hi⟩, hsat⟩

lemma bki_up (n t : ℕ) (kL : Fin n → LN (Fin n ⊕ Fin t))
   (F : Finset (CN (Fin n ⊕ Fin t))) (seed : Set (LN (Fin n ⊕ Fin t)))
   (st : St (Fin n ⊕ Fin t))
   (hF : ∀ C ∈ (bki n t kL 0 st).2, C ∈ F)
   (hk : ∀ j : Fin n, VL st.1 (kL j))
   (hst : VS st) :
   ∀ (j : Fin n) (b : Bool), (Sum.inl (Sum.inl j), b) ∈ seed →
     kL j ∈ (upS F)^[1] seed := by
 intro j b hmem
 obtain ⟨_, _, _, _, hmem_cl⟩ := bki_pr n t kL n 0 (Nat.sub_zero _) st hst hk
 have hc := hmem_cl j (Nat.zero_le _)
 rw [Function.iterate_one]
 cases hb : b
 · rw [hb] at hmem
   exact upStep_unit2 (hF _ hc.2) (by simpa [negL_negL] using hmem)
 · rw [hb] at hmem
   exact upStep_unit2 (hF _ hc.1) (by simpa [negL_negL] using hmem)

lemma brat_ss {V : Type} [DecidableEq V] (R m : ℕ) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) :
   ∀ (k r : ℕ) (_ : R - r = k) (arr : Fin R → LN V) (st : St V) (α : Sum V ℕ → Bool),
     (∀ C ∈ (brat R m hm lits r arr st).2.2, ClauseSat α C) →
     (∀ C ∈ st.2, ClauseSat α C) ∧
     ∀ rf : Fin R, r ≤ rf.val →
       lEv α ((brat R m hm lits r arr st).1 rf) =
         (List.finRange m).all (fun s => lEv α (lits rf s))
 | 0, r, hk, arr, st, α, hsat => by
   have hge : ¬ (r < R) := by omega
   unfold brat at hsat ⊢; simp only [hge, ↓reduceDIte] at hsat ⊢
   exact ⟨hsat, fun rf hrf => by exfalso; omega⟩
 | k + 1, r, hk, arr, st, α, hsat => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = k := by omega
   unfold brat at hsat ⊢
   simp only [hr, ↓reduceDIte] at hsat ⊢
   set rf : Fin R := ⟨r, hr⟩
   set T_r := BTree.ofList ((List.finRange m).map (lits rf)) (by simp [list_finRange_ne_nil m hm])
   set res := bat T_r st
   let arr' : Fin R → LN V := fun r' => if r' = rf then res.1 else arr r'
   obtain ⟨hsat_res, hrec⟩ := brat_ss R m hm lits k (r + 1) hm1 arr' res.2 α hsat
   obtain ⟨hsat_st, hand⟩ := bat_ss T_r st α hsat_res
   refine ⟨hsat_st, fun rf' hrf' => ?_⟩
   by_cases heq : r = rf'.val
   · have hrfeq : rf' = rf := Fin.ext heq.symm
     subst hrfeq
     rw [brat_uc R m hm lits k (r + 1) hm1 arr' res.2 rf (by omega)]
     dsimp only [arr']
     simp only [↓reduceIte]
     rw [hand, BTree.leaves_ofList, List.all_map]
     rfl
   · exact hrec rf' (by omega)

lemma baog_ss {V : Type} [DecidableEq V] (R m : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m)
   (lits : Fin R → Fin m → LN V) (st : St V) (α : Sum V ℕ → Bool)
   (hsat : ∀ C ∈ (baog R m hR hm lits st).2.2, ClauseSat α C) :
   (∀ C ∈ st.2, ClauseSat α C) ∧
   lEv α (baog R m hR hm lits st).1 =
     decide (∃ r : Fin R, ∀ s : Fin m, lEv α (lits r s) = true) := by
 dsimp only [baog] at hsat ⊢
 set dummy : Fin R → LN V := fun _ => lits ⟨0, hR⟩ ⟨0, hm⟩
 set rowRes := brat R m hm lits 0 dummy st
 set T_or := BTree.ofList ((List.finRange R).map rowRes.1) (by simp [list_finRange_ne_nil R hR])
 obtain ⟨hsat_row, hor⟩ := bot_ss T_or rowRes.2 α hsat
 obtain ⟨hsat_st, hrow⟩ := brat_ss R m hm lits R 0 (Nat.sub_zero _) dummy st α hsat_row
 refine ⟨hsat_st, ?_⟩
 rw [hor, BTree.leaves_ofList, List.any_map, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
 simp only [Function.comp_apply]
 constructor
 · rintro ⟨r, _, hr⟩
   refine ⟨r, fun s => ?_⟩
   rw [hrow r (Nat.zero_le _), List.all_eq_true] at hr
   exact hr s (List.mem_finRange s)
 · rintro ⟨r, hrs⟩
   refine ⟨r, List.mem_finRange r, ?_⟩
   rw [hrow r (Nat.zero_le _), List.all_eq_true]
   exact fun s _ => hrs s

lemma bbi_ss {V : Type} [DecidableEq V] (n : ℕ)
   (rawIn : Fin n → LN V) (wRow : Fin n → Bool → LN V)
   (xDual : Fin n → LN V × LN V) (excl : LN V) (α : Sum V ℕ → Bool) :
   ∀ (r i : ℕ) (_ : n - i = r) (st : St V),
     (∀ C ∈ (bbi n rawIn wRow xDual excl i st).2, ClauseSat α C) →
     lEv α excl = false →
     (∀ C ∈ st.2, ClauseSat α C) ∧
     ∀ j : Fin n, i ≤ j.val →
       lEv α (xDual j).1 = lEv α (rawIn j) ∧
       lEv α (xDual j).2 = !(lEv α (rawIn j))
 | 0, i, hr, st, hsat, _ => by
   have hge : ¬ (i < n) := by omega
   unfold bbi at hsat; simp only [hge, ↓reduceDIte] at hsat
   exact ⟨hsat, fun j hj => by exfalso; omega⟩
 | r + 1, i, hr, st, hsat, hex => by
   have hi : i < n := by omega
   have hm1 : n - (i + 1) = r := by omega
   unfold bbi at hsat; simp only [hi, ↓reduceDIte] at hsat
   set ifin : Fin n := ⟨i, hi⟩
   set st1 :=
     ei3 (xDual ifin).1 (xDual ifin).2 excl
       (ei2 (wRow ifin false) (xDual ifin).2
         (ei2 (negL (rawIn ifin)) (xDual ifin).2
           (ei2 (wRow ifin true) (xDual ifin).1
             (ei2 (rawIn ifin) (xDual ifin).1 st))))
   obtain ⟨hsat1, hrec⟩ := bbi_ss n rawIn wRow xDual excl α r (i + 1) hm1 st1 hsat hex
   simp only [st1, ei3, ei2, addCl, List.mem_cons, forall_eq_or_imp,
     clauseSat_imp3, clauseSat_imp2, litEval_negL] at hsat1
   rcases hsat1 with ⟨h3, _, h2f, _, h2t, hst0⟩
   refine ⟨hst0, fun j hj => ?_⟩
   by_cases heq : i = j.val
   · have hjeq : j = ifin := Fin.ext heq.symm
     subst hjeq
     cases hraw : lEv α (rawIn ifin)
     · have h1 := h2f (by simp [hraw])
       have hnot : lEv α (xDual ifin).1 = false := by
         cases hd1 : lEv α (xDual ifin).1
         · rfl
         · have hx := h3 hd1 h1; rw [hex] at hx; cases hx
       exact ⟨hnot, h1⟩
     · have h1 := h2t hraw
       have hnot : lEv α (xDual ifin).2 = false := by
         cases hd2 : lEv α (xDual ifin).2
         · rfl
         · have hx := h3 h1 hd2; rw [hex] at hx; cases hx
       exact ⟨h1, hnot⟩
   · exact hrec j (by omega)

lemma bb_ss (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (s : Fin (2 ^ h')) (st : St (Fin n ⊕ Fin t)) (α : Sum (Fin n ⊕ Fin t) ℕ → Bool)
   (hst : VS st)
   (hf1 : VL st.1 fd.1) (hf2 : VL st.1 fd.2)
   (hw : ∀ i b, VL st.1 (wRow i b))
   (hsat : ∀ C ∈ (bb n t h' D gates out H_row wRow fd s st).stOut.2, ClauseSat α C)
   (hfval : lEv α fd.1 = false ∧ lEv α fd.2 = true)
   (hex : lEv α (bb n t h' D gates out H_row wRow fd s st).excl = false)
   (hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D) :
   ∀ j : Fin t, α (Sum.inl (Sum.inr j)) =
     ((⟨gates, 0⟩ : BinaryCircuit).wires
       (List.ofFn (fun i : Fin n => α (Sum.inl (Sum.inl i))))).getD (out j) false := by
 dsimp only [bb] at hsat hex
 set pEx := fv st
 set excl := pEx.1
 set base := pEx.2.1
 set xDual : Fin n → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun i => (ag n base i false, ag n base i true)
 set st2 : St (Fin n ⊕ Fin t) := (base + 2 * n, pEx.2.2)
 set rawIn : Fin n → LN (Fin n ⊕ Fin t) := fun i => (Sum.inl (Sum.inl i), true)
 set stIn := bbi n rawIn wRow xDual excl 0 st2
 set stPar := bpc n h' H_row xDual excl s 0 stIn
 set wires0 : ℕ → LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t) :=
   fun u => if hu : u < n then xDual ⟨u, hu⟩ else fd
 set resG := bcg n D gates fd (some excl) 0 wires0 stPar
 have hst2v : VS st2 := fun C hC =>
   ⟨(hst C hC).1, (hst C hC).2.mono (by dsimp only [st2, base, pEx, fv]; omega)⟩
 have hst2_1 : st2.1 = st.1 + 1 + 2 * n := rfl
 have hex2 : VL st2.1 excl := (validLit_fresh st).mono (by rw [hst2_1]; omega)
 have hle02 : st.1 ≤ st2.1 := by omega
 have hv_in : ∀ j, VL st2.1 (rawIn j) ∧ VL st2.1 (wRow j false) ∧ VL st2.1 (wRow j true) ∧
     VL st2.1 (xDual j).1 ∧ VL st2.1 (xDual j).2 := fun j =>
   ⟨validLit_inl _ _ _, (hw j false).mono hle02, (hw j true).mono hle02,
   validLit_allocGrid _ n base j false, validLit_allocGrid _ n base j true⟩
 obtain ⟨hstIn, hIn_1, _, _, _⟩ :=
   bbi_pr n rawIn wRow xDual excl n 0 (Nat.sub_zero _) st2 hst2v hex2 hv_in
 have hexIn : VL stIn.1 excl := by rw [hIn_1]; exact hex2
 have hxIn : ∀ i, VL stIn.1 (xDual i).1 ∧ VL stIn.1 (xDual i).2 := fun i => by
   rw [hIn_1]; exact ⟨(hv_in i).2.2.2.1, (hv_in i).2.2.2.2⟩
 obtain ⟨hstPar, hPar_le, _, _, _⟩ :=
   bpc_pr n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn hstIn hexIn hxIn
 have hle2P : st2.1 ≤ stPar.1 := by rw [← hIn_1]; exact hPar_le
 have hle0P : st.1 ≤ stPar.1 := le_trans hle02 hle2P
 have hwires0 : ∀ u, VL stPar.1 (wires0 u).1 ∧ VL stPar.1 (wires0 u).2 := fun u => by
   dsimp only [wires0]
   split_ifs
   · exact ⟨(hv_in _).2.2.2.1.mono hle2P, (hv_in _).2.2.2.2.mono hle2P⟩
   · exact ⟨hf1.mono hle0P, hf2.mono hle0P⟩
 have hexPar : VL stPar.1 excl := hexIn.mono hPar_le
 obtain ⟨hstG, _, _, _, _, hGw, _, hGge⟩ :=
   bcg_pr n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar
     hstPar (hf1.mono hle0P) (hf2.mono hle0P) (fun _ h => by cases h; exact hexPar) hwires0
 have hexG : ∀ ex, some excl = some ex → VL resG.2.1 ex := fun _ h => by cases h; exact hexPar.mono (by omega)
 obtain ⟨_, _, _, _, hOmem⟩ :=
   boc_pr out resG.1 (some excl) t 0 (Nat.sub_zero _) resG.2 hstG hexG hGw
 have hsatG : ∀ C ∈ resG.2.2, ClauseSat α C := fun C hC =>
   hsat C (boc_cm out resG.1 (some excl) t 0 (Nat.sub_zero _) resG.2 C hC)
 have hsatPar : ∀ C ∈ stPar.2, ClauseSat α C := fun C hC =>
   hsatG C (bcg_cm n D gates fd (some excl) gates.length 0 (Nat.sub_zero _) wires0 stPar C hC)
 have hsatIn : ∀ C ∈ stIn.2, ClauseSat α C := fun C hC =>
   hsatPar C (bpc_cm n h' H_row xDual excl s h' 0 (Nat.sub_zero _) stIn C hC)
 obtain ⟨_, hxDual_eq⟩ :=
   bbi_ss n rawIn wRow xDual excl α n 0 (Nat.sub_zero _) st2 hsatIn hex
 let x : Fin n → Bool := fun i => α (Sum.inl (Sum.inl i))
 have hlt0 : ∀ u < n + 0, dv n gates u ≤ D →
     lEv α (wires0 u).1 = wv n x gates u ∧
     lEv α (wires0 u).2 = !(wv n x gates u) := by
   intro u hu _
   have hu' : u < n := by omega
   have hwv : wv n x gates u = x ⟨u, hu'⟩ := by rw [wv]; simp [hu']
   rw [hwv]
   dsimp only [wires0]
   simp only [hu', ↓reduceDIte]
   have h1 := hxDual_eq ⟨u, hu'⟩ (Nat.zero_le _)
   simpa [rawIn, lEv, x] using h1
 have hsound := bcg_ss n D gates fd (some excl) x gates.length 0
   (Nat.sub_zero _) wires0 stPar α hsatG (fun _ h => by cases h; exact hex) hfval hlt0
 intro jf
 rw [(wires_length_and_getD n x gates).2 (out jf)]
 have hom := hOmem jf (Nat.zero_le _)
 simp only at hom
 have hc1 := hsat _ hom.1
 have hc2 := hsat _ hom.2
 rw [clauseSat_imp3] at hc1 hc2
 by_cases hlt : out jf < n + gates.length
 · have hres := hsound (out jf) hlt (hD_bound jf)
   cases hwv : wv n x gates (out jf)
   · cases hvj : α (Sum.inl (Sum.inr jf))
     · rfl
     · have hbad := hc2 (by rw [hres.2, hwv]; rfl) (by simp [lEv, hvj])
       rw [hex] at hbad; cases hbad
   · cases hvj : α (Sum.inl (Sum.inr jf))
     · have hbad := hc1 (by rw [hres.1, hwv]) (by simp [lEv, hvj])
       rw [hex] at hbad; cases hbad
     · rfl
 · have hge : out jf ≥ n + gates.length := by omega
   have hres_eq : resG.1 (out jf) = wires0 (out jf) := hGge (out jf) hge
   have hwv : wv n x gates (out jf) = false := by
     rw [wv]; simp [show ¬ (out jf < n) by omega, hlt]
   have hnotn : ¬ (out jf < n) := by omega
   have h2 : lEv α (resG.1 (out jf)).2 = true := by
     rw [hres_eq]
     simp [wires0, hnotn, hfval.2]
   rw [hwv]
   cases hvj : α (Sum.inl (Sum.inr jf))
   · rfl
   · have hbad := hc2 h2 (by simp [lEv, hvj])
     rw [hex] at hbad; cases hbad

lemma bbr_ss (n t h' D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H_row : Fin h' → Fin n → Bool) (wRow : Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D) :
   ∀ (m s : ℕ) (_ : 2 ^ h' - s = m) (arr : Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (α : Sum (Fin n ⊕ Fin t) ℕ → Bool) (sf : Fin (2 ^ h')),
     s ≤ sf.val →
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ i s' b, VL st.1 (wRow i s' b)) →
     (∀ C ∈ (bbr n t h' D gates out H_row wRow fd s arr st).2.2, ClauseSat α C) →
     (lEv α fd.1 = false ∧ lEv α fd.2 = true) →
     lEv α ((bbr n t h' D gates out H_row wRow fd s arr st).1 sf).excl = false →
     ∀ j : Fin t, α (Sum.inl (Sum.inr j)) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => α (Sum.inl (Sum.inl i))))).getD (out j) false
 | 0, s, hm, _, _, _, sf, hsf, _, _, _, _, _, _, _ => by exfalso; omega
 | m + 1, s, hm, arr, st, α, sf, hsf, hst, hf1, hf2, hw, hsat, hfval, hex => by
   have hs : s < 2 ^ h' := by omega
   have hm1 : 2 ^ h' - (s + 1) = m := by omega
   unfold bbr at hsat hex
   simp only [hs, ↓reduceDIte] at hsat hex
   set sf0 : Fin (2 ^ h') := ⟨s, hs⟩
   obtain ⟨hst1, hle1, _, _, _, _, _, _⟩ :=
     bb_pr n t h' D gates out H_row (fun i => wRow i sf0) fd sf0 st hst hf1 hf2 (fun i b => hw i sf0 b)
   set br := bb n t h' D gates out H_row (fun i => wRow i sf0) fd sf0 st
   let arr' : Fin (2 ^ h') → BR n t := fun s' => if s' = sf0 then br else arr s'
   by_cases heq : s = sf.val
   · have hsfeq : sf = sf0 := Fin.ext heq.symm
     rw [hsfeq] at hex
     rw [bbr_uc n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut sf0 (by omega)] at hex
     dsimp only [arr'] at hex
     simp only [↓reduceIte] at hex
     have hsat_br : ∀ C ∈ br.stOut.2, ClauseSat α C := fun C hC =>
       hsat C (bbr_cm n t h' D gates out H_row wRow fd m (s + 1) hm1 arr' br.stOut C hC)
     exact bb_ss n t h' D gates out H_row (fun i => wRow i sf0) fd sf0 st α
       hst hf1 hf2 (fun i b => hw i sf0 b) hsat_br hfval hex hD_bound
   · exact bbr_ss n t h' D gates out H_row wRow fd hD_bound m (s + 1) hm1
       arr' br.stOut α sf (by omega) hst1 (hf1.mono hle1) (hf2.mono hle1) (fun i s' b => (hw i s' b).mono hle1)
       hsat hfval hex

lemma bab_ss (n t h' R D : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (H : Fin R → Fin h' → Fin n → Bool) (wMat : Fin R → Fin n → Fin (2 ^ h') → Bool → LN (Fin n ⊕ Fin t))
   (fd : LN (Fin n ⊕ Fin t) × LN (Fin n ⊕ Fin t))
   (hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D) :
   ∀ (m r : ℕ) (_ : R - r = m) (arr : Fin R → Fin (2 ^ h') → BR n t) (st : St (Fin n ⊕ Fin t))
     (α : Sum (Fin n ⊕ Fin t) ℕ → Bool) (rf : Fin R) (sf : Fin (2 ^ h')),
     r ≤ rf.val →
     VS st →
     VL st.1 fd.1 → VL st.1 fd.2 →
     (∀ rf' i s' b, VL st.1 (wMat rf' i s' b)) →
     (∀ C ∈ (bab n t h' R D gates out H wMat fd r arr st).2.2, ClauseSat α C) →
     (lEv α fd.1 = false ∧ lEv α fd.2 = true) →
     lEv α ((bab n t h' R D gates out H wMat fd r arr st).1 rf sf).excl = false →
     ∀ j : Fin t, α (Sum.inl (Sum.inr j)) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => α (Sum.inl (Sum.inl i))))).getD (out j) false
 | 0, r, hm, _, _, _, rf, _, hrf, _, _, _, _, _, _, _ => by exfalso; omega
 | m + 1, r, hm, arr, st, α, rf, sf, hrf, hst, hf1, hf2, hw, hsat, hfval, hex => by
   have hr : r < R := by omega
   have hm1 : R - (r + 1) = m := by omega
   unfold bab at hsat hex
   simp only [hr, ↓reduceDIte] at hsat hex
   set rf0 : Fin R := ⟨r, hr⟩
   let dummyRow : Fin (2 ^ h') → BR n t := fun _ => ⟨fd.1, fun _ => fd, fun _ => fd, st⟩
   obtain ⟨hst1, hle1, _, _, _, _⟩ :=
     bbr_pr n t h' D gates out (H rf0) (wMat rf0) fd (2 ^ h') 0 (Nat.sub_zero _)
       dummyRow st hst hf1 hf2 (fun i s' b => hw rf0 i s' b) (fun sf' hsf' => by exfalso; omega)
   set rowRes := bbr n t h' D gates out (H rf0) (wMat rf0) fd 0 dummyRow st
   let arr' : Fin R → Fin (2 ^ h') → BR n t := fun r' => if r' = rf0 then rowRes.1 else arr r'
   by_cases heq : r = rf.val
   · have hrfeq : rf = rf0 := Fin.ext heq.symm
     rw [hrfeq] at hex
     rw [bab_uc n t h' R D gates out H wMat fd m (r + 1) hm1 arr' rowRes.2 rf0 (by omega)] at hex
     dsimp only [arr'] at hex
     simp only [↓reduceIte] at hex
     have hsat_row : ∀ C ∈ rowRes.2.2, ClauseSat α C := fun C hC =>
       hsat C (bab_cm n t h' R D gates out H wMat fd m (r + 1) hm1 arr' rowRes.2 C hC)
     exact bbr_ss n t h' D gates out (H rf0) (wMat rf0) fd hD_bound (2 ^ h') 0
       (Nat.sub_zero _) dummyRow st α sf (Nat.zero_le _) hst hf1 hf2 (fun i s' b => hw rf0 i s' b)
       hsat_row hfval hex
   · exact bab_ss n t h' R D gates out H wMat fd hD_bound m (r + 1) hm1
       arr' rowRes.2 α rf sf (by omega) hst1 (hf1.mono hle1) (hf2.mono hle1)
       (fun rf' i s' b => (hw rf' i s' b).mono hle1) hsat hfval hex

def bitsToNatGo : ℕ → (ℕ → Bool) → ℕ
 | 0, _ => 0
 | d + 1, f => if f d then setBit1 (bitsToNatGo d f) d else bitsToNatGo d f

lemma bitsToNatGo_lt (f : ℕ → Bool) : ∀ d : ℕ, bitsToNatGo d f < 2 ^ d
 | 0 => by simp [bitsToNatGo]
 | d + 1 => by
   have ih := bitsToNatGo_lt f d
   simp only [bitsToNatGo]
   split_ifs
   · exact setBit1_lt (lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))) (by omega)
   · exact lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))

lemma testBit_bitsToNatGo (f : ℕ → Bool) : ∀ d q : ℕ,
   (bitsToNatGo d f).testBit q = if q < d then f q else false
 | 0, q => by simp [bitsToNatGo]
 | d + 1, q => by
   have ih := testBit_bitsToNatGo f d q
   simp only [bitsToNatGo]
   by_cases hfd : f d = true
   · simp only [hfd, ↓reduceIte, testBit_setBit1, ih]
     by_cases hqd : q = d
     · subst hqd; simp [hfd]
     · simp [hqd, show q < d + 1 ↔ q < d by omega]
   · have hfd' : f d = false := Bool.eq_false_iff.2 hfd
     simp only [hfd, Bool.false_eq_true, ↓reduceIte, ih]
     by_cases hqd : q = d
     · subst hqd; simp [hfd']
     · simp [hqd, show q < d + 1 ↔ q < d by omega]

def bitsToFin {h' : ℕ} (f : Fin h' → Bool) : Fin (2 ^ h') :=
 ⟨bitsToNatGo h' (fun q => if h : q < h' then f ⟨q, h⟩ else false), bitsToNatGo_lt _ h'⟩

lemma testBit_bitsToFin {h' : ℕ} (f : Fin h' → Bool) (q : Fin h') :
   (bitsToFin f).val.testBit q.val = f q := by
 simp only [bitsToFin, testBit_bitsToNatGo, q.isLt, ↓reduceIte, ↓reduceDIte]

lemma size_bound_core (n t g h h' R T_int m clF H1 L1 P S : ℕ)
   (hh'h : h' ≤ h) (hR1 : 1 ≤ R)
   (hR_le : R ≤ 3 * H1 * L1)
   (hpow_le : 2 ^ h' ≤ P)
   (hH1_eq : H1 = h + 1)
   (hL1_pos : 1 ≤ L1)
   (hP_pos : 1 ≤ P)
   (hS_eq : S = n + t + g + 1)
   (hTn_int : T_int ≤ n)
   (hm_le : m ≤ (1 + n) +
     (6 * T_int * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
     ((1 + 2 * n + 4 * n * h' + 2 * g) * 2 ^ h') * R +
     (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
     2 * R * 2 ^ h' + 2 * R)
   (hcl_le : clF ≤ (1 + 2 * n) +
     (21 * T_int * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R +
     ((5 * n + (8 * n + 1) * h' + 5 * g + 2 * t) * 2 ^ h') * R +
     (18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t +
     6 * R * 2 ^ h' + 6 * R + 1) :
   m + 3 * clF ≤ 262144 * S * H1 ^ 2 * L1 * P := by
 have hpow_pos : 1 ≤ 2 ^ h' := Nat.one_le_two_pow
 have hH1_pos : 1 ≤ H1 := by omega
 have hS_pos : 1 ≤ S := by omega
 have hb_base : (1 + n) + 3 * (1 + 2 * n) ≤ 7 * S * H1 ^ 2 * L1 * P := by
   have h7 : (1 + n) + 3 * (1 + 2 * n) ≤ 7 * S := by omega
   have h1 : 1 ≤ H1 ^ 2 * L1 * P :=
     Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hH1_pos) hL1_pos) hP_pos
   calc (1 + n) + 3 * (1 + 2 * n) ≤ 7 * S := h7
     _ ≤ 7 * S * (H1 ^ 2 * L1 * P) := Nat.le_mul_of_pos_right _ h1
     _ = 7 * S * H1 ^ 2 * L1 * P := by ring
 have hb_mat : (6 * T_int * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
     3 * ((21 * T_int * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R) ≤
     255 * S * H1 ^ 2 * L1 * P := by
   have hT : 6 * T_int * 2 ^ h' ≤ 6 * n * 2 ^ h' :=
     Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hTn_int)
   have hT2 : 21 * T_int * 2 ^ h' ≤ 21 * n * 2 ^ h' :=
     Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hTn_int)
   have h1 : (85 + 14 * h') * n ≤ 85 * S * H1 := by
     have h1a : 85 + 14 * h' ≤ 85 * H1 := by omega
     have h1b : n ≤ S := by omega
     calc (85 + 14 * h') * n ≤ (85 * H1) * S := Nat.mul_le_mul h1a h1b
       _ = 85 * S * H1 := by ring
   have h2 : 2 ^ h' * R ≤ 3 * H1 * L1 * P := by
     calc 2 ^ h' * R ≤ P * (3 * H1 * L1) := Nat.mul_le_mul hpow_le hR_le
       _ = 3 * H1 * L1 * P := by ring
   calc (6 * T_int * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
         3 * ((21 * T_int * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R)
     _ ≤ (6 * n * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
         3 * ((21 * n * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R) := by nlinarith
     _ = ((85 + 14 * h') * n) * (2 ^ h' * R) := by ring
     _ ≤ (85 * S * H1) * (3 * H1 * L1 * P) := Nat.mul_le_mul h1 h2
     _ = 255 * S * H1 ^ 2 * L1 * P := by ring
 have hb_br : ((1 + 2 * n + 4 * n * h' + 2 * g) * 2 ^ h') * R +
     3 * (((5 * n + (8 * n + 1) * h' + 5 * g + 2 * t) * 2 ^ h') * R) ≤
     84 * S * H1 ^ 2 * L1 * P := by
   have h1 : 1 + 17 * n + 6 * t + 17 * g + (28 * n + 3) * h' ≤ 28 * S * H1 := by
     have h1a : 1 + 17 * n + 6 * t + 17 * g ≤ 28 * S := by omega
     have h1b : (28 * n + 3) * h' ≤ 28 * S * h := by
       have : 28 * n + 3 ≤ 28 * S := by omega
       exact Nat.mul_le_mul this hh'h
     calc 1 + 17 * n + 6 * t + 17 * g + (28 * n + 3) * h'
       _ ≤ 28 * S + 28 * S * h := Nat.add_le_add h1a h1b
       _ = 28 * S * H1 := by rw [hH1_eq]; ring
   have h2 : 2 ^ h' * R ≤ 3 * H1 * L1 * P := by
     calc 2 ^ h' * R ≤ P * (3 * H1 * L1) := Nat.mul_le_mul hpow_le hR_le
       _ = 3 * H1 * L1 * P := by ring
   calc ((1 + 2 * n + 4 * n * h' + 2 * g) * 2 ^ h') * R +
       3 * (((5 * n + (8 * n + 1) * h' + 5 * g + 2 * t) * 2 ^ h') * R)
     _ = (1 + 17 * n + 6 * t + 17 * g + (28 * n + 3) * h') * (2 ^ h' * R) := by ring
     _ ≤ (28 * S * H1) * (3 * H1 * L1 * P) := Nat.mul_le_mul h1 h2
     _ = 84 * S * H1 ^ 2 * L1 * P := by ring
 have hb_cons : (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
     3 * ((18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t) ≤
     318 * S * H1 ^ 2 * L1 * P := by
   have h1 : 60 * R * 2 ^ h' + 40 * R + 6 ≤ 106 * R * 2 ^ h' := by
     have ha : R ≤ R * 2 ^ h' := Nat.le_mul_of_pos_right R hpow_pos
     have hb : 1 ≤ R * 2 ^ h' := Nat.mul_pos hR1 hpow_pos
     nlinarith
   have h2 : 106 * R * 2 ^ h' ≤ 318 * H1 * L1 * P := by
     calc 106 * R * 2 ^ h' ≤ 106 * (3 * H1 * L1) * P :=
         Nat.mul_le_mul (Nat.mul_le_mul_left 106 hR_le) hpow_le
       _ = 318 * H1 * L1 * P := by ring
   have hnt : n + t ≤ S := by omega
   have hH1_le : 318 * H1 * L1 * P ≤ 318 * H1 ^ 2 * L1 * P := by
     have hsq : H1 ≤ H1 ^ 2 := by nlinarith
     calc 318 * H1 * L1 * P
       _ = 318 * (H1 * (L1 * P)) := by ring
       _ ≤ 318 * (H1 ^ 2 * (L1 * P)) := Nat.mul_le_mul_left 318 (Nat.mul_le_mul_right _ hsq)
       _ = 318 * H1 ^ 2 * L1 * P := by ring
   calc (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
         3 * ((18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t)
     _ = (60 * R * 2 ^ h' + 40 * R + 6) * (n + t) := by ring
     _ ≤ (106 * R * 2 ^ h') * S := Nat.mul_le_mul h1 hnt
     _ ≤ (318 * H1 ^ 2 * L1 * P) * S := Nat.mul_le_mul_right S (le_trans h2 hH1_le)
     _ = 318 * S * H1 ^ 2 * L1 * P := by ring
 have hb_conf : (2 * R * 2 ^ h' + 2 * R) + 3 * (6 * R * 2 ^ h' + 6 * R + 1) ≤
     129 * S * H1 ^ 2 * L1 * P := by
   have h1 : (2 * R * 2 ^ h' + 2 * R) + 3 * (6 * R * 2 ^ h' + 6 * R + 1) ≤ 43 * R * 2 ^ h' := by
     have ha : R ≤ R * 2 ^ h' := Nat.le_mul_of_pos_right R hpow_pos
     have hb : 1 ≤ R * 2 ^ h' := Nat.mul_pos hR1 hpow_pos
     nlinarith
   have h2 : 43 * R * 2 ^ h' ≤ 129 * H1 * L1 * P := by
     calc 43 * R * 2 ^ h' ≤ 43 * (3 * H1 * L1) * P :=
         Nat.mul_le_mul (Nat.mul_le_mul_left 43 hR_le) hpow_le
       _ = 129 * H1 * L1 * P := by ring
   have hmul : 129 * H1 * L1 * P ≤ 129 * S * H1 ^ 2 * L1 * P := by
     have hSH : 1 ≤ S * H1 := Nat.mul_pos hS_pos hH1_pos
     calc 129 * H1 * L1 * P ≤ (129 * H1 * L1 * P) * (S * H1) := Nat.le_mul_of_pos_right _ hSH
       _ = 129 * S * H1 ^ 2 * L1 * P := by ring
   exact le_trans h1 (le_trans h2 hmul)
 calc m + 3 * clF
   _ ≤ ((1 + n) + 3 * (1 + 2 * n)) +
       ((6 * T_int * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
         3 * ((21 * T_int * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R)) +
       (((1 + 2 * n + 4 * n * h' + 2 * g) * 2 ^ h') * R +
         3 * (((5 * n + (8 * n + 1) * h' + 5 * g + 2 * t) * 2 ^ h') * R)) +
       ((6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
         3 * ((18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t)) +
       ((2 * R * 2 ^ h' + 2 * R) + 3 * (6 * R * 2 ^ h' + 6 * R + 1)) := by omega
   _ ≤ 7 * S * H1 ^ 2 * L1 * P + 255 * S * H1 ^ 2 * L1 * P + 84 * S * H1 ^ 2 * L1 * P +
       318 * S * H1 ^ 2 * L1 * P + 129 * S * H1 ^ 2 * L1 * P := by
       exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hb_base hb_mat) hb_br) hb_cons) hb_conf
   _ = 793 * S * H1 ^ 2 * L1 * P := by ring
   _ ≤ 262144 * S * H1 ^ 2 * L1 * P := by
       exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))))

lemma size_bound_aux (n t g h h' R T_int m clF : ℕ)
   (hh'h : h' ≤ h) (hR1 : 1 ≤ R)
   (hRbd : R ≤ 3 * (h' + 1) * (Nat.clog 2 (n + 1) + 1))
   (hTn_int : T_int ≤ n)
   (hm_le : m ≤ (1 + n) +
     (6 * T_int * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
     ((1 + 2 * n + 4 * n * h' + 2 * g) * 2 ^ h') * R +
     (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
     2 * R * 2 ^ h' + 2 * R)
   (hcl_le : clF ≤ (1 + 2 * n) +
     (21 * T_int * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R +
     ((5 * n + (8 * n + 1) * h' + 5 * g + 2 * t) * 2 ^ h') * R +
     (18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t +
     6 * R * 2 ^ h' + 6 * R + 1) :
   m + 3 * clF ≤ 262144 * (n + t + g + 1) * (h + 1) ^ 2 * (Nat.clog 2 (n + 1) + 1) * 2 ^ h :=
 size_bound_core n t g h h' R T_int m clF (h + 1) (Nat.clog 2 (n + 1) + 1) (2 ^ h) (n + t + g + 1)
   hh'h hR1 (le_trans hRbd (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))))
   (Nat.pow_le_pow_right (by omega) hh'h) rfl (by omega) Nat.one_le_two_pow rfl hTn_int hm_le hcl_le

lemma upper_bound_hpos (n t h : ℕ) (gates : List BinaryGate) (out : Fin t → ℕ)
   (hh : 1 ≤ h) (hn : 1 ≤ n) :
   let V := Fin n ⊕ Fin t
   let circuit : BinaryCircuit := ⟨gates, 0⟩
   let agrees := fun (v : V → Bool) =>
     let wires := circuit.wires (List.ofFn (fun i : Fin n => v (Sum.inl i)))
     ∀ j : Fin t, v (Sum.inr j) = wires.getD (out j) false
   let depths := gates.foldl (fun (w : List ℕ) g =>
     w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
   let D := (Finset.univ : Finset (Fin t)).sup (fun j => depths.getD (out j) 0)
   let rounds := 128*(D+h+Nat.clog 2 (n+t+1)+1)
   ∃ (m : ℕ) (F : Finset (Clause (Sum V (Fin m)))),
     m + (∑ C ∈ F, C.card) ≤ 262144*(n+t+gates.length+1)*(h+1)^2*(Nat.clog 2 (n+1)+1)*2^h ∧
     (∀ C ∈ F, C.card ≤ 3) ∧
     (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
       Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
     ∀ ρ : V → Option Bool,
       (Finset.univ.filter (fun i : Fin n => ρ (Sum.inl i) = none)).card ≤ h →
       let seed : Set (Literal (Sum V (Fin m))) :=
         {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
       let advance := fun S : Set (Literal (Sum V (Fin m))) =>
         S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
           negL other ∈ S}
       let known := (advance^[rounds]) seed
       let complete := fun v : V → Bool => agrees v ∧
         ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
       ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, negL l ∈ known) ∧
       ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
         (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known) := by
 classical
 let V := Fin n ⊕ Fin t
 let depths := gates.foldl (fun (w : List ℕ) g =>
   w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
 let D := (Finset.univ : Finset (Fin t)).sup (fun j => depths.getD (out j) 0)
 have hD_eq : ∀ u : ℕ, depths.getD u 0 = dv n gates u :=
   (depths_length_and_getD n gates).2
 have hD_bound : ∀ j : Fin t, dv n gates (out j) ≤ D := by
   intro j
   rw [← hD_eq (out j)]
   exact Finset.le_sup (f := fun j' : Fin t => depths.getD (out j') 0) (Finset.mem_univ j)
 let h' : ℕ := min h n
 have hh'1 : 1 ≤ h' := le_min hh hn
 have hh'h : h' ≤ h := min_le_left h n
 have hh'n : h' ≤ n := min_le_right h n
 obtain ⟨R, H, hR1, hRbd, hcov⟩ := exists_mat_family n h' hh'1 hh'n
 let T_n : BTree (Fin n) := BTree.ofList (List.finRange n) (list_finRange_ne_nil n hn)
 have hTn_leaves : T_n.leaves = List.finRange n := BTree.leaves_ofList _ _
 have hTn_nd : T_n.leaves.Nodup := by rw [hTn_leaves]; exact List.nodup_finRange n
 have hTn_sub : ∀ j : Fin n, j ∈ T_n.leaves := fun j => by rw [hTn_leaves]; exact List.mem_finRange j
 have hTn_depth : T_n.depth ≤ Nat.clog 2 (n + 1) := by
   have h1 := BTree.depth_ofList (List.finRange n) (list_finRange_ne_nil n hn)
   change T_n.depth ≤ Nat.clog 2 (List.finRange n).length at h1
   rw [List.length_finRange] at h1
   exact le_trans h1 (Nat.clog_mono_right 2 (by omega))
 have hTn_int : T_n.intNodes ≤ n := by
   have h1 := T_n.intNodes_add_one
   rw [hTn_leaves, List.length_finRange] at h1
   omega
 let tL : LN V := (Sum.inr 0, true)
 let fL : LN V := (Sum.inr 0, false)
 let fd : LN V × LN V := (fL, tL)
 let kL : Fin n → LN V := fun i => (Sum.inr (1 + i.val), true)
 let xLit : Fin n → LN V := fun i => (Sum.inl (Sum.inl i), true)
 let stBase : St V := eu tL (1 + n, [])
 let st0 : St V := bki n t kL 0 stBase
 have hstBase : VS stBase := validSt_emitUnit (fun _ h => by simp at h)
   (fun k hk => by simp [tL] at hk ⊢; omega)
 have hkBase : ∀ j : Fin n, VL stBase.1 (kL j) := fun j k hk => by
   simp only [kL, Sum.inr.injEq] at hk
   change k < 1 + n
   omega
 obtain ⟨hst0, h0_1, h0_len, h0_sub, _⟩ :=
   bki_pr n t kL n 0 (Nat.sub_zero _) stBase hstBase hkBase
 have hT0 : VL st0.1 tL := fun k hk => by
   rw [h0_1]; simp only [tL, Sum.inr.injEq] at hk; change k < 1 + n; omega
 have hF0 : VL st0.1 fL := fun k hk => by
   rw [h0_1]; simp only [fL, Sum.inr.injEq] at hk; change k < 1 + n; omega
 have hkx0 : ∀ i, VL st0.1 (kL i) ∧ VL st0.1 (xLit i) := fun i =>
   ⟨by rw [h0_1]; exact hkBase i, validLit_inl _ _ _⟩
 let dummyW : Fin R → Fin n → Fin (2 ^ h') → Bool → LN V := fun _ _ _ _ => tL
 let matsRes := bam n h' R H kL xLit tL fL T_n 0 dummyW st0
 obtain ⟨hstM, hleM, hmM_v, hlM_c, hsubM, hwM⟩ :=
   bam_pr n h' R H kL xLit tL fL T_n R 0 (Nat.sub_zero _) dummyW st0
     hst0 hT0 hF0 hkx0 (fun rf h => by exfalso; omega)
 let dummyBr : Fin R → Fin (2 ^ h') → BR n t := fun _ _ => ⟨fd.1, fun _ => fd, fun _ => fd, matsRes.2⟩
 let brRes := bab n t h' R D gates out H matsRes.1 fd 0 dummyBr matsRes.2
 obtain ⟨hstB, hleB, hmB_v, hlB_c, hsubB, hbrB⟩ :=
   bab_pr n t h' R D gates out H matsRes.1 fd R 0 (Nat.sub_zero _) dummyBr matsRes.2
     hstM (hF0.mono hleM) (hT0.mono hleM) (fun rf i s' b => hwM rf i s' b) (fun rf h => by exfalso; omega)
 let exclGrid : Fin R → Fin (2 ^ h') → LN V := fun r s => (brRes.1 r s).excl
 let consInlSt := bci n t h' R hR1 exclGrid brRes.1 0 brRes.2
 obtain ⟨hstInl, hleInl, hmInl_v, hlInl_c, hsubInl⟩ :=
   bci_pr n t h' R hR1 exclGrid brRes.1 n 0 (Nat.sub_zero _) brRes.2
     hstB (fun r s => (hbrB r s).1) (fun r s i => (hbrB r s).2.1 i)
 let consInrSt := bcr n t h' R hR1 out exclGrid brRes.1 0 consInlSt
 obtain ⟨hstInr, hleInr, hmInr_v, hlInr_c, hsubInr⟩ :=
   bcr_pr n t h' R hR1 out exclGrid brRes.1 t 0 (Nat.sub_zero _) consInlSt
     hstInl (fun r s => ((hbrB r s).1).mono hleInl)
     (fun r s j => ⟨((hbrB r s).2.2 (out j)).1.mono hleInl, ((hbrB r s).2.2 (out j)).2.mono hleInl⟩)
 let confGrid := baog R (2 ^ h') hR1 Nat.one_le_two_pow exclGrid consInrSt
 obtain ⟨hstC, hleC, hmC_v, hlC_c, hsubC, hvC⟩ :=
   baog_pr R (2 ^ h') hR1 Nat.one_le_two_pow exclGrid consInrSt hstInr
     (fun r s => ((hbrB r s).1).mono (le_trans hleInl hleInr))
 let stFinal : St V := eu (negL confGrid.1) confGrid.2
 have hstFinal : VS stFinal := validSt_emitUnit hstC (validLit_negL.2 hvC)
 let m : ℕ := stFinal.1
 have hm : 0 < m := by
   have h01 : st0.1 = 1 + n := h0_1
   have hm_eq : m = confGrid.2.1 := rfl
   have hle_all : st0.1 ≤ confGrid.2.1 :=
     le_trans hleM (le_trans hleB (le_trans hleInl (le_trans hleInr hleC)))
   omega
 let Fnat : Finset (CN V) := stFinal.2.toFinset
 let Lfin : List (Cl (Sum V (Fin m))) := stFinal.2.map (mapCl m hm)
 let Ffin : Finset (Cl (Sum V (Fin m))) := Lfin.toFinset
 have hImgF : ∀ C ∈ Fnat, mapCl m hm C ∈ Ffin := fun C hC =>
   List.mem_toFinset.2 (List.mem_map.2 ⟨C, List.mem_toFinset.1 hC, rfl⟩)
 have hcard3 : ∀ C ∈ Ffin, C.card ≤ 3 := by
   intro C hC
   rcases List.mem_map.1 (List.mem_toFinset.1 hC) with ⟨C', hC', rfl⟩
   exact (mapCl_card_le m hm C').trans (hstFinal C' hC').1
 have hFnat_sub : ∀ C ∈ stFinal.2, C ∈ Fnat := fun C hC => List.mem_toFinset.2 hC
 have hConf_sub : ∀ C ∈ confGrid.2.2, C ∈ stFinal.2 := fun C hC => by
   simp only [stFinal, eu, addCl, List.mem_cons]; exact Or.inr hC
 have hInr_sub : ∀ C ∈ consInrSt.2, C ∈ confGrid.2.2 := fun C hC => hsubC C hC
 have hInl_sub : ∀ C ∈ consInlSt.2, C ∈ consInrSt.2 := fun C hC => hsubInr C hC
 have hBr_sub : ∀ C ∈ brRes.2.2, C ∈ consInlSt.2 := fun C hC => hsubInl C hC
 have hMat_sub : ∀ C ∈ matsRes.2.2, C ∈ brRes.2.2 := fun C hC => hsubB C hC
 have h0_sub' : ∀ C ∈ st0.2, C ∈ matsRes.2.2 := fun C hC => hsubM C hC
 have hsat_nat : ∀ v : V → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) ↔
     ∃ aux : ℕ → Bool, ∀ C ∈ stFinal.2, ClauseSat (Sum.elim v aux) C := by
   intro v
   constructor
   · intro hag
     let α0 : Sum V ℕ → Bool := Sum.elim v (fun _ => true)
     have hα0_base : ∀ C ∈ stBase.2, ClauseSat α0 C := by
       intro C hC
       simp only [stBase, eu, addCl, List.mem_singleton] at hC
       subst hC
       rw [clauseSat_singleton]
       rfl
     have hα0_sat0 : ∀ C ∈ st0.2, ClauseSat α0 C :=
       bki_sat n t kL α0 n 0 (Nat.sub_zero _) stBase hα0_base (fun _ => rfl)
     have hα0_T : lEv α0 tL = true := rfl
     have hα0_F : lEv α0 fL = false := rfl
     have hα0_K : ∀ i, lEv α0 (kL i) = true := fun _ => rfl
     obtain ⟨α1, h1inl, h1lt, h1sat, h1mat⟩ :=
       bam_sat n h' R H kL xLit tL fL T_n hTn_nd hTn_sub R 0 (Nat.sub_zero _)
         dummyW st0 α0 hst0 hT0 hF0 hkx0 (fun rf h => by exfalso; omega) hα0_sat0 hα0_T hα0_F hα0_K
     have hfval1 : lEv α1 fd.1 = false ∧ lEv α1 fd.2 = true :=
       ⟨(lecl h1inl h1lt hF0).trans hα0_F, (lecl h1inl h1lt hT0).trans hα0_T⟩
     have hww1 : ∀ rf : Fin R, ∀ sf : Fin (2 ^ h'), (∀ q : Fin h', sf.val.testBit q.val =
         xl (((List.finRange n).filter (fun i => H rf q i)).map (fun i => α1 (Sum.inl (Sum.inl i))))) →
         ∀ i b, lEv α1 (matsRes.1 rf i sf b) = true → α1 (Sum.inl (Sum.inl i)) = b := by
       intro rf sf hsyn i b hwb
       have h1 := h1mat rf (Nat.zero_le _) i sf b
       rw [h1, decide_eq_true_iff] at hwb
       rcases hwb with ⟨c, hSci, hceq⟩
       have hsyn' : ∀ q : Fin h', sf.val.testBit q.val =
           xl (((List.finRange n).filter (fun j => H rf q j)).map (fun j => α1 (Sum.inl (Sum.inl j)))) := hsyn
       have hid := syndrome_parity_id (H rf) c sf (fun j => α1 (Sum.inl (Sum.inl j))) i hsyn' hSci
       have hcongr_fn : ∀ q : Fin n,
           (if xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q)) then
             lEv α0 (xLit q) else false) =
           (if xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q)) then
             α1 (Sum.inl (Sum.inl q)) else false) := by
         intro q; simp [xLit, lEv, α0, h1inl]
       have hcongr : xl ((T_n.leaves.filter (· ≠ i)).map (fun q =>
           if xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H rf p q)) then
             lEv α0 (xLit q) else false)) =
           xl (((List.finRange n).filter (· ≠ i)).map (fun j =>
             if xl (List.ofFn (fun q : Fin h' => decide (c.val.testBit q.val) && H rf q j)) then
               α1 (Sum.inl (Sum.inl j)) else false)) := by
         rw [hTn_leaves]
         congr 1
         exact List.map_congr_left fun q _ => hcongr_fn q
       dsimp only at hceq
       rw [hcongr] at hceq
       rw [hid] at hceq
       exact hceq
     have hag1 : ∀ j : Fin t, α1 (Sum.inl (Sum.inr j)) =
         ((⟨gates, 0⟩ : BinaryCircuit).wires
           (List.ofFn (fun i : Fin n => α1 (Sum.inl (Sum.inl i))))).getD (out j) false := by
       intro j
       have h1j : α1 (Sum.inl (Sum.inr j)) = v (Sum.inr j) := h1inl (Sum.inr j)
       rw [h1j, hag j]
       congr 2
       exact congrArg List.ofFn (funext fun i => (h1inl (Sum.inl i)).symm)
     obtain ⟨α2, h2inl, h2lt, h2sat, h2br⟩ :=
       bab_sat n t h' R D gates out H matsRes.1 fd hD_bound R 0 (Nat.sub_zero _)
         dummyBr matsRes.2 α1 hstM (hF0.mono hleM) (hT0.mono hleM) hwM
         (fun rf h => by exfalso; omega) h1sat hfval1 hww1 hag1
     have hgood2 : ∀ r : Fin R, ∃ s : Fin (2 ^ h'),
         lEv α2 (exclGrid r s) = false ∧
         ∀ i : Fin n, lEv α2 ((brRes.1 r s).xDual i).1 = α2 (Sum.inl (Sum.inl i)) ∧
                     lEv α2 ((brRes.1 r s).xDual i).2 = !(α2 (Sum.inl (Sum.inl i))) := by
       intro r
       let x2 : Fin n → Bool := fun i => α2 (Sum.inl (Sum.inl i))
       let s := bitsToFin (fun q : Fin h' => xl (((List.finRange n).filter (fun i => H r q i)).map x2))
       have hsyn : ∀ q : Fin h', s.val.testBit q.val =
           xl (((List.finRange n).filter (fun i => H r q i)).map x2) :=
         testBit_bitsToFin _
       have hbr := h2br r (Nat.zero_le _) s
       have hex_false : lEv α2 (brRes.1 r s).excl = false := by
         rw [hbr.1, decide_eq_false_iff_not]; push Not; intro q
         rw [hsyn q]; congr 1; exact List.map_congr_left fun i _ => h2inl (Sum.inl i)
       obtain ⟨hx_eq, _⟩ := hbr.2 hex_false
       refine ⟨s, hex_false, fun i => ?_⟩
       rw [h2inl (Sum.inl i)]
       exact hx_eq i
     obtain ⟨α3, h3inl, h3lt, h3sat⟩ :=
       bci_sat n t h' R hR1 exclGrid brRes.1 n 0 (Nat.sub_zero _) brRes.2 α2
         hstB (fun r s => (hbrB r s).1) (fun r s i => (hbrB r s).2.1 i) h2sat hgood2
     have hgood3 : ∀ r : Fin R, ∃ s : Fin (2 ^ h'),
         lEv α3 (exclGrid r s) = false ∧
         ∀ j : Fin t, lEv α3 ((brRes.1 r s).wiresOut (out j)).1 = α3 (Sum.inl (Sum.inr j)) ∧
                     lEv α3 ((brRes.1 r s).wiresOut (out j)).2 = !(α3 (Sum.inl (Sum.inr j))) := by
       intro r
       let x2 : Fin n → Bool := fun i => α2 (Sum.inl (Sum.inl i))
       let s := bitsToFin (fun q : Fin h' => xl (((List.finRange n).filter (fun i => H r q i)).map x2))
       have hsyn : ∀ q : Fin h', s.val.testBit q.val =
           xl (((List.finRange n).filter (fun i => H r q i)).map x2) :=
         testBit_bitsToFin _
       have hbr := h2br r (Nat.zero_le _) s
       have hex_false2 : lEv α2 (brRes.1 r s).excl = false := by
         rw [hbr.1, decide_eq_false_iff_not]; push Not; intro q
         rw [hsyn q]; congr 1; exact List.map_congr_left fun i _ => h2inl (Sum.inl i)
       obtain ⟨_, hw_eq⟩ := hbr.2 hex_false2
       refine ⟨s, (lecl h3inl h3lt (hbrB r s).1).trans hex_false2, fun j => ?_⟩
       rw [lecl h3inl h3lt ((hbrB r s).2.2 (out j)).1,
           lecl h3inl h3lt ((hbrB r s).2.2 (out j)).2, h3inl (Sum.inr j), h2inl (Sum.inr j)]
       exact hw_eq j
     obtain ⟨α4, h4inl, h4lt, h4sat⟩ :=
       bcr_sat n t h' R hR1 out exclGrid brRes.1 t 0 (Nat.sub_zero _) consInlSt α3
         hstInl (fun r s => ((hbrB r s).1).mono hleInl)
         (fun r s j => ⟨((hbrB r s).2.2 (out j)).1.mono hleInl, ((hbrB r s).2.2 (out j)).2.mono hleInl⟩)
         h3sat hgood3
     obtain ⟨α5, h5inl, h5lt, h5sat, h5grid⟩ :=
       baog_sa R (2 ^ h') hR1 Nat.one_le_two_pow exclGrid consInrSt α4
         hstInr (fun r s => ((hbrB r s).1).mono (le_trans hleInl hleInr)) h4sat
     have hgrid_false : lEv α5 confGrid.1 = false := by
       rw [h5grid, decide_eq_false_iff_not]
       rintro ⟨r, hrs⟩
       obtain ⟨s, hes, _⟩ := hgood3 r
       have h4eq : lEv α4 (exclGrid r s) = lEv α3 (exclGrid r s) :=
         lecl h4inl h4lt (((hbrB r s).1).mono hleInl)
       have hbad := hrs s
       rw [h4eq, hes] at hbad
       cases hbad
     have hsatFinal : ∀ C ∈ stFinal.2, ClauseSat α5 C := by
       intro C hC
       simp only [stFinal, eu, addCl, List.mem_cons] at hC
       rcases hC with rfl | hCg
       · rw [clauseSat_singleton, litEval_negL, hgrid_false]; rfl
       · exact h5sat C hCg
     refine ⟨fun k => α5 (Sum.inr k), fun C hC => ?_⟩
     have heq : Sum.elim v (fun k => α5 (Sum.inr k)) = α5 := by
       ext z
       cases z with
       | inl u =>
         exact ((h5inl u).trans ((h4inl u).trans ((h3inl u).trans ((h2inl u).trans (h1inl u))))).symm
       | inr k => rfl
     rw [heq]
     exact hsatFinal C hC
   · rintro ⟨aux, haux⟩
     let α := Sum.elim v aux
     have hsat_conf : ∀ C ∈ confGrid.2.2, ClauseSat α C := fun C hC => haux C (hConf_sub C hC)
     obtain ⟨hsat_inr, hgrid_val⟩ :=
       baog_ss R (2 ^ h') hR1 Nat.one_le_two_pow exclGrid consInrSt α hsat_conf
     have hgrid_false : lEv α confGrid.1 = false := by
       have hc := haux {negL confGrid.1} (by simp [stFinal, eu, addCl])
       rw [clauseSat_singleton, litEval_negL] at hc
       cases hcv : lEv α confGrid.1
       · rfl
       · rw [hcv] at hc; cases hc
     rw [hgrid_false] at hgrid_val
     replace hgrid_val := hgrid_val.symm
     rw [decide_eq_false_iff_not] at hgrid_val
     push Not at hgrid_val
     obtain ⟨s0, hs0⟩ := hgrid_val ⟨0, hR1⟩
     have hsat_brRes : ∀ C ∈ brRes.2.2, ClauseSat α C := fun C hC =>
       hsat_inr C (hInl_sub C (hBr_sub C hC))
     have htrue : aux 0 = true := by
       have hsat_base : ∀ C ∈ stBase.2, ClauseSat α C := fun C hC =>
         hsat_brRes C (hMat_sub C (h0_sub' C (h0_sub C hC)))
       have hc := hsat_base {tL} (by simp [stBase, eu, addCl])
       rw [clauseSat_singleton] at hc
       simpa [lEv, α, tL] using hc
     have hfval : lEv α fd.1 = false ∧ lEv α fd.2 = true := by
       simp [fd, fL, tL, lEv, α, htrue]
     have hex_false : lEv α (brRes.1 ⟨0, hR1⟩ s0).excl = false :=
       Bool.eq_false_iff.2 hs0
     exact bab_ss n t h' R D gates out H matsRes.1 fd hD_bound
       R 0 (Nat.sub_zero _) dummyBr matsRes.2 α ⟨0, hR1⟩ s0 (Nat.zero_le _)
       hstM (hF0.mono hleM) (hT0.mono hleM) hwM hsat_brRes hfval hex_false
 have hsat : ∀ v : V → Bool,
     (∀ j : Fin t, v (Sum.inr j) =
       ((⟨gates, 0⟩ : BinaryCircuit).wires
         (List.ofFn (fun i : Fin n => v (Sum.inl i)))).getD (out j) false) ↔
     ∃ aux : Fin m → Bool, Satisfies (Sum.elim v aux) (↑Ffin : Set _) := by
   intro v
   rw [hsat_nat v]
   constructor
   · rintro ⟨aux, haux⟩
     refine ⟨fun k : Fin m => aux k.val, fun C hC => ?_⟩
     rcases List.mem_map.1 (List.mem_toFinset.1 hC) with ⟨C', hC', rfl⟩
     exact mapCl_sat_of_nat m hm v aux (hstFinal C' hC').2 (haux C' hC')
   · rintro ⟨auxFin, haux⟩
     refine ⟨fun k => if hk : k < m then auxFin ⟨k, hk⟩ else false, fun C hC => ?_⟩
     have hmem : mapCl m hm C ∈ Ffin := List.mem_toFinset.2 (List.mem_map.2 ⟨C, hC, rfl⟩)
     exact mapCl_sat_to_nat m hm v auxFin (hstFinal C hC).2 (haux _ hmem)
 refine ⟨m, Ffin, ?_, hcard3, hsat, ?_⟩
 · have hsum1 : (∑ C ∈ Ffin, C.card) ≤ (Lfin.map Finset.card).sum := sum_toFinset_card_le Lfin
   have hsum2 : (Lfin.map Finset.card).sum ≤ 3 * Lfin.length :=
     sum_map_card_le Lfin 3 fun D hD => hcard3 D (List.mem_toFinset.2 hD)
   have hLlen : Lfin.length = stFinal.2.length := by simp [Lfin]
   have hst0_1 : st0.1 = 1 + n := h0_1
   have hstBase_len : stBase.2.length = 1 := rfl
   have hst0_len : st0.2.length ≤ 1 + 2 * n := by rw [hstBase_len] at h0_len; exact h0_len
   have hm_eq : m = confGrid.2.1 := rfl
   have hsf_len : stFinal.2.length = confGrid.2.2.length + 1 := rfl
   have hm_le : m ≤ (1 + n) +
       (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
       ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * R +
       (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
       2 * R * 2 ^ h' + 2 * R := by
     calc m = confGrid.2.1 := hm_eq
       _ ≤ consInrSt.1 + 2 * R * 2 ^ h' + 2 * R := hmC_v
       _ ≤ consInlSt.1 + (6 * R * 2 ^ h' + 4 * R) * t + 2 * R * 2 ^ h' + 2 * R :=
           Nat.add_le_add_right (Nat.add_le_add_right hmInr_v _) _
       _ ≤ brRes.2.1 + (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
           2 * R * 2 ^ h' + 2 * R :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hmInl_v _) _) _
       _ ≤ matsRes.2.1 + ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * R +
           (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
           2 * R * 2 ^ h' + 2 * R :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hmB_v _) _) _) _
       _ ≤ (1 + n) + (6 * T_n.intNodes * 2 ^ h' + ((4 + 2 * h') * 2 ^ h') * n) * R +
           ((1 + 2 * n + 4 * n * h' + 2 * gates.length) * 2 ^ h') * R +
           (6 * R * 2 ^ h' + 4 * R) * n + (6 * R * 2 ^ h' + 4 * R) * t +
           2 * R * 2 ^ h' + 2 * R :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
             (by rw [← hst0_1]; exact hmM_v) _) _) _) _) _
   have hcl_le : stFinal.2.length ≤ (1 + 2 * n) +
       (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R +
       ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * R +
       (18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t +
       6 * R * 2 ^ h' + 6 * R + 1 := by
     calc stFinal.2.length = confGrid.2.2.length + 1 := hsf_len
       _ ≤ consInrSt.2.length + 6 * R * 2 ^ h' + 6 * R + 1 := Nat.add_le_add_right hlC_c 1
       _ ≤ consInlSt.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * t + 6 * R * 2 ^ h' + 6 * R + 1 :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hlInr_c _) _) 1
       _ ≤ brRes.2.2.length + (18 * R * 2 ^ h' + 12 * R + 2) * n +
           (18 * R * 2 ^ h' + 12 * R + 2) * t + 6 * R * 2 ^ h' + 6 * R + 1 :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hlInl_c _) _) _) 1
       _ ≤ matsRes.2.2.length + ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * R +
           (18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t +
           6 * R * 2 ^ h' + 6 * R + 1 :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hlB_c _) _) _) _) 1
       _ ≤ (1 + 2 * n) + (21 * T_n.intNodes * 2 ^ h' + ((4 + 4 * h') * 2 ^ h') * n) * R +
           ((5 * n + (8 * n + 1) * h' + 5 * gates.length + 2 * t) * 2 ^ h') * R +
           (18 * R * 2 ^ h' + 12 * R + 2) * n + (18 * R * 2 ^ h' + 12 * R + 2) * t +
           6 * R * 2 ^ h' + 6 * R + 1 :=
           Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
             (le_trans hlM_c (Nat.add_le_add_right hst0_len _)) _) _) _) _) _) 1
   have hcard_le : (∑ C ∈ Ffin, C.card) ≤ 3 * stFinal.2.length := by
     calc (∑ C ∈ Ffin, C.card) ≤ (Lfin.map Finset.card).sum := hsum1
       _ ≤ 3 * Lfin.length := hsum2
       _ = 3 * stFinal.2.length := by rw [hLlen]
   exact le_trans (Nat.add_le_add_left hcard_le m)
     (size_bound_aux n t gates.length h h' R T_n.intNodes m stFinal.2.length hh'h hR1 hRbd hTn_int hm_le hcl_le)
 · intro ρ hρ
   let rounds := 128 * (D + h + Nat.clog 2 (n + t + 1) + 1)
   let U : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => ρ (Sum.inl i) = none)
   have hU_card : U.card ≤ h' := by
     have h1 : U.card ≤ h := hρ
     have h2 : U.card ≤ n := by
       calc U.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
         _ = n := Finset.card_fin n
     exact le_min h1 h2
   obtain ⟨r, hr_cov⟩ := hcov U hU_card
   have htrue_up : tL ∈ (upS Fnat)^[1] (sd ρ) := by
     rw [Function.iterate_one]
     exact upStep_unit1 (hFnat_sub _ (hConf_sub _ (hInr_sub _ (hInl_sub _ (hBr_sub _ (hMat_sub _ (h0_sub' _ (h0_sub _ (by simp [stBase, eu, addCl])))))))))
   have hfalse_up : negL fL ∈ (upS Fnat)^[1] (sd ρ) := by
     change tL ∈ (upS Fnat)^[1] (sd ρ)
     exact htrue_up
   have hk_up : ∀ (q : Fin n) (b : Bool), (Sum.inl (Sum.inl q), b) ∈ (sd ρ : Set (LN V)) →
       kL q ∈ (upS Fnat)^[1] (sd ρ) :=
     bki_up n t kL Fnat (sd ρ) stBase
       (fun C hC => hFnat_sub C (hConf_sub C (hInr_sub C (hInl_sub C (hBr_sub C (hMat_sub C (h0_sub' C hC)))))))
       hkBase hstBase
   let x0 : Fin n → Bool := fun i =>
     match ρ (Sum.inl i) with
     | some b => b
     | none => false
   have hx0_notin : ∀ q : Fin n, q ∉ U → ρ (Sum.inl q) = some (x0 q) := by
     intro q hq
     simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hq
     cases hq' : ρ (Sum.inl q) with
     | none => exact absurd hq' hq
     | some b => simp [x0, hq']
   have hq_notin_ready : ∀ q : Fin n, q ∉ U →
       kL q ∈ (upS Fnat)^[1] (sd ρ) ∧ fLt (xLit q) (x0 q) ∈ (upS Fnat)^[1] (sd ρ) := by
     intro q hq
     have hρq := hx0_notin q hq
     have hmem : (Sum.inl (Sum.inl q), x0 q) ∈ (sd ρ : Set (LN V)) := ⟨Sum.inl q, rfl, hρq⟩
     refine ⟨hk_up q (x0 q) hmem, ?_⟩
     rw [Function.iterate_one]
     apply subset_upStep
     cases hx : x0 q <;> simpa [xLit, fLt, negL, PEqualNP.Search.negLit, hx] using hmem
   let d_mat : ℕ := 2 * T_n.depth + 3 + h'
   let d_br : ℕ := d_mat + 1 + D + Nat.clog 2 (n + 1) + 1
   have hrounds_ge : d_br + 2 + h' + Nat.clog 2 R ≤ rounds := by
     have hclog_nt : Nat.clog 2 (n + 1) ≤ Nat.clog 2 (n + t + 1) := Nat.clog_mono_right 2 (by omega)
     have hclog_R : Nat.clog 2 R ≤ 2 + h' + Nat.clog 2 (n + 1) := clog2_bound_mul3 hRbd
     dsimp only [rounds, d_br, d_mat]
     omega
   have hmat_for_U : ∀ s : Fin (2 ^ h'), ∀ j ∈ U,
       ∃ b : Bool, matsRes.1 r j s b ∈ (upS Fnat)^[d_mat] (sd ρ) := by
     intro s j hjU
     obtain ⟨c_fn, hc_fn⟩ := hr_cov j hjU
     let c : Fin (2 ^ h') := bitsToFin c_fn
     have hScj : xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H r p j)) = true := by
       have h1 := hc_fn j hjU
       simp only at h1
       have heq : List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H r p j) =
           List.ofFn (fun p : Fin h' => c_fn p && H r p j) := by
         congr 1; ext p; simp [c, testBit_bitsToFin]
       rw [heq, h1]; decide
     have hqx : ∀ q : Fin n, q ≠ j →
         xl (List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H r p q)) = true →
         kL q ∈ (upS Fnat)^[1] (sd ρ) ∧ fLt (xLit q) (x0 q) ∈ (upS Fnat)^[1] (sd ρ) := by
       intro q hne hScq
       apply hq_notin_ready q
       intro hqU
       have h1 := hc_fn q hqU
       have heq : List.ofFn (fun p : Fin h' => decide (c.val.testBit p.val) && H r p q) =
           List.ofFn (fun p : Fin h' => c_fn p && H r p q) := by
         congr 1; ext p; simp [c, testBit_bitsToFin]
       rw [← heq, hScq] at h1
       have : q = j := of_decide_eq_true h1.symm
       exact hne this
     refine ⟨_, bam_up n h' R Fnat (sd ρ) H kL xLit tL fL T_n hTn_nd
       x0 r c s j (hTn_sub j) R 0 (Nat.sub_zero _) dummyW st0 (Nat.zero_le _) hst0 hT0 hF0 hkx0
       (fun C hC => hFnat_sub C (hConf_sub C (hInr_sub C (hInl_sub C (hBr_sub C (hMat_sub C hC))))))
       htrue_up hfalse_up hScj hqx⟩
   have hbranch_s : ∀ s : Fin (2 ^ h'),
       ∃ x' : Fin n → Bool,
         (∀ i : Fin n, ∀ sign : Bool, ρ (Sum.inl i) = some sign → x' i = sign) ∧
         ((brRes.1 r s).excl ∈ (upS Fnat)^[d_br] (sd ρ) ∨
           ((∀ i, lod ((brRes.1 r s).xDual i) (x' i) ∈ (upS Fnat)^[d_br] (sd ρ)) ∧
           (∀ j : Fin t, lod ((brRes.1 r s).wiresOut (out j)) (wv n x' gates (out j)) ∈ (upS Fnat)^[d_br] (sd ρ)) ∧
           (∀ q : Fin h', s.val.testBit q.val =
             xl (((List.finRange n).filter (fun i => H r q i)).map x')) ∧
           (∀ j : Fin t, ∀ sign : Bool, ρ (Sum.inr j) = some sign → wv n x' gates (out j) = sign))) := by
     intro s
     let x' : Fin n → Bool := fun j =>
       if hj : j ∈ U then Classical.choose (hmat_for_U s j hj) else x0 j
     have hx'_ρ : ∀ i : Fin n, ∀ sign : Bool, ρ (Sum.inl i) = some sign → x' i = sign := by
       intro i sign hρi
       have hnotU : i ∉ U := by simp [U, hρi]
       dsimp only [x']; simp only [hnotU, ↓reduceDIte]
       have h1 := hx0_notin i hnotU
       rw [hρi] at h1
       exact (Option.some.inj h1).symm
     have hx_in : ∀ j : Fin n,
         fLt (Sum.inl (Sum.inl j), true) (x' j) ∈ (upS Fnat)^[d_mat] (sd ρ) ∨
           matsRes.1 r j s (x' j) ∈ (upS Fnat)^[d_mat] (sd ρ) := by
       intro j
       by_cases hj : j ∈ U
       · right
         have hx'j : x' j = Classical.choose (hmat_for_U s j hj) := by dsimp only [x']; simp only [hj, ↓reduceDIte]
         rw [hx'j]
         exact Classical.choose_spec (hmat_for_U s j hj)
       · left
         have hx'j : x' j = x0 j := by dsimp only [x']; simp only [hj, ↓reduceDIte]
         rw [hx'j]
         exact upStep_iter_le Fnat (sd ρ) (by omega) (hq_notin_ready j hj).2
     have hbr_up := bab_up n t h' R D gates out H matsRes.1 fd Fnat (sd ρ)
       d_mat x' r s R 0 (Nat.sub_zero _) dummyBr matsRes.2 (Nat.zero_le _) hstM
       (hF0.mono hleM) (hT0.mono hleM) hwM
       (fun C hC => hFnat_sub C (hConf_sub C (hInr_sub C (hInl_sub C (hBr_sub C hC)))))
       hx_in hfalse_up
     refine ⟨x', hx'_ρ, ?_⟩
     by_cases hpar : ∀ q : Fin h', s.val.testBit q.val =
         xl (((List.finRange n).filter (fun i => H r q i)).map x')
     · by_cases hout : ∀ j : Fin t, ∀ sign : Bool, ρ (Sum.inr j) = some sign → wv n x' gates (out j) = sign
       · right
         refine ⟨fun i => upStep_iter_le Fnat (sd ρ) (by omega) (hbr_up.1 i),
           fun j => upStep_iter_le Fnat (sd ρ) (by omega) (hbr_up.2.2.2.1 j (hD_bound j)),
           hpar, hout⟩
       · left
         push Not at hout
         obtain ⟨j, sign, hρj, hne⟩ := hout
         have hseedj : (Sum.inl (Sum.inr j), sign) ∈ (sd ρ : Set (LN V)) := ⟨Sum.inr j, rfl, hρj⟩
         exact upStep_iter_le Fnat (sd ρ) (by omega) (hbr_up.2.2.2.2 j sign (hD_bound j) hseedj hne)
     · left
       push Not at hpar
       obtain ⟨q, hq⟩ := hpar
       exact upStep_iter_le Fnat (sd ρ) (by omega) (hbr_up.2.1 q hq)
   constructor
   · constructor
     · intro hno
       have hall_excl : ∀ s : Fin (2 ^ h'), exclGrid r s ∈ (upS Fnat)^[d_br] (sd ρ) := by
         intro s
         obtain ⟨x', hx'_ρ, hres⟩ := hbranch_s s
         rcases hres with hex | ⟨_, _, _, hout⟩
         · exact hex
         · exfalso
           apply hno
           let v : V → Bool := fun raw => match raw with
             | Sum.inl i => x' i
             | Sum.inr j => wv n x' gates (out j)
           refine ⟨v, fun j => by rw [(wires_length_and_getD n (fun i => v (Sum.inl i)) gates).2 (out j)],
             fun raw sign hraw => ?_⟩
           cases raw with
           | inl i => exact hx'_ρ i sign hraw
           | inr j => exact hout j sign hraw
       have hgrid_up := baog_up R (2 ^ h') hR1 Nat.one_le_two_pow Fnat (sd ρ) exclGrid consInrSt d_br
         (fun C hC => hFnat_sub C (hConf_sub C hC)) ⟨r, hall_excl⟩
       have hclog2 : Nat.clog 2 (2 ^ h') = h' := by simp
       rw [hclog2] at hgrid_up
       have hgrid_rounds : confGrid.1 ∈ (upS Fnat)^[rounds] (sd ρ) :=
         upStep_iter_le Fnat (sd ρ) (le_trans (by omega) hrounds_ge) hgrid_up
       have hC_nat : ({negL confGrid.1} : CN V) ∈ Fnat :=
         hFnat_sub _ (by simp [stFinal, eu, addCl])
       refine ⟨mapCl m hm _, hImgF _ hC_nat, fun l hl => ?_⟩
       rw [mapCl, Finset.image_singleton, Finset.mem_singleton] at hl
       subst hl
       change negL (mapLit m hm (negL confGrid.1)) ∈ (upS Ffin)^[rounds] (sd ρ)
       rw [← mapLit_negL m hm (negL confGrid.1), negL_negL]
       exact upStep_map_transport m hm Fnat Ffin hImgF ρ rounds confGrid.1 hgrid_rounds
     · intro hconf hcomp
       exact enc_conflict_sound (d := rounds) (fun v hv => (hsat v).1 hv) hcomp hconf
   · intro hcomp raw sign
     constructor
     · intro hforced
       have hnat : (Sum.inl raw, sign) ∈ (upS Fnat)^[rounds] (sd ρ) := by
         cases raw with
         | inl i =>
           have hex : ∀ s : Fin (2 ^ h'),
               exclGrid r s ∈ (upS Fnat)^[d_br] (sd ρ) ∨
               lod ((brRes.1 r s).xDual i) sign ∈ (upS Fnat)^[d_br] (sd ρ) := by
             intro s
             obtain ⟨x', hx'_ρ, hres⟩ := hbranch_s s
             rcases hres with hex | ⟨hx_up, _, _, hout⟩
             · exact Or.inl hex
             · right
               let v : V → Bool := fun raw' => match raw' with
                 | Sum.inl i' => x' i'
                 | Sum.inr j' => wv n x' gates (out j')
               have hv_comp : (∀ j : Fin t, v (Sum.inr j) =
                   ((⟨gates, 0⟩ : BinaryCircuit).wires
                     (List.ofFn (fun i' : Fin n => v (Sum.inl i')))).getD (out j) false) ∧
                   ∀ (raw' : V) (sign' : Bool), ρ raw' = some sign' → v raw' = sign' := by
                 refine ⟨fun j => by rw [(wires_length_and_getD n (fun i' => v (Sum.inl i')) gates).2 (out j)],
                   fun raw' sign' hraw' => ?_⟩
                 cases raw' with
                 | inl i' => exact hx'_ρ i' sign' hraw'
                 | inr j' => exact hout j' sign' hraw'
               have hvi : x' i = sign := hforced v hv_comp
               rw [← hvi]
               exact hx_up i
           have hcons := bci_up n t h' R hR1 Fnat (sd ρ) exclGrid brRes.1 d_br i sign
             n 0 (Nat.sub_zero _) brRes.2 (Nat.zero_le _)
             (fun C hC => hFnat_sub C (hConf_sub C (hInr_sub C (hInl_sub C hC)))) ⟨r, hex⟩
           exact upStep_iter_le Fnat (sd ρ) hrounds_ge hcons
         | inr j =>
           have hex : ∀ s : Fin (2 ^ h'),
               exclGrid r s ∈ (upS Fnat)^[d_br] (sd ρ) ∨
               lod ((brRes.1 r s).wiresOut (out j)) sign ∈ (upS Fnat)^[d_br] (sd ρ) := by
             intro s
             obtain ⟨x', hx'_ρ, hres⟩ := hbranch_s s
             rcases hres with hex | ⟨_, hw_up, _, hout⟩
             · exact Or.inl hex
             · right
               let v : V → Bool := fun raw' => match raw' with
                 | Sum.inl i' => x' i'
                 | Sum.inr j' => wv n x' gates (out j')
               have hv_comp : (∀ j' : Fin t, v (Sum.inr j') =
                   ((⟨gates, 0⟩ : BinaryCircuit).wires
                     (List.ofFn (fun i' : Fin n => v (Sum.inl i')))).getD (out j') false) ∧
                   ∀ (raw' : V) (sign' : Bool), ρ raw' = some sign' → v raw' = sign' := by
                 refine ⟨fun j' => by rw [(wires_length_and_getD n (fun i' => v (Sum.inl i')) gates).2 (out j')],
                   fun raw' sign' hraw' => ?_⟩
                 cases raw' with
                 | inl i' => exact hx'_ρ i' sign' hraw'
                 | inr j' => exact hout j' sign' hraw'
               have hvj : wv n x' gates (out j) = sign := hforced v hv_comp
               rw [← hvj]
               exact hw_up j
           have hcons := bcr_up n t h' R hR1 out Fnat (sd ρ) exclGrid brRes.1 d_br j sign
             t 0 (Nat.sub_zero _) consInlSt (Nat.zero_le _)
             (fun C hC => hFnat_sub C (hConf_sub C (hInr_sub C hC))) ⟨r, hex⟩
           exact upStep_iter_le Fnat (sd ρ) hrounds_ge hcons
       exact upStep_map_transport m hm Fnat Ffin hImgF ρ rounds (Sum.inl raw, sign) hnat
     · intro hmem v ⟨hv_ag, hv_ρ⟩
       exact enc_force_sound (d := rounds) (fun v' hv' => (hsat v').1 hv') hmem v hv_ag hv_ρ
end PEqualNP.Outside.L_pcx_303

theorem PEqualNP.Outside.L_pcx_303 : (∀ (n t h : ℕ) (gates : List PEqualNP.MetaComplexity.BinaryGate) (out : Fin t → ℕ),
  let V := Fin n ⊕ Fin t
  let circuit : PEqualNP.MetaComplexity.BinaryCircuit := ⟨gates, 0⟩
  let agrees := fun (v : V → Bool) =>
    let wires := circuit.wires (List.ofFn (fun i : Fin n => v (Sum.inl i)))
    ∀ j : Fin t, v (Sum.inr j) = wires.getD (out j) false
  let depths := gates.foldl (fun (w : List ℕ) g =>
    w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]) (List.replicate n 0)
  let D := (Finset.univ : Finset (Fin t)).sup (fun j => depths.getD (out j) 0)
  let rounds := 128*(D+h+Nat.clog 2 (n+t+1)+1)
  ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
    m + (∑ C ∈ F, C.card) ≤ 262144*(n+t+gates.length+1)*(h+1)^2*(Nat.clog 2 (n+1)+1)*2^h ∧
    (∀ C ∈ F, C.card ≤ 3) ∧
    (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
    ∀ ρ : V → Option Bool,
      (Finset.univ.filter (fun i : Fin n => ρ (Sum.inl i) = none)).card ≤ h →
      let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
      let advance := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
        S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
          PEqualNP.Search.negLit other ∈ S}
      let known := (advance^[rounds]) seed
      let complete := fun v : V → Bool => agrees v ∧
        ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
      ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, PEqualNP.Search.negLit l ∈ known) ∧
      ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
        (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known)) := by
  intro n t h gates out
  by_cases hh0 : h = 0 ∨ n = 0
  · exact PEqualNP.Outside.L_pcx_303.upper_bound_h0 n t h gates out hh0
  · have hh : 1 ≤ h := by omega
    have hn : 1 ≤ n := by omega
    exact PEqualNP.Outside.L_pcx_303.upper_bound_hpos n t h gates out hh hn
