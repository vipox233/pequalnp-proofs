import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47082

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241384 * 2 ^ 32 + 3907577992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x00071450d1434354#64 ++ 0x0001c5143450d0d5#64 ++ 0xf50f3cf1f3c7c7fe#64 ++ 0xfd43cf3c7cf1f1ff#64 : BitVec 256),
   (0x10704926249898a8#64 ++ 0x041c12498926262a#64 ++ 0xfef0cf3e3cf8f8ff#64 ++ 0xffbc33cf8f3e3e3f#64 : BitVec 256),
   (0x2700a28b4a2d2d30#64 ++ 0x09c028a2d28b4b4c#64 ++ 0xf700f3cfcf3f3f33#64 ++ 0x7dc03cf3f3cfcfcc#64 : BitVec 256),
   (0x4bbb03f00fc036c0#64 ++ 0x52eec0fc03f00db0#64 ++ 0x5bff03f00fc03fc3#64 ++ 0xd6ffc0fc03f00ff0#64 : BitVec 256),
   (0x8bddfc000ff6c000#64 ++ 0xa2f77f0003fdb000#64 ++ 0xabfffc000fffc003#64 ++ 0xeaffff0003fff000#64 : BitVec 256),
   (0xc7eefffdb0000001#64 ++ 0x31fbbfff6c000000#64 ++ 0xcffffffff0000003#64 ++ 0xb3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x54000030300000fc 0x1500000c0c00003f

def z1 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z2 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z3 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z4 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z5 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xabfffc000fffc003 0xeaffff0003fff000

def z6 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xcffffffff0000003 0xb3fffffffc000000

def z7 : W := mkw 0x0000000200080820 0x0000000080020208 0xf600cf3e3cf8f8ff 0xfd8033cf8f3e3e3f

def z8 : W := mkw 0x240202dbd0092f74 0x090080b6f4024bdd 0x540003fff0003ffc 0x150000fffc000fff

def z9 : W := mkw 0x4b8b02d00b402640 0x52e2c0b402d00990 0x010f00c003000700 0x0043c03000c001c0

def z10 : W := mkw 0x402203f0000036c0 0x500880fc00000db0 0x500003f000003fc0 0x140000fc00000ff0

def z11 : W := mkw 0x8044fc000036c000 0xa0113f00000db000 0xa000fc00003fc000 0x28003f00000ff000

def z12 : W := mkw 0x081100000fc036c0 0x4204400003f00db0 0x100000000fc03fc0 0x4400000003f00ff0

def z13 : W := mkw 0x502203f620083ee8 0x540880fd88020fba 0x540003fe30003ffc 0x150000ff8c000fff

def z14 : W := mkw 0x8bdffc509ff6c000 0xa2f7ff1427fdb000 0xeffffcf1ffffc003 0xfbffff3c7ffff000

def z15 : W := mkw 0x1070492424909088 0x041c124909242422 0x08f00c3030c0c0cc 0x823c030c0c303033

def z16 : W := mkw 0x3770ebaf6ebdbdb8 0x0ddc3aebdbaf6f6e 0xfff0ffffffffffff 0xfffc3fffffffffff

def z17 : W := mkw 0x8bfdfd200ff6d080 0xa2ff7f4803fdb420 0xfbffff300ffff8c3 0xfeffffcc03fffe30

def z18 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700ffffffffffff 0xfdc03fffffffffff

def z19 : W := mkw 0x8b8db4000b664000 0xa2e36d0002d99000 0xa30ff0000f3f0003 0x68c3fc0003cfc000

def z20 : W := mkw 0x081100000fc00000 0x0204400003f00000 0x000000000fc00000 0x4000000003f00000

def z21 : W := mkw 0x081100000ff6f6c0 0xc204400003fdbdb0 0x300000000fffffc0 0x4c00000003fffff0

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4000c3030c0c0fe 0xfd00030c0c30303f

def z23 : W := mkw 0xcfeffffdbb402641 0x73fbffff6ed00990 0xcffffffff3000703 0xb3fffffffcc001c0

def z24 : W := mkw 0x4b9b02d00fc02640 0x52e6c0b403f00990 0x0bff00c00fc00703 0xc2ffc03003f001c0

def z25 : W := mkw 0x87ccfc0db0000001 0x21f33f036c000000 0x8ffffc0ff0000003 0xa3ffff03fc000000

def z26 : W := mkw 0xcbfffff00ff6c000 0xb2fffffc03fdb000 0xebfffff00fffc003 0xfafffffc03fff000

def z27 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xfffffc303fffc0ff 0xffffff0c0ffff03f

def z28 : W := mkw 0xc0e8492420000001 0x303a124908000000 0x08f0000000000000 0x023c000000000000

def z29 : W := mkw 0xc7eefffdf0034115 0x31fbbfff7c00d045 0xeffffffff007c03f 0xbbfffffffc01f00f

def z30 : W := mkw 0x4bfb4bf00fd0b6c0 0x52fed2fc03f42db0 0xfbffcff00ff8ffc3 0xfefff3fc03fe3ff0

def z31 : W := mkw 0x8bddfe800ff6e400 0xa2f77fa003fdb900 0xfbffffc00fffff03 0xfefffff003ffffc0

def z32 : W := mkw 0x081100000ff6c000 0x8204400003fdb000 0x200000000fffc000 0x4800000003fff000

def z33 : W := mkw 0x0b9900000fc036c0 0x42e6400003f00db0 0x1bff00000fc03fc3 0xc6ffc00003f00ff0

def z34 : W := mkw 0x1011000245dbdbfc 0x040440009176f6ff 0x300000000ffffffc 0x4c00000003ffffff

def z35 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z36 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z37 : W := mkw 0x0000000040010110 0x0000000010004044 0xf50030c1c3070732 0x7d400c3070c1c1cc

def z38 : W := mkw 0x2707b6dbdb6f6f74 0x09c1edb6f6dbdbdd 0xf70fffffffffffff 0xfdc3ffffffffffff

def z39 : W := mkw 0x00041400d0034114 0x000105003400d045 0xa4003c01f007c03c 0x29000f007c01f00f

def z40 : W := mkw 0x4bb803a00e803480 0x52ee00e803a00d20 0x0af003000c003801 0x02bc00c003000e00

def z41 : W := mkw 0xa7ccfe8b4a2d2d30 0x29f33fa2d28b4b4c 0xffffffcfcf3f3f33 0xfffffff3f3cfcfcc

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000000c0c0fc 0x4c0000000030303f

def z43 : W := mkw 0x10445c06f01bc93c 0x04111701bc06f24f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z44 : W := mkw 0x10775d76f5dbdbfc 0x041dd75dbd76f6ff 0xffffffffffffffff 0xffffffffffffffff

def z45 : W := mkw 0xc7eefffdba240001 0x31fbbfff6e890000 0xefffffffff3f0003 0xfbffffffffcfc000

def z46 : W := mkw 0x2700a2894a252510 0x09c028a252894944 0xf50030c1c3070732 0x7d400c3070c1c1cc

def z47 : W := mkw 0x0030012004801080 0x000c004801200420 0x5af003300cc038c3 0xd6bc00cc03300e30

def z48 : W := mkw 0x5bfb4bf62fd8bee8 0x56fed2fd8bf62fba 0xffffcffe3ff8ffff 0xfffff3ff8ffe3fff

def z49 : W := mkw 0xdbfffff62ffefee8 0xf6fffffd8bffbfba 0xfffffffe3fffffff 0xffffffff8fffffff

def z50 : W := mkw 0x0b9900000fc00000 0x02e6400003f00000 0x0bff00000fc00003 0xc2ffc00003f00000

def z51 : W := mkw 0xcbfffff00ff6f6c0 0xf2fffffc03fdbdb0 0xfbfffff00fffffc3 0xfefffffc03fffff0

def z52 : W := mkw 0x2400a00b4a2d2d30 0x09002802d28b4b4c 0xb400f00fcf3f3f30 0x6d003c03f3cfcfcc

def z53 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x0aff03300cc038c1 0x82bfc0cc03300e30

def z54 : W := mkw 0x40220170000012c0 0x5008805c000004b0 0x00000030000000c0 0x0000000c00000030

def z55 : W := mkw 0xafddfe8b0ffeec20 0xabf77fa2c3ffbb08 0xabffff0e0ffff803 0xeaffffc383fffe00

def z56 : W := mkw 0x081300500fc036c0 0x4204c01403f00db0 0x510f00f00fc03fc2 0xd443c03c03f00ff0

def z57 : W := mkw 0xc78fb6d9d1434355 0x31e3edb67450d0d5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z58 : W := mkw 0xcffffffdbfc036c1 0x73ffffff6ff00db0 0xdfffffffffc03fc3 0xf7fffffffff00ff0

def z59 : W := mkw 0xe7eefffffa2d2d31 0x39fbbffffe8b4b4c 0xffffffffff3f3f33 0xffffffffffcfcfcc

def z60 : W := mkw 0x00020050d0010354 0x00008014340040d5 0x000000c1c0000700 0x00000030700001c0

def z61 : W := mkw 0xc7effffdf1434355 0x31fbffff7c50d0d5 0xfffffffff3c7c7ff 0xfffffffffcf1f1ff

def z62 : W := mkw 0x0003005041410350 0x0000c014105040d4 0xf50f30f1c3c707f2 0xfd43cc3c70f1c1fc

def z63 : W := mkw 0x0700a28900000000 0x01c028a240000000 0xc700f3cfc0000003 0x31c03cf3f0000000

def z64 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x5ef0c33e3c3838fd 0x17bc30cf8f0e0e3f

def z65 : W := mkw 0x4bbb01700fc012c0 0x52eec05c03f004b0 0x0bff00300fc000c3 0xc2ffc00c03f00030

def z66 : W := mkw 0x8bd8e8000eb48000 0xa2f63a0003ad2000 0xabf0f0000f3f0003 0x6afc3c0003cfc000

def z67 : W := mkw 0x48bb017005c012c0 0x522ec05c017004b0 0x08ff003000c000c0 0x823fc00c00300030

def z68 : W := mkw 0xc8ff5d74b5d2c001 0xb23fd75d2d74b000 0x08ff0c3030c0c000 0x823fc30c0c303000

def z69 : W := mkw 0xa444fc0ff02d0931 0x29113f03fc0b424c 0xa400fc0ff03f0030 0x29003f03fc0fc00c

def z70 : W := mkw 0x43aa03f000000000 0x10ea80fc00000000 0x4bff03f000000003 0x92ffc0fc00000000

def z71 : W := mkw 0x43aa03f00a002400 0x10ea80fc02800900 0x5bff03f00f003f03 0xd6ffc0fc03c00fc0

def z72 : W := mkw 0x4bbb03f0dfc137d4 0x52eec0fc37f04df5 0x5fff03f1ffc03fff 0xd7ffc0fc7ff00fff

def z73 : W := mkw 0x00020050d0010354 0x00008014340040d5 0x540000f1f00007fc 0x1500003c7c0001ff

def z74 : W := mkw 0x8bd8e8000eb48000 0xa2f63a0003ad2000 0x0af0c0000c380001 0x02bc3000030e0000

def z75 : W := mkw 0xcbff5ff4bfc036c1 0x72ffd7fd2ff00db0 0x5bff0ff03fc03fc3 0xd6ffc3fc0ff00ff0

def z76 : W := mkw 0x10300126248818a8 0x040c00498922062a 0x5ef0033e3cc038ff 0xd7bc00cf8f300e3f

def z77 : W := mkw 0x2f11a28b4fed3ff0 0x4bc468a2d3fb4ffc 0xf700f3cfcfff3ff3 0x7dc03cf3f3ffcffc

def z78 : W := mkw 0x3770ebaf6ebdbdb8 0x0ddc3aebdbaf6f6e 0xfff0f3cfcf3f3f33 0x7ffc3cf3f3cfcfcc

def z79 : W := mkw 0xc7effffdb1424001 0x31fbffff6c509000 0xeffffffff3c7c003 0xfbfffffffcf1f000

def z80 : W := mkw 0x00071452d14b4b74 0x0001c514b452d2dd 0xf70fffffffffffff 0xfdc3ffffffffffff

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0xc600c30e00000003 0x318030c380000000

def z82 : W := mkw 0x0007145091424244 0x0001c51424509091 0x000f0c3030c0c0cc 0x8003c30c0c303033

def z83 : W := mkw 0x2700a28b0a2c2c20 0x09c028a2c28b0b08 0x0200c30e0c383801 0x008030c3830e0e00

def z84 : W := mkw 0xd7fefffdb4909089 0x35ffbfff6d242422 0xcffffffff0c0c0cf 0xb3fffffffc303033

def z85 : W := mkw 0x281100024fed3ff0 0x4a04400093fb4ffc 0x300000000fff3ff0 0x4c00000003ffcffc

def z86 : W := mkw 0x0070492004909080 0x001c124801242420 0xfaf0cf300cf8f8c3 0xfebc33cc033e3e30

def z87 : W := mkw 0x00665d74b0000000 0x0019975d2c000000 0xcffffffff0000003 0xb3fffffffc000000

def z88 : W := mkw 0xc78eb6d990000001 0x31e3adb664000000 0xc50f3cf1f0000002 0xb143cf3c7c000000

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0x520003000c003803 0x548000c003000e00

def z90 : W := mkw 0x2400a00b402d0930 0x09002802d00b424c 0xa400f00fc03f0030 0x29003c03f00fc00c

def z91 : W := mkw 0x58fb497625d89ae8 0x563ed25d897626ba 0xfeffcf3e3cf8f8ff 0xffbff3cf8f3e3e3f

def z92 : W := mkw 0x88dd5c0005d2c000 0xa23757000174b000 0x08ff0c0000c0c000 0x823fc30000303000

def z93 : W := mkw 0x200000024a2d2d30 0x08000000928b4b4c 0x300000000f3f3f30 0x4c00000003cfcfcc

def z94 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x0bff03c00f003f01 0x02ffc0f003c00fc0

def z95 : W := mkw 0x000000000a002400 0x0000000002800900 0x100000000f003f00 0x4400000003c00fc0

def z96 : W := mkw 0x47aa03fdb0000001 0x11ea80ff6c000000 0x4fff03fff0000003 0x93ffc0fffc000000

def z97 : W := mkw 0x0000000240090930 0x000000009002424c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z98 : W := mkw 0x0bb901200fc01080 0x02ee404803f00420 0x5bff03300fc038c3 0xd6ffc0cc03f00e30

def z99 : W := mkw 0x10171452d5dbdbfc 0x0405c514b576f6ff 0xf50f3cf1fffffffe 0xfd43cf3c7fffffff

def z100 : W := mkw 0x0899000005c00000 0x0226400001700000 0x08ff000000c00000 0x823fc00000300000

def z101 : W := mkw 0x83ccfc0000000000 0x20f33f0000000000 0x8bfffc0000000003 0xa2ffff0000000000

def z102 : W := mkw 0x0001000001400000 0x0000400000500000 0x010f000003c00002 0xc043c00000f00000

def z103 : W := mkw 0x2701a28b4b6f6f74 0x09c068a2d2dbdbdd 0xf700f3cfcfffffff 0x7dc03cf3f3ffffff

def z104 : W := mkw 0x6fbba3fb4fed3ff0 0x5beee8fed3fb4ffc 0xfffff3ffcfff3ff3 0xfffffcfff3ffcffc

def z105 : W := mkw 0x4bbb03f00ff6f6c0 0xd2eec0fc03fdbdb0 0x7bff03f00fffffc3 0xdeffc0fc03fffff0

def z106 : W := mkw 0x10220176f0091bfc 0x0408805dbc0246ff 0x540003fff0003ffc 0x150000fffc000fff

def z107 : W := mkw 0x0000000040010110 0x0000000010004044 0xa4003001c0070030 0x29000c007001c00c

def z108 : W := mkw 0x4fbba3f90fc036c0 0x53eee8fe43f00db0 0xdffff3ffcfc03fc3 0xf7fffcfff3f00ff0

def z109 : W := mkw 0x8444fc0db0000001 0x21113f036c000000 0x8400fc0ff0000000 0x21003f03fc000000

def z110 : W := mkw 0x9bfffd76ffffdbfc 0xa6ffff5dbffff6ff 0xffffffffffffffff 0xffffffffffffffff

def z111 : W := mkw 0x0005140001424000 0x0001450000509000 0xa10f3c0003c7c002 0xe843cf0000f1f000

def z112 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xf50f30c1c3070732 0x7d43cc3070c1c1cc

def z113 : W := mkw 0x0006145090000000 0x0001851424000000 0xf50f3cf1f0c0c0fe 0xfd43cf3c7c30303f

def z114 : W := mkw 0x8fddfc0dbff6c001 0xa3f77f036ffdb000 0xaffffc0fffffc003 0xebffff03fffff000

def z115 : W := mkw 0x10504806249898a8 0x041412018926262a 0xb400cc0e3cf8f8fc 0x6d0033038f3e3e3f

def z116 : W := mkw 0x033003a00e803480 0x00cc00e803a00d20 0x5bf003f00fc03fc3 0xd6fc00fc03f00ff0

def z117 : W := mkw 0x542203ffb00818a9 0x150880ffec02062a 0x540003fff00038fc 0x150000fffc000e3f

def z118 : W := mkw 0x030002800a002400 0x00c000a002800900 0x530003c00f003f03 0x54c000f003c00fc0

def z119 : W := mkw 0xc0ee5d74b0000001 0x303b975d2c000000 0x08ff0c3030000000 0x823fc30c0c000000

def z120 : W := mkw 0x0050480004908000 0x0014120001242000 0xaaf0cc000cf8c003 0xeabc3300033e3000

def z121 : W := mkw 0x2400028b40092d30 0x090000a2d0024b4c 0xf50033cfc3073f32 0x7d400cf3f0c1cfcc

def z122 : W := mkw 0xcffdffad2ff6c001 0xb3ff7feb4bfdb000 0xabffff0e0fffc003 0xeaffffc383fff000

def z123 : W := mkw 0x3770ebaf2ebcbca8 0x0ddc3aebcbaf2f2a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z124 : W := mkw 0xe7eefffdfa252511 0x39fbbfff7e894944 0xcffffffff3070703 0xb3fffffffcc1c1c0

def z125 : W := mkw 0x58fb497425d092c8 0x563ed25d097424b2 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z126 : W := mkw 0x442203fdb00036c1 0x510880ff6c000db0 0x540003fff0003fc0 0x150000fffc000ff0

def z127 : W := mkw 0x0004140000000000 0x0001050000000000 0x810f3c0000000002 0xa043cf0000000000

def z128 : W := mkw 0x5bf84ba62e98bca8 0x56fe12e98ba62f2a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z129 : W := mkw 0x20000002402d0930 0x08000000900b424c 0x20000000003f0030 0x08000000000fc00c

def z130 : W := mkw 0x8344fc000a36c000 0xa0d13f00028db000 0xa300fc000f3fc003 0x68c03f0003cff000

def z131 : W := mkw 0x2400028b40092d30 0x090000a2d0024b4c 0x540003cfc0003f30 0x150000f3f0000fcc

def z132 : W := mkw 0x2704b68bda2f6d34 0x09c12da2f68bdb4d 0xf700ffcfff3fff3f 0x7dc03ff3ffcfffcf

def z133 : W := mkw 0x2400a00b402d0930 0x09002802d00b424c 0xf500f0cfc33f0732 0x7d403c33f0cfc1cc

def z134 : W := mkw 0x1040480620188828 0x041012018806220a 0xa400cc0e3038c03c 0x290033038c0e300f

def z135 : W := mkw 0xa444fc0b403fc930 0xa9113f02d00ff24c 0xa400fc0fc03fc030 0x29003f03f00ff00c

def z136 : W := mkw 0xafddfe8b4fffed30 0xabf77fa2d3fffb4c 0xffffffcfcfffff33 0xfffffff3f3ffffcc

def z137 : W := mkw 0xc7eefffdb00036c1 0x71fbbfff6c000db0 0xdffffffff0003fc3 0xb7fffffffc000ff0

def z138 : W := mkw 0xa744fe8ffa2d2d31 0x29d13fa3fe8b4b4c 0xf700ffcfff3f3f33 0x7dc03ff3ffcfcfcc

def z139 : W := mkw 0xcffffffdbff6c001 0xb3ffffff6ffdb000 0xefffffffffffc003 0xfbfffffffffff000

def z140 : W := mkw 0xe78eb6dbda2d2d31 0x39e3adb6f68b4b4c 0xf70ff3cfcf3f3f33 0x7dc3fcf3f3cfcfcc

def z141 : W := mkw 0x10604926201898a8 0x041812498806262a 0xf400cf3e3038f8fc 0x3d0033cf8c0e3e3f

def z142 : W := mkw 0x0060492420000000 0x0018124908000000 0xcef0cf3e30000003 0xb3bc33cf8c000000

def z143 : W := mkw 0xd7feffffb49898a9 0x35ffbfffed26262a 0xfffffffffcf8f8ff 0xffffffffff3e3e3f

def z144 : W := mkw 0x8bdffc50dff7c354 0xa2f7ff1437fdf0d5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z145 : W := mkw 0x2700a00b4a2d0930 0x09c02802d28b424c 0xa700f00fcf3f0033 0x69c03c03f3cfc00c

def z146 : W := mkw 0x2700028b4a092d30 0x09c000a2d2824b4c 0x570003cfcf003f33 0x55c000f3f3c00fcc

def z147 : W := mkw 0x0000000200080820 0x0000000080020208 0xf600c30e0c383833 0x7d8030c3830e0e0c

def z148 : W := mkw 0x9bfdfd242ff6d088 0xa6ff7f490bfdb422 0xabfffc303fffc0cf 0xeaffff0c0ffff033

def z149 : W := mkw 0x10271576f14b5bfc 0x0409c55dbc52d6ff 0xf50f3ffff3c7fffe 0xfd43cffffcf1ffff

def z150 : W := mkw 0x80445c04b0000001 0x201117012c000000 0x00000c0030000000 0x000003000c000000

def z151 : W := mkw 0x642203fff0092d31 0x190880fffc024b4c 0x540003fff0003f30 0x150000fffc000fcc

def z152 : W := mkw 0xc7e8ebad20000001 0x31fa3aeb48000000 0xcff0f3cfc0000003 0x33fc3cf3f0000000

def z153 : W := mkw 0x0000000200080820 0x0000000080020208 0x5400030e00003830 0x150000c380000e0c

def z154 : W := mkw 0x0000000200080820 0x0000000080020208 0x0200c30e0c383801 0x008030c3830e0e00

def z155 : W := mkw 0x10200126200818a8 0x040800498802062a 0xf4000f3e30c0f8fe 0xfd0003cf8c303e3f

def z156 : W := mkw 0x4bab03f00b4036c0 0x52eac0fc02d00db0 0x510f03f003003fc0 0x1443c0fc00c00ff0

def z157 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x310f30c1c3c7c7fc 0x4c43cc3070f1f1ff

def z158 : W := mkw 0x0002005000000240 0x0000801400000090 0x500000f0000007c0 0x1400003c000001f0

def z159 : W := mkw 0x0006145090000000 0x0001851424000000 0xc50f3cf1f0000002 0xb143cf3c7c000000

def z160 : W := mkw 0xcffffffdb5c012c1 0x73ffffff6d7004b0 0xcffffffff0c000c3 0xb3fffffffc300030

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0xa4000c003000c03c 0x290003000c00300f

def z162 : W := mkw 0xc8ff5d7005d2d2c0 0xf23fd75c0174b4b0 0x08ff0c3000c0c0c0 0x823fc30c00303030

def z163 : W := mkw 0x0003005041434354 0x0000c0141050d0d5 0x710f00f003c7c7fe 0xdc43c03c00f1f1ff

def z164 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xfef0c30e0c383833 0x7fbc30c3830e0e0c

def z165 : W := mkw 0x0001000001424244 0x0000400000509091 0x0000000000c0c0cc 0x0000000000303033

def z166 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x09ff3c0003c7c000 0x827fcf0000f1f000

def z167 : W := mkw 0x1070492424909088 0x041c124909242422 0xaaf0cc303cf8c0cf 0xeabc330c0f3e3033

def z168 : W := mkw 0x0700a2890a002400 0x01c028a242800900 0xd700f3cfcf003f03 0x75c03cf3f3c00fc0

def z169 : W := mkw 0x9474fd2fb49898a9 0x251d3f4bed26262a 0xfef0ff3ffcf8f8ff 0xffbc3fcfff3e3e3f

def z170 : W := mkw 0x10200126200818a8 0x040800498802062a 0x5400033e300038fc 0x150000cf8c000e3f

def z171 : W := mkw 0xd7f8ebaf249898a9 0x35fe3aebc926262a 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z172 : W := mkw 0x47aaa3f900000000 0x11eaa8fe40000000 0xcffff3ffc0000003 0xb3fffcfff0000000

def z173 : W := mkw 0x8bddfc000ff6f6c0 0xe2f77f0003fdbdb0 0xbbfffc000fffffc3 0xeeffff0003fffff0

def z174 : W := mkw 0x442203fdb0000001 0x110880ff6c000000 0x440003fff0000000 0x110000fffc000000

def z175 : W := mkw 0x00555c0005d2c000 0x001557000174b000 0xabfffc000fffc003 0xeaffff0003fff000

def z176 : W := mkw 0x0033017005c012c0 0x000cc05c017004b0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z177 : W := mkw 0x9bf8e9262ebc98a8 0xa6fe3a498baf262a 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z178 : W := mkw 0x2700a2894a252510 0x09c028a252894944 0x530033c1cf073f03 0x54c00cf073c1cfc0

def z179 : W := mkw 0x1040480620188828 0x041012018806220a 0x0000c00e00380000 0x00003003800e0000

def z180 : W := mkw 0x0001000041434354 0x000040001050d0d5 0x3000000003c7c7fc 0x4c00000000f1f1ff

def z181 : W := mkw 0x307049266ebdbdb8 0x0c1c12499baf6f6e 0xfef0cf3e3fffffff 0xffbc33cf8fffffff

def z182 : W := mkw 0x8444fc0db036c001 0xa1113f036c0db000 0xa400fc0ff03fc000 0x29003f03fc0ff000

def z183 : W := mkw 0x440202d990000001 0x110080b664000000 0x000000c1c0000000 0x0000003070000000

def z184 : W := mkw 0x8b8db4000b664000 0xa2e36d0002d99000 0x010f300003070000 0x0043cc0000c1c000

def z185 : W := mkw 0x88dd5c000ff6c000 0xa237570003fdb000 0x28ff0c000fffc000 0xca3fc30003fff000

def z186 : W := mkw 0x442203fdf0010355 0x110880ff7c0040d5 0x540003fff00007fc 0x150000fffc0001ff

def z187 : W := mkw 0x2700a2894a252510 0x09c028a252894944 0x010030c1c3070700 0x00400c3070c1c1c0

def z188 : W := mkw 0x187149262fd8bee8 0x461c52498bf62fba 0xfef0cf3e3ff8ffff 0xffbc33cf8ffe3fff

def z189 : W := mkw 0x10704926649999b8 0x041c12499926666e 0xfff0ffffffffffff 0xfffc3fffffffffff

def z190 : W := mkw 0xe7effffffb6f6f75 0x39fbfffffedbdbdd 0xffffffffffffffff 0xffffffffffffffff

def z191 : W := mkw 0x081000000e803480 0x4204000003a00d20 0x000000000c003800 0x0000000003000e00

def z192 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0xa300f0000f3f0003 0x68c03c0003cfc000

def z193 : W := mkw 0x4bbba3f00fe436c0 0x52eee8fc03f90db0 0xfbfff3f00fff3fc3 0xfefffcfc03ffcff0

def z194 : W := mkw 0xc4ee5ffdb0000001 0x313b97ff6c000000 0x4cff0ffff0000000 0x933fc3fffc000000

def z195 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x0bfff3cfc0000001 0x02fffcf3f0000000

def z196 : W := mkw 0xcfdffed99ff6c001 0xb3f7ffb667fdb000 0xabfffcc1cfffc003 0xeaffff3073fff000

def z197 : W := mkw 0x10300122049898a8 0x040c00488126262a 0x7af003300cf8f8ff 0xdebc00cc033e3e3f

def z198 : W := mkw 0x402203f0d00137d4 0x500880fc34004df5 0x540003f1f0003ffc 0x150000fc7c000fff

def z199 : W := mkw 0xcbf8eba00eb4b480 0xf2fe3ae803ad2d20 0x0af0c3000c383801 0x02bc30c0030e0e00

def z200 : W := mkw 0x5bfb4bf62fd8bee8 0x56fed2fd8bf62fba 0x5bffc3fe0ff83fc3 0xd6fff0ff83fe0ff0

def z201 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x3af0c30e0cf8f8fd 0x4ebc30c3833e3e3f

def z202 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xa500f0cfc33f0730 0x29403c33f0cfc1cc

def z203 : W := mkw 0x181100020ffed8a8 0x8604400083ffb62a 0x300000000ffff8fc 0x4c00000003fffe3f

def z204 : W := mkw 0x87ccfe8900000000 0x21f33fa240000000 0xcfffffcfc0000003 0xb3fffff3f0000000

def z205 : W := mkw 0x83ccfc000a240000 0x20f33f0002890000 0xabfffc000f3f0003 0xeaffff0003cfc000

def z206 : W := mkw 0x53fa4bf6249898a8 0x14fe92fd8926262a 0xffffcffe3cf8f8ff 0xfffff3ff8f3e3e3f

def z207 : W := mkw 0x0000000040010110 0x0000000010004044 0xf5003cf1f3c7c7fe 0xfd400f3c7cf1f1ff

def z208 : W := mkw 0x8004b40000264000 0xa0012d0000099000 0x0000300000070000 0x00000c000001c000

def z209 : W := mkw 0x2400a00b402d0930 0x09002802d00b424c 0xf600f30fcc3f3833 0x7d803cc3f30fce0c

def z210 : W := mkw 0xc78eb6d990000001 0x31e3adb664000000 0x010f30c1c0000000 0x0043cc3070000000

def z211 : W := mkw 0x0070492424801080 0x001c124909200420 0xdef0cf3e3cc038c3 0xf7bc33cf8f300e30

def z212 : W := mkw 0x43aa03f0000036c0 0x50ea80fc00000db0 0x5bff03f000003fc3 0x96ffc0fc00000ff0

def z213 : W := mkw 0x0060492420000000 0x0018124908000000 0x0af0c30e00000001 0x02bc30c380000000

def z214 : W := mkw 0x83c8e80000000000 0x20f23a0000000000 0x0af0c00000000001 0x02bc300000000000

def z215 : W := mkw 0x081000000eb48000 0x8204000003ad2000 0x000000000c380000 0x00000000030e0000

def z216 : W := mkw 0xc78eb6d990000001 0x31e3adb664000000 0xc70ff3cfc0000003 0x31c3fcf3f0000000

def z217 : W := mkw 0x0070492424908000 0x001c124909242000 0xeef0cf3e3cf8c003 0xfbbc33cf8f3e3000

def z218 : W := mkw 0x0307b450db674354 0x00c1ed1436d9d0d5 0xf70ffcf1ffffc7ff 0xfdc3ff3c7ffff1ff

def z219 : W := mkw 0x0007145091424244 0x0001c51424509091 0xc50f3cf1f0c0c0ce 0xb143cf3c7c303033

def z220 : W := mkw 0xcffffffdffc377d5 0x73ffffff7ff0ddf5 0xffffffffffc7ffff 0xfffffffffff1ffff

def z221 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x3200c30e0f3f3f31 0x4c8030c383cfcfcc

def z222 : W := mkw 0x0811000005c012c0 0x42044000017004b0 0x0000000000c000c0 0x0000000000300030

def z223 : W := mkw 0x40220174b0000001 0x1008805d2c000000 0x0000003030000000 0x0000000c0c000000

def z224 : W := mkw 0x1070492424909088 0x041c124909242422 0x08f0000000000000 0x023c000000000000

def z225 : W := mkw 0x1770ebaf249898a8 0x05dc3aebc926262a 0xfff0fffffcf8f8ff 0xfffc3fffff3e3e3f

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x510000c003000702 0x5440003000c001c0

def z227 : W := mkw 0x4b8f16d0db436754 0x52e3c5b436d0d9d5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z228 : W := mkw 0x54724bffb49898a9 0x151c92ffed26262a 0xfef0cffffcf8f8ff 0xffbc33ffff3e3e3f

def z229 : W := mkw 0x0006145090000000 0x0001851424000000 0x010f30c1c0000000 0x0043cc3070000000

def z230 : W := mkw 0x8bcdfc000b76c000 0xa2f37f0002ddb000 0xa10ffc00033fc000 0x2843ff0000cff000

def z231 : W := mkw 0x10100002049898a8 0x040400008126262a 0x300000000cf8f8fc 0x4c000000033e3e3f

def z232 : W := mkw 0x10775d74f5d3d3dc 0x041dd75d3d74f4f7 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z233 : W := mkw 0xcffffffdbfc00001 0x33ffffff6ff00000 0xcfffffffffc00003 0xf3fffffffff00000

def z234 : W := mkw 0x0002005000000000 0x0000801400000000 0x410f00f000000002 0x9043c03c00000000

def z235 : W := mkw 0xcffffffdfff7c355 0xb3ffffff7ffdf0d5 0xffffffffffffc7ff 0xfffffffffffff1ff

def z236 : W := mkw 0x4b8b02d00b402640 0x52e2c0b402d00990 0x510f00f003c007c2 0xd443c03c00f001f0

def z237 : W := mkw 0x2730a3ab4ead3db0 0x09cc28ead3ab4f6c 0xfff0f3ffcfff3ff3 0xfffc3cfff3ffcffc

def z238 : W := mkw 0x93fcfd26249898a8 0x24ff3f498926262a 0xffffff3e3cf8f8ff 0xffffffcf8f3e3e3f

def z239 : W := mkw 0xd7fffffff5dbdbfd 0x35fffffffd76f6ff 0xffffffffffffffff 0xffffffffffffffff

def z240 : W := mkw 0x8bdffc50dff7c354 0xa2f7ff1437fdf0d5 0xabfffcc1cfffc703 0xeaffff3073fff1c0

def z241 : W := mkw 0x0003005001400240 0x0000c01400500090 0x000f003000c000c0 0x8003c00c00300030

def z242 : W := mkw 0xc7ecffad20000001 0x31fb3feb48000000 0x8bffff0e00000003 0xa2ffffc380000000

def z243 : W := mkw 0x5bff5ff6ffdbfffc 0x56ffd7fdbff6ffff 0xffffffffffffffff 0xffffffffffffffff

def z244 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xa50f3cc1f307c73c 0x2943cf307cc1f1cf

def z245 : W := mkw 0x43ea4bf420000000 0x10fa92fd08000000 0xcfffcffe30000003 0xb3fff3ff8c000000

def z246 : W := mkw 0xc7fefffdb4908001 0x31ffbfff6d242000 0xeffffffffcf8c003 0xfbffffffff3e3000

def z247 : W := mkw 0xc7effffdb1424245 0x31fbffff6c509091 0xcffffffff0c0c0cf 0xb3fffffffc303033

def z248 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x5af0c33e0cf838c3 0xd6bc30cf833e0e30

def z249 : W := mkw 0x83cefc5090000000 0x20f3bf1424000000 0xcffffcf1f0000003 0xb3ffff3c7c000000

def z250 : W := mkw 0x400202d000002640 0x500080b400000990 0x000000c000000700 0x00000030000001c0

def z251 : W := mkw 0xc4eefd7db0000001 0x313bbf5f6c000000 0x8cfffc3ff0000000 0xa33fff0ffc000000

def z252 : W := mkw 0x2000000240092d30 0x0800000090024b4c 0x1000000000003f30 0x0400000000000fcc

def z253 : W := mkw 0x2f11a28b4fffed30 0x8bc468a2d3fffb4c 0xf700f3cfcfffff33 0x7dc03cf3f3ffffcc

def z254 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x0affcc000cf8c001 0x82bff300033e3000

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z256 : W := mkw 0x6fbfb7fbdfef7ff4 0x5befedfef7fbdffd 0xffffffffffffffff 0xffffffffffffffff

def z257 : W := mkw 0x0040480000000000 0x0010120000000000 0x8af0cc0000000003 0xa2bc330000000000

def z258 : W := mkw 0x2400028b40092d30 0x090000a2d0024b4c 0xf600c3cfcc383f33 0x7d8030f3f30e0fcc

def z259 : W := mkw 0xc7eefffdba002401 0x31fbbfff6e800900 0xdfffffffff003f03 0xf7ffffffffc00fc0

def z260 : W := mkw 0x281100024fffed30 0x8a04400093fffb4c 0x300000000fffff30 0x4c00000003ffffcc

def z261 : W := mkw 0x0005140041434354 0x000145001050d0d5 0xb10f3c0003c7c7fe 0xec43cf0000f1f1ff

def z262 : W := mkw 0x2400a28b402d2d30 0x090028a2d00b4b4c 0xf400f3cfc03f3f30 0x3d003cf3f00fcfcc

def z263 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x09ff00f003c007c0 0x827fc03c00f001f0

def z264 : W := mkw 0x0003005001400240 0x0000c01400500090 0x510f00f003c007c2 0xd443c03c00f001f0

def z265 : W := mkw 0x4bbf17f0dfc377d4 0x52efc5fc37f0ddf5 0xffff3ff1ffc7ffff 0xffffcffc7ff1ffff

def z266 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xa600f30fcc3f3831 0x29803cc3f30fce0c

def z267 : W := mkw 0xc7e8ebad20000001 0x31fa3aeb48000000 0x0af0c30e00000001 0x02bc30c380000000

def z268 : W := mkw 0x0b99a0000fe40000 0x02e6680003f90000 0xabfff0000fff0003 0xeafffc0003ffc000

def z269 : W := mkw 0x0000000040010110 0x0000000010004044 0x3000000003070730 0x4c00000000c1c1cc

def z270 : W := mkw 0xc7eaebfd20000001 0x31fabaff48000000 0x4bffc3fe00000003 0x92fff0ff80000000

def z271 : W := mkw 0xefffffffffffed31 0xbbfffffffffffb4c 0xffffffffffffff33 0xffffffffffffffcc

def z272 : W := mkw 0x48bb01700fc036c0 0x522ec05c03f00db0 0x18ff00300fc03fc0 0xc63fc00c03f00ff0

def z273 : W := mkw 0x8bddfc004ff7c110 0xa2f77f0013fdf044 0xfffffcc1cfffc733 0xffffff3073fff1cc

def z274 : W := mkw 0x8fddfe890ff6c000 0xa3f77fa243fdb000 0xefffffcfcfffc003 0xfbfffff3f3fff000

def z275 : W := mkw 0x4bbb03f04fc137d0 0x52eec0fc13f04df4 0xffff33f1cfc73ff3 0xffffccfc73f1cffc

def z276 : W := mkw 0x3440e80f603d8938 0x0d103a03d80f624e 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z277 : W := mkw 0x00575c50d5d3c354 0x0015d7143574f0d5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z278 : W := mkw 0x5bbb03f20fd8bee8 0x56eec0fc83f62fba 0x7bff03f00ff8ffff 0xdeffc0fc03fe3fff

def z279 : W := mkw 0x200000020a2c2c20 0x08000000828b0b08 0x000000000c383800 0x00000000030e0e00

def z280 : W := mkw 0x3710a28b4ebdbdb8 0x0dc428a2d3af6f6e 0xf700f3cfcfffffff 0x7dc03cf3f3ffffff

def z281 : W := mkw 0x0050480004908000 0x0014120001242000 0xfef0cc303cf8c0ff 0xffbc330c0f3e303f

def z282 : W := mkw 0x888d140001424000 0xa223450000509000 0x000f000000000000 0x0003c00000000000

def z283 : W := mkw 0x0007145091424244 0x0001c51424509091 0x000f000000000000 0x0003c00000000000

def z284 : W := mkw 0xafddfc0b4fffc930 0xabf77f02d3fff24c 0xaffffc0fcfffc033 0xebffff03f3fff00c

def z285 : W := mkw 0x0007145091400240 0x0001c51424500090 0xd50f3cf1f3c007c2 0xf543cf3c7cf001f0

def z286 : W := mkw 0x0b9f1450dfc34354 0x02e7c51437f0d0d5 0xffff3cf1ffc7c7ff 0xffffcf3c7ff1f1ff

def z287 : W := mkw 0x0002005090000244 0x0000801424000091 0x00000030300000cc 0x0000000c0c000033

def z288 : W := mkw 0x43af17f0d1434354 0x10ebc5fc3450d0d5 0xffff3ff1f3c7c7ff 0xffffcffc7cf1f1ff

def z289 : W := mkw 0x030716d0db436754 0x00c1c5b436d0d9d5 0xf70f3ff1ffc7ffff 0xfdc3cffc7ff1ffff

def z290 : W := mkw 0x0b9900000ff6c000 0x82e6400003fdb000 0x2bff00000fffc003 0xcaffc00003fff000

def z291 : W := mkw 0xcf8fb6d99b664001 0xb3e3edb666d99000 0x010f30c1c3070000 0x0043cc3070c1c000

def z292 : W := mkw 0x4bbb03f00fc00000 0x12eec0fc03f00000 0x4bff03f00fc00003 0xd2ffc0fc03f00000

def z293 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x0300f3cfcf3f3f01 0x00c03cf3f3cfcfc0

def z294 : W := mkw 0x7ffbebff6ffdbff8 0x5ffefaffdbff6ffe 0xffffffffffffffff 0xffffffffffffffff

def z295 : W := mkw 0x8054fc0004b6c000 0xa0153f00012db000 0xaaf0fc000cffc003 0xeabc3f00033ff000

def z296 : W := mkw 0x88ddfc0005f6c000 0xa2377f00017db000 0xa8fffc0000ffc000 0xaa3fff00003ff000

def z297 : W := mkw 0x4bbf17f09fc276c4 0x52efc5fc27f09db1 0x5bff0ff03fc0ffcf 0xd6ffc3fc0ff03ff3

def z298 : W := mkw 0x43ab03f001400240 0x10eac0fc00500090 0x5bff03f003c007c3 0xd6ffc0fc00f001f0

def z299 : W := mkw 0x0000000040010110 0x0000000010004044 0x010030c1c3070700 0x00400c3070c1c1c0

def z300 : W := mkw 0x88d8480004908000 0xa236120001242000 0x08f0000000000000 0x023c000000000000

def z301 : W := mkw 0x0350e8000eb48000 0x00d43a0003ad2000 0xabf0fc000fffc003 0xeafc3f0003fff000

def z302 : W := mkw 0x9bfdfd262ffed8a8 0xa6ff7f498bffb62a 0xffffff3e3ffff8ff 0xffffffcf8ffffe3f

def z303 : W := mkw 0x10765d76b49898a8 0x041d975dad26262a 0xfffffffffcf8f8ff 0xffffffffff3e3e3f

def z304 : W := mkw 0x0060492420000000 0x0018124908000000 0xfef0cf3e30c0c0ff 0xffbc33cf8c30303f

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0xa100300003070002 0x68400c0000c1c000

def z306 : W := mkw 0x4bb803a00e803480 0x52ee00e803a00d20 0x5bf003c00f003f03 0x56fc00f003c00fc0

def z307 : W := mkw 0xc08e145090000001 0x3023851424000000 0x000f000000000000 0x0003c00000000000

def z308 : W := mkw 0x2760ebaf6a2d2d30 0x09d83aebda8b4b4c 0xfff0ffffff3f3f33 0xfffc3fffffcfcfcc

def z309 : W := mkw 0x483303f00fc036c0 0x520cc0fc03f00db0 0x500003f00fc03fc0 0x540000fc03f00ff0

def z310 : W := mkw 0x00061450d0010110 0x0001851434004044 0xf50f3cf1f3070732 0xfd43cf3c7cc1c1cc

def z311 : W := mkw 0x83cffc50d1434354 0x20f3ff143450d0d5 0xfffffcf1f3c7c7ff 0xffffff3c7cf1f1ff

def z312 : W := mkw 0x0004140090000000 0x0001050024000000 0x84003c01f0000000 0x21000f007c000000

def z313 : W := mkw 0x200000004a252510 0x0800000012894944 0x0000000003070700 0x0000000000c1c1c0

def z314 : W := mkw 0x0010000004801080 0x0004000001200420 0x100000000cc038c0 0x4400000003300e30

def z315 : W := mkw 0x1070492424909088 0x041c124909242422 0xfcf00c3030c0c0fe 0xff3c030c0c30303f

def z316 : W := mkw 0x10745d26f49bd9bc 0x041d1749bd26f66f 0xfef0ff3ffcfff8ff 0xffbc3fcfff3ffe3f

def z317 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x550f30f1f30707fc 0x1543cc3c7cc1c1ff

def z318 : W := mkw 0x0010000004908000 0x0004000001242000 0x200000000cf8c000 0x48000000033e3000

def z319 : W := mkw 0x00051400d1434114 0x000145003450d045 0xa50f3c01f3c7c03e 0xe943cf007cf1f00f

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0xc4000c3030000002 0xb100030c0c000000

def z321 : W := mkw 0x6bbb03f24fed3ff0 0x5aeec0fc93fb4ffc 0x7bff03f00fff3ff3 0xdeffc0fc03ffcffc

def z322 : W := mkw 0xabddfc024fffed30 0xaaf77f0093fffb4c 0xbbfffc000fffff33 0xeeffff0003ffffcc

def z323 : W := mkw 0x230002824a2d2d30 0x08c000a0928b4b4c 0x730003c00f3f3f33 0x5cc000f003cfcfcc

def z324 : W := mkw 0x0020012000001080 0x0008004800000420 0x50000330000038c0 0x140000cc00000e30

def z325 : W := mkw 0xdfffffffbffed8a9 0xb7ffffffefffb62a 0xfffffffffffff8ff 0xfffffffffffffe3f

def z326 : W := mkw 0x10200126200818a8 0x040800498802062a 0xf600c33e3c3838ff 0x7d8030cf8f0e0e3f

def z327 : W := mkw 0xeffffffb4ffffff0 0xfbfffffed3fffffc 0xffffffffcffffff3 0xfffffffff3fffffc

def z328 : W := mkw 0x8bdd5c000fd2c000 0xa2f7570003f4b000 0x0bff0c000fc0c003 0xc2ffc30003f03000

def z329 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x550033cfc3073f30 0x15400cf3f0c1cfcc

def z330 : W := mkw 0x50724bf62498bee8 0x541c92fd89262fba 0xfef0cffe3cf8ffff 0xffbc33ff8f3e3fff

def z331 : W := mkw 0x4fbb03fdbfc036c1 0x53eec0ff6ff00db0 0x5fff03ffffc03fc3 0xd7ffc0fffff00ff0

def z332 : W := mkw 0x00030050d1434354 0x0000c0143450d0d5 0x740000f1f3c7c7fc 0x5d00003c7cf1f1ff

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000c0000c0c002 0xe800030000303000

def z334 : W := mkw 0x5bfb4bf42fd0b6c8 0x56fed2fd0bf42db2 0x5bff0ff03fc0ffcf 0xd6ffc3fc0ff03ff3

def z335 : W := mkw 0x432203f00a0036c0 0x50c880fc02800db0 0x530003f00f003fc3 0x54c000fc03c00ff0

def z336 : W := mkw 0x2700a2890a242400 0x09c028a242890900 0x0000000000000000 0x0000000000000000

def z337 : W := mkw 0x3740ea8f6a3dad38 0x0dd03aa3da8f6b4e 0xf700ffcfff3fff3f 0x7dc03ff3ffcfffcf

def z338 : W := mkw 0x00300122048818a0 0x000c004881220628 0xfef0c33e0cf838f3 0xffbc30cf833e0e3c

def z339 : W := mkw 0x8bd9e8000ff6c000 0xa2f67a0003fdb000 0x2af0c0000fffc001 0x4abc300003fff000

def z340 : W := mkw 0x80445c000012c000 0xa01117000004b000 0x00000c000000c000 0x0000030000003000

def z341 : W := mkw 0xc7eefffdb036c001 0xb1fbbfff6c0db000 0xeffffffff03fc003 0xbbfffffffc0ff000

def z342 : W := mkw 0x0001000041434354 0x000040001050d0d5 0x0000000003070700 0x0000000000c1c1c0

def z343 : W := mkw 0xafdffedbdfffef74 0xabf7ffb6f7fffbdd 0xffffffffffffffff 0xffffffffffffffff

def z344 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x540f0cf1f0c0c7fc 0x9503c33c7c3031ff

def z345 : W := mkw 0xc7fefffdb4801081 0x31ffbfff6d200420 0xdffffffffcc038c3 0xf7ffffffff300e30

def z346 : W := mkw 0x48bf1570d5c353d4 0x522fc55c3570d4f5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z347 : W := mkw 0x0b11a0000ff6c000 0x82c4680003fdb000 0xa300f0000fffc003 0x68c03c0003fff000

def z348 : W := mkw 0x48bb03f005c036c0 0x522ec0fc01700db0 0x58ff03f000c03fc0 0x963fc0fc00300ff0

def z349 : W := mkw 0xc7ecffadb0000001 0x31fb3feb6c000000 0x8ef0ff0ff0000001 0x23bc3fc3fc000000

def z350 : W := mkw 0x0007145091424244 0x0001c51424509091 0xf40f0c3030c0c0fe 0xfd03c30c0c30303f

def z351 : W := mkw 0x403203f0048036c0 0x500c80fc01200db0 0x5af003f00cc03fc3 0xd6bc00fc03300ff0

def z352 : W := mkw 0xcbfffff00fc036c0 0x72fffffc03f00db0 0xdbfffff00fc03fc3 0xf6fffffc03f00ff0

def z353 : W := mkw 0x0300a2800a242400 0x00c028a002890900 0xf300f3c00f3f3f03 0x7cc03cf003cfcfc0

def z354 : W := mkw 0x48bb017005c012c0 0x522ec05c017004b0 0x59ff00f003c007c2 0xd67fc03c00f001f0

def z355 : W := mkw 0x4b9b02d00fc036c0 0x52e6c0b403f00db0 0x110f00c00fc03fc0 0x4443c03003f00ff0

def z356 : W := mkw 0x88dd5c0005d2c000 0xa23757000174b000 0xaaffcc000cf8c003 0xeabff300033e3000

def z357 : W := mkw 0x0b9902800fc02400 0x02e640a003f00900 0x5bff03c00fc03f03 0xd6ffc0f003f00fc0

def z358 : W := mkw 0x1070492424909088 0x041c124909242422 0xcef0cf3e30c0c0cf 0xb3bc33cf8c303033

def z359 : W := mkw 0xc0ef5d74b1424245 0x303bd75d2c509091 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z360 : W := mkw 0x085148000ff6c000 0x8214520003fdb000 0xaaf0cc000fffc003 0xeabc330003fff000

def z361 : W := mkw 0x83cdfc0001424000 0x20f37f0000509000 0xabfffc0003c7c003 0xeaffff0000f1f000

def z362 : W := mkw 0x0005140041434110 0x000145001050d044 0xf50f3cc1c3c7c732 0xfd43cf3070f1f1cc

def z363 : W := mkw 0x0060492620080820 0x0018124988020208 0xfef0cf3e3c383833 0xffbc33cf8f0e0e0c

def z364 : W := mkw 0xcfbfb7f99fc036c1 0x73efedfe67f00db0 0x5bff33f1cfc03fc3 0xd6ffccfc73f00ff0

def z365 : W := mkw 0x48bf157095c252c4 0x522fc55c257094b1 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z366 : W := mkw 0x0000000040034114 0x000000001000d045 0x200000000007c03c 0x080000000001f00f

def z367 : W := mkw 0x4bba03f00e803480 0x52ee80fc03a00d20 0x4bff03f00c003803 0x92ffc0fc03000e00

def z368 : W := mkw 0xc7eaebfdb0000001 0x31fabaff6c000000 0x4ef0c3fff0000001 0x13bc30fffc000000

def z369 : W := mkw 0x1020012420001088 0x0408004908000422 0x00000030300000cc 0x0000000c0c000033

def z370 : W := mkw 0x3470e92f64bd99b8 0x0d1c3a4bd92f666e 0xfef0ff3ffcfff8ff 0xffbc3fcfff3ffe3f

def z371 : W := mkw 0x6722a3fffa2d2d31 0x19c8a8fffe8b4b4c 0xf700f3ffff3f3f33 0x7dc03cffffcfcfcc

def z372 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xaef0cf0e3c38f83d 0x2bbc33c38f0e3e0f

def z373 : W := mkw 0x0030012004801080 0x000c004801200420 0x0af003000c003801 0x02bc00c003000e00

def z374 : W := mkw 0x0000a00000240000 0x0000280000090000 0xa000f000003f0000 0x28003c00000fc000

def z375 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x310030c1cf3f3f30 0x4c400c3073cfcfcc

def z376 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x09ff3cf1f0000000 0x827fcf3c7c000000

def z377 : W := mkw 0x4bbb03f005c012c0 0x52eec0fc017004b0 0x4bff03f000c000c3 0x92ffc0fc00300030

def z378 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x0bfff0000f3f0001 0x02fffc0003cfc000

def z379 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xacf0cc3e30f8c0fc 0xab3c330f8c3e303f

def z380 : W := mkw 0x3770ebaf2ebcbca8 0x0ddc3aebcbaf2f2a 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z381 : W := mkw 0x2400028b00082c20 0x090000a2c0020b08 0x0000030e00003800 0x000000c380000e00

def z382 : W := mkw 0x0030012004801080 0x000c004801200420 0x08f0003000c000c0 0x823c000c00300030

def z383 : W := mkw 0xc0ef5d74f1434355 0x303bd75d3c50d0d5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z384 : W := mkw 0x0400000db0000001 0x010000036c000000 0x0400000ff0000000 0x01000003fc000000

def z385 : W := mkw 0x442003ad20000001 0x110800eb48000000 0x0000030e00000000 0x000000c380000000

def z386 : W := mkw 0xcbfbebf00ff4b6c0 0xf2fefafc03fd2db0 0x5bffc3f00ff83fc3 0xd6fff0fc03fe0ff0

def z387 : W := mkw 0xd0fe5d74b4909089 0x343f975d2d242422 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z388 : W := mkw 0xc3eefff000000000 0x30fbbffc00000000 0xcbfffff000000003 0xb2fffffc00000000

def z389 : W := mkw 0x2400a00b002c0820 0x09002802c00b0208 0x0000c00e00380000 0x00003003800e0000

def z390 : W := mkw 0xcbfdffa00ff6f480 0xf2ff7fe803fdbd20 0xabffff000ffff803 0xeaffffc003fffe00

def z391 : W := mkw 0x2700a28b0a2c2c20 0x09c028a2c28b0b08 0xa300f30e0f3f3803 0x68c03cc383cfce00

def z392 : W := mkw 0x080100000b664000 0x8200400002d99000 0x0000000003070000 0x0000000000c1c000

def z393 : W := mkw 0x642203fb40093ff0 0x590880fed0024ffc 0x540003ffc0003ff0 0x150000fff0000ffc

def z394 : W := mkw 0xe7eefffff0092d31 0x39fbbffffc024b4c 0xdffffffff0003f33 0xb7fffffffc000fcc

def z395 : W := mkw 0x88df5c50d5d3c354 0xa237d7143574f0d5 0xfdff3cf1f3c7c7fe 0xff7fcf3c7cf1f1ff

def z396 : W := mkw 0x402003a000003480 0x500800e800000d20 0x0000030000003800 0x000000c000000e00

def z397 : W := mkw 0x10724976f4999bfc 0x041c925dbd2666ff 0xfef0cffffcf8ffff 0xffbc33ffff3e3fff

def z398 : W := mkw 0x0002005090000000 0x0000801424000000 0x440000f1f0000000 0x1100003c7c000000

def z399 : W := mkw 0xc78fb6d9d1434355 0x31e3edb67450d0d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z400 : W := mkw 0x83ecfd2420000000 0x20fb3f4908000000 0xcfffff3e30000003 0xb3ffffcf8c000000

def z401 : W := mkw 0x0300a00000000000 0x00c0280000000000 0x8300f00000000003 0x20c03c0000000000

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000003000c000c2 0xd400000c00300030

def z403 : W := mkw 0x4bb903a00fc03480 0x52ee40e803f00d20 0x0bff03000fc03803 0xc2ffc0c003f00e00

def z404 : W := mkw 0x0b9b00500fc00240 0x02e6c01403f00090 0x5bff00f00fc007c3 0xd6ffc03c03f001f0

def z405 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xa10f3cc1c3c7c702 0xe843cf3070f1f1c0

def z406 : W := mkw 0x00041400d0034114 0x000105003400d045 0xf5003cc1f307c73e 0x7d400f307cc1f1cf

def z407 : W := mkw 0x98fd5d2625dad8a8 0xa63f57498976b62a 0xfeffcf3e3cf8f8ff 0xffbff3cf8f3e3e3f

def z408 : W := mkw 0x10100002049898a8 0x040400008126262a 0xf600c30e0cf8f8ff 0x7d8030c3833e3e3f

def z409 : W := mkw 0x10504802049898a8 0x041412008126262a 0xbaf0cc000cf8f8ff 0xeebc3300033e3e3f

def z410 : W := mkw 0xc7eefffdf0010111 0x31fbbfff7c004044 0xfffffffff3070733 0xfffffffffcc1c1cc

def z411 : W := mkw 0x8bddfc020ffec820 0xa2f77f0083ffb208 0xffffff0e0ffff833 0xffffffc383fffe0c

def z412 : W := mkw 0x83ccfc000036c000 0xa0f33f00000db000 0xabfffc00003fc003 0xaaffff00000ff000

def z413 : W := mkw 0x030302d00b402640 0x00c0c0b402d00990 0x530f03f00fc03fc3 0xd4c3c0fc03f00ff0

def z414 : W := mkw 0xc0ee5d74b0000001 0x303b975d2c000000 0xcdff3cf1f0000002 0xb37fcf3c7c000000

def z415 : W := mkw 0x0060492420000000 0x0018124908000000 0x08f00c3030000000 0x823c030c0c000000

def z416 : W := mkw 0x0020012420000000 0x0008004908000000 0x4400033e30000000 0x110000cf8c000000

def z417 : W := mkw 0x00051400d1434354 0x000145003450d0d5 0xb4003c01f3c7c7fc 0x6d000f007cf1f1ff

def z418 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xfffffffff0c0c0ff 0xfffffffffc30303f

def z419 : W := mkw 0x838cb40000000000 0x20e32d0000000000 0x010f300000000000 0x0043cc0000000000

def z420 : W := mkw 0x00061450d0034114 0x000185143400d045 0xe50f3cf1f007c03e 0xb943cf3c7c01f00f

def z421 : W := mkw 0x2702a2dbda2d2f74 0x09c0a8b6f68b4bdd 0xf700f3ffff3f3fff 0x7dc03cffffcfcfff

def z422 : W := mkw 0x0000000040010354 0x00000000100040d5 0x10000000000007fc 0x04000000000001ff

def z423 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xcef0cf3e3c383803 0xb3bc33cf8f0e0e00

def z424 : W := mkw 0x0001000041434354 0x000040001050d0d5 0xf4000c3033c7c7fe 0xfd00030c0cf1f1ff

def z425 : W := mkw 0x0400a00900000000 0x0100280240000000 0x8400f00fc0000000 0x21003c03f0000000

def z426 : W := mkw 0x2300a0024a2d2d30 0x08c02800928b4b4c 0xb300f0000f3f3f33 0x6cc03c0003cfcfcc

def z427 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xa40f3c31f0c7c0fc 0xa903cf0c7c31f03f

def z428 : W := mkw 0x3777fffffffffffc 0x0dddffffffffffff 0xffffffffffffffff 0xffffffffffffffff

def z429 : W := mkw 0x442617fdb0000001 0x110985ff6c000000 0xc50f3ffff0000002 0xb143cffffc000000

def z430 : W := mkw 0xc466fffdb0000001 0x3119bfff6c000000 0xc400fffff0000000 0x31003ffffc000000

def z431 : W := mkw 0x10775d74b5d2d2cc 0x041dd75d2d74b4b3 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z432 : W := mkw 0x0305b4000b664000 0x00c16d0002d99000 0xa30ffc000fffc003 0xe8c3ff0003fff000

def z433 : W := mkw 0x2707b6dbdb6f6f74 0x09c1edb6f6dbdbdd 0xf70ff3cfcf3f3f33 0x7dc3fcf3f3cfcfcc

def z434 : W := mkw 0x00000000000036c0 0x4000000000000db0 0x1000000000003fc0 0x0400000000000ff0

def z435 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x5600c3cfcc383f31 0x158030f3f30e0fcc

def z436 : W := mkw 0x1040480620188828 0x041012018806220a 0xf600cf0e3c38f83f 0x7d8033c38f0e3e0f

def z437 : W := mkw 0x0700a28900000000 0x01c028a240000000 0x0200c30e00000001 0x008030c380000000

def z438 : W := mkw 0xc8ff5d74b5c012c1 0x723fd75d2d7004b0 0x08ff0c3030c000c0 0x823fc30c0c300030

def z439 : W := mkw 0x2707b6d9db676754 0x09c1edb676d9d9d5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z440 : W := mkw 0x10475c56f15bcb7c 0x0411d715bc56f2df 0xf50ffcfff3ffc7fe 0xfd43ff3ffcfff1ff

def z441 : W := mkw 0xc788a28900000001 0x31e228a240000000 0x0000000000000000 0x0000000000000000

def z442 : W := mkw 0x8404b40990000001 0x21012d0264000000 0x00003001c0000000 0x00000c0070000000

def z443 : W := mkw 0xc3eefd74b0000001 0x30fbbf5d2c000000 0x8bfffc3030000003 0xa2ffff0c0c000000

def z444 : W := mkw 0x1040480620188828 0x041012018806220a 0xf400cc3e30f8c0fe 0xfd00330f8c3e303f

def z445 : W := mkw 0x301000024ebdbdb8 0x0c04000093af6f6e 0x300000000ffffffc 0x4c00000003ffffff

def z446 : W := mkw 0xcbdffed00ff6e640 0xf2f7ffb403fdb990 0xabfffcc00fffc703 0xeaffff3003fff1c0

def z447 : W := mkw 0x4bbf17f00fc276c0 0x52efc5fc03f09db0 0xfbff3ff00fc7ffc3 0xfeffcffc03f1fff0

def z448 : W := mkw 0x2404b40bd02f4934 0x09012d02f40bd24d 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z449 : W := mkw 0x8440e80d20000001 0x21103a0348000000 0x0000c00e00000000 0x0000300380000000

def z450 : W := mkw 0xcbbfb7f00fe676c0 0xf2efedfc03f99db0 0x5bff33f00fc73fc3 0xd6ffccfc03f1cff0

def z451 : W := mkw 0x0050480204988820 0x0014120081262208 0xfef0cf0e0cf8f833 0xffbc33c3833e3e0c

def z452 : W := mkw 0x402203f000000000 0x100880fc00000000 0x400003f000000000 0x100000fc00000000

def z453 : W := mkw 0x00030050d1410354 0x0000c014345040d5 0x550f00f1f3c007fe 0xd543c03c7cf001ff

def z454 : W := mkw 0x08171450dfc377d4 0x4205c51437f0ddf5 0xf50f3cf1ffc7fffe 0xfd43cf3c7ff1ffff

def z455 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x0affcf3e30000001 0x82bff3cf8c000000

def z456 : W := mkw 0x88dd5c0005d2c000 0xa23757000174b000 0xa9ff3c0003c7c002 0xea7fcf0000f1f000

def z457 : W := mkw 0x0300a0020a2c0820 0x00c02800828b0208 0xf700f30e0f3f3833 0x7dc03cc383cfce0c

def z458 : W := mkw 0x4bbb03f20fc83ee0 0x52eec0fc83f20fb8 0xffffc3fe0ff83ff3 0xfffff0ff83fe0ffc

def z459 : W := mkw 0xd7eeffffb00818a9 0x35fbbfffec02062a 0xdffffffff00038ff 0xb7fffffffc000e3f

def z460 : W := mkw 0x4b8f16d0db436754 0x52e3c5b436d0d9d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z461 : W := mkw 0x1010000004909088 0x0404000001242422 0x0000000000c0c0cc 0x0000000000303033

def z462 : W := mkw 0xe7eefffff02d0931 0x39fbbffffc0b424c 0xeffffffff03f0033 0xbbfffffffc0fc00c

def z463 : W := mkw 0xe7e8ebaf6a2d2d31 0x39fa3aebda8b4b4c 0xfff0f3cfcf3f3f33 0x7ffc3cf3f3cfcfcc

def z464 : W := mkw 0x00675d74f1434354 0x0019d75d3c50d0d5 0xfffffffff3c7c7ff 0xfffffffffcf1f1ff

def z465 : W := mkw 0x80cc5c0000000000 0x2033170000000000 0x08ff0c0000000000 0x823fc30000000000

def z466 : W := mkw 0x08171450dff7c354 0x8205c51437fdf0d5 0xf50f3cf1ffffc7fe 0xfd43cf3c7ffff1ff

def z467 : W := mkw 0x2705b68b4b6f6d30 0x09c16da2d2dbdb4c 0xf70fffcfcfffff33 0xfdc3fff3f3ffffcc

def z468 : W := mkw 0x0005140001424000 0x0001450000509000 0x010f300003070000 0x0043cc0000c1c000

def z469 : W := mkw 0x10755d2625dad8a8 0x041d57498976b62a 0xffffff3e3ffff8ff 0xffffffcf8ffffe3f

def z470 : W := mkw 0x2400028b4a2d2d30 0x090000a2d28b4b4c 0x740003cfcf3f3f30 0x5d0000f3f3cfcfcc

def z471 : W := mkw 0x8bd9e8000ff48000 0xa2f67a0003fd2000 0x0bffc0000ff80003 0xc2fff00003fe0000

def z472 : W := mkw 0xe7eeffffba2c2c21 0x39fbbfffee8b0b08 0xcffffffffc383803 0xb3ffffffff0e0e00

def z473 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x510f30f1c3c707c2 0xd443cc3c70f1c1f0

def z474 : W := mkw 0x9bf8e9262ebc98a8 0xa6fe3a498baf262a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z475 : W := mkw 0xc7effffdf1434355 0x31fbffff7c50d0d5 0xcffffffff3070703 0xb3fffffffcc1c1c0

def z476 : W := mkw 0x8446fc5db0000001 0x2111bf176c000000 0xc50ffcfff0000002 0xb143ff3ffc000000

def z477 : W := mkw 0xc0ee5d74b0000001 0x303b975d2c000000 0xceffcf3e30000003 0xb3bff3cf8c000000

def z478 : W := mkw 0x1370e9262ebc98a8 0x04dc3a498baf262a 0xfff0ff3e3ffff8ff 0xfffc3fcf8ffffe3f

def z479 : W := mkw 0xcffffffdb5d2c001 0xb3ffffff6d74b000 0xcffffffff0c0c003 0xb3fffffffc303000

def z480 : W := mkw 0x8bdffc509ff6c244 0xa2f7ff1427fdb091 0xabfffc303fffc0cf 0xeaffff0c0ffff033

def z481 : W := mkw 0xcbfffff0dff7f7d4 0xf2fffffc37fdfdf5 0xfffffff1ffffffff 0xfffffffc7fffffff

def z482 : W := mkw 0x1040480420108008 0x0410120108042002 0x00000c003000c00c 0x000003000c003003

def z483 : W := mkw 0x34704baf6499bdb8 0x0d1c12ebd9266f6e 0xfef0cffffcf8ffff 0xffbc33ffff3e3fff

def z484 : W := mkw 0x2700a28b402d0930 0x09c028a2d00b424c 0xe700f3cfc03f0033 0x39c03cf3f00fc00c

def z485 : W := mkw 0x342003af60093db8 0x0d0800ebd8024f6e 0x540003fff0003ffc 0x150000fffc000fff

def z486 : W := mkw 0xdfffffffbfd8bee9 0x77ffffffeff62fba 0xfffffffffff8ffff 0xfffffffffffe3fff

def z487 : W := mkw 0x8b8db4000b664000 0xa2e36d0002d99000 0xa10f3c0003c7c002 0xe843cf0000f1f000

def z488 : W := mkw 0x8040e80000348000 0xa0103a00000d2000 0x0000c00000380000 0x00003000000e0000

def z489 : W := mkw 0x8444fc0df0034115 0x21113f037c00d045 0xa400fc0ff007c03c 0x29003f03fc01f00f

def z490 : W := mkw 0x0700a28940010110 0x01c028a250004044 0xf700f3cfc3070733 0x7dc03cf3f0c1c1cc

def z491 : W := mkw 0x0388000000000000 0x00e2000000000000 0x0bff000000000003 0x82ffc00000000000

def z492 : W := mkw 0x9bddfc062ffec828 0xa6f77f018bffb20a 0xaffffc0e3fffc03f 0xebffff038ffff00f

def z493 : W := mkw 0xcbff5ff00fd2f6c0 0xf2ffd7fc03f4bdb0 0x5bff0ff00fc0ffc3 0xd6ffc3fc03f03ff0

def z494 : W := mkw 0x20071452db6f6f74 0x0801c514b6dbdbdd 0xf50f3cf1fffffffe 0xfd43cf3c7fffffff

def z495 : W := mkw 0x0b9d14000fc24000 0x02e7450003f09000 0xabff3c000fc7c003 0xeaffcf0003f1f000

def z496 : W := mkw 0x0050480004908000 0x0014120001242000 0x08f00c0000c0c000 0x823c030000303000

def z497 : W := mkw 0x438a02d000000000 0x10e280b400000000 0x010f00c000000000 0x0043c03000000000

def z498 : W := mkw 0x1050480624988828 0x041412018926220a 0xaef0cc0e3cf8c03f 0xebbc33038f3e300f

def z499 : W := mkw 0x0005140001424000 0x0001450000509000 0x000f0c0000c0c000 0x8003c30000303000

def z500 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0x0100300003070000 0x00400c0000c1c000

def z501 : W := mkw 0x83dcfc0004908000 0x20f73f0001242000 0xabfffc000cf8c003 0xeaffff00033e3000

def z502 : W := mkw 0xcffefffdbe803481 0x73ffbfff6fa00d20 0xcffffffffc003803 0xb3ffffffff000e00

def z503 : W := mkw 0x8bddfc004ff7c354 0xa2f77f0013fdf0d5 0xbbfffc000fffc7ff 0xeeffff0003fff1ff

def z504 : W := mkw 0x98fd5d2425d2d088 0xa63f57490974b422 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z505 : W := mkw 0x8b88a0000a240000 0xa2e2280002890000 0x0000000000000000 0x0000000000000000

def z506 : W := mkw 0x4bb903a00fc036c0 0x52ee40e803f00db0 0x1af003000fc03fc1 0x46bc00c003f00ff0

def z507 : W := mkw 0x030002820a082c20 0x00c000a082820b08 0xf700c3ce0f383f33 0x7dc030f383ce0fcc

def z508 : W := mkw 0x9444fc0fb0188829 0x25113f03ec06220a 0xa400fc0ff038c03c 0x29003f03fc0e300f

def z509 : W := mkw 0x0700a2890a240000 0x01c028a242890000 0xe700f3cfcf3f0003 0x79c03cf3f3cfc000

def z510 : W := mkw 0x8bfdfd242ff6c000 0xa2ff7f490bfdb000 0xefffff3e3fffc003 0xfbffffcf8ffff000

def z511 : W := mkw 0x200000024a2d2d30 0x08000000928b4b4c 0xf600c30e0f3f3f33 0x7d8030c383cfcfcc

def z512 : W := mkw 0x10604926200818a8 0x041812498802062a 0xdef0cf3e300038ff 0xb7bc33cf8c000e3f

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c3030c0c0cc 0x8000030c0c303033

def z514 : W := mkw 0x00041400d0034114 0x000105003400d045 0x00003001c0070000 0x00000c007001c000

def z515 : W := mkw 0x0bd948000fd08000 0x02f6520003f42000 0xabffcc000ff8c003 0xeafff30003fe3000

def z516 : W := mkw 0xe78eb6d9da252511 0x39e3adb676894944 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z517 : W := mkw 0x1060492620188828 0x041812498806220a 0xeef0cf3e3038c03f 0xbbbc33cf8c0e300f

def z518 : W := mkw 0x4bbf17f09fc036c0 0x52efc5fc27f00db0 0xdfff3ff1ffc03fc3 0xf7ffcffc7ff00ff0

def z519 : W := mkw 0x0007145091424244 0x0001c51424509091 0x510f0cf033c0c7ce 0xd443c33c0cf031f3

def z520 : W := mkw 0x0706b6d990000000 0x01c1adb664000000 0xc70ffffff0000003 0xb1c3fffffc000000

def z521 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xaaf0cf0e0cf8f803 0xeabc33c3833e3e00

def z522 : W := mkw 0x00061450d0034354 0x000185143400d0d5 0xf4003cf1f007c7fc 0x3d000f3c7c01f1ff

def z523 : W := mkw 0x6722a3fb4a2d3ff0 0x59c8a8fed28b4ffc 0xf700f3ffcf3f3ff3 0x7dc03cfff3cfcffc

def z524 : W := mkw 0x10100002049898a8 0x040400008126262a 0x000000000c383800 0x00000000030e0e00

def z525 : W := mkw 0x6fb8a3ab4ead3db0 0x5bee28ead3ab4f6c 0xfff0f3cfcf3f3f33 0x7ffc3cf3f3cfcfcc

def z526 : W := mkw 0x8bcdfc000b664000 0xa2f37f0002d99000 0x8bfffc0003070003 0xa2ffff0000c1c000

def z527 : W := mkw 0xd7eeffffb0188829 0x35fbbfffec06220a 0xeffffffff038c03f 0xbbfffffffc0e300f

def z528 : W := mkw 0x4bfb4bf42fc036c0 0x52fed2fd0bf00db0 0xdfffcffe3fc03fc3 0xf7fff3ff8ff00ff0

def z529 : W := mkw 0x0300028000000000 0x00c000a000000000 0x430003c000000003 0x10c000f000000000

def z530 : W := mkw 0x8bdcfc000eb6c000 0xa2f73f0003adb000 0xaaf0fc000c3fc001 0x2abc3f00030ff000

def z531 : W := mkw 0x13704ba62e98bca8 0x04dc12e98ba62f2a 0xfff0cffe3ff8ffff 0xfffc33ff8ffe3fff

def z532 : W := mkw 0x2400028940012510 0x090000a250004944 0x000000c1c0000700 0x00000030700001c0

def z533 : W := mkw 0x6fbb03fb4fc93ff0 0x5beec0fed3f24ffc 0x5fff03ffcfc03ff3 0xd7ffc0fff3f00ffc

def z534 : W := mkw 0x8044fc00d037c114 0xa0113f00340df045 0xa400fc01f03fc03c 0x29003f007c0ff00f

def z535 : W := mkw 0x8bddfc000fc00000 0x22f77f0003f00000 0x8bfffc000fc00003 0xe2ffff0003f00000

def z536 : W := mkw 0x0000000040010110 0x0000000010004044 0x540000c1c0000730 0x15000030700001cc

def z537 : W := mkw 0x2700a28b0a2c2c20 0x09c028a2c28b0b08 0xf600c30e0c383833 0x7d8030c3830e0e0c

def z538 : W := mkw 0x9bfdfd262ffed8a8 0xa6ff7f498bffb62a 0xabffff0e0ffff803 0xeaffffc383fffe00

def z539 : W := mkw 0x081100004fc377d4 0x4204400013f0ddf5 0x300000000fc7fffc 0x4c00000003f1ffff

def z540 : W := mkw 0xc7eefffdf0010355 0x31fbbfff7c0040d5 0xdffffffff00007ff 0xb7fffffffc0001ff

def z541 : W := mkw 0x9074fd2624bed8a8 0xa41d3f49892fb62a 0xfef0ff3e3cfff8ff 0xffbc3fcf8f3ffe3f

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0xf400000000000032 0x7d0000000000000c

def z543 : W := mkw 0x2f99a28b4fed2d30 0x0be668a2d3fb4b4c 0xfffff3cfcfff3f33 0xfffffcf3f3ffcfcc

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0xa200c0000c380003 0x68803000030e0000

def z545 : W := mkw 0x2750ea8b4ebdad30 0x09d43aa2d3af6b4c 0xfff0ffcfcfffff33 0xfffc3ff3f3ffffcc

def z546 : W := mkw 0x8b9db4000ff6c000 0xa2e76d0003fdb000 0x210f30000fffc000 0x4843cc0003fff000

def z547 : W := mkw 0x1070492424909088 0x041c124909242422 0x5af00f303cc0f8cf 0xd6bc03cc0f303e33

def z548 : W := mkw 0x0811000005d2c000 0x820440000174b000 0x0000000000c0c000 0x0000000000303000

def z549 : W := mkw 0x8044fc0000000000 0x20113f0000000000 0x8000fc0000000000 0x20003f0000000000

def z550 : W := mkw 0x8447fc5df1434355 0x2111ff177c50d0d5 0xf50ffcfff3c7c7fe 0xfd43ff3ffcf1f1ff

def z551 : W := mkw 0x0004140090024004 0x0001050024009001 0x00000c003000c00c 0x000003000c003003

def z552 : W := mkw 0xf7fefffffebdbdb9 0x3dffbfffffaf6f6e 0xffffffffffffffff 0xffffffffffffffff

def z553 : W := mkw 0x0005140001424000 0x0001450000509000 0xf50f3c3033c7c0fe 0xfd43cf0c0cf1f03f

def z554 : W := mkw 0x10200126200818a8 0x040800498802062a 0x0000030e00003800 0x000000c380000e00

def z555 : W := mkw 0xc7cefeddb0000001 0x31f3bfb76c000000 0x850ffccff0000000 0x2143ff33fc000000

def z556 : W := mkw 0x080100000b402640 0x4200400002d00990 0x0000000003000700 0x0000000000c001c0

def z557 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x300f0c3033c7c7fc 0xcc03c30c0cf1f1ff

def z558 : W := mkw 0xaf8db6894b676510 0xabe36da252d9d944 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z559 : W := mkw 0x081100004ff7c354 0x8204400013fdf0d5 0x300000000fffc7fc 0x4c00000003fff1ff

def z560 : W := mkw 0xe7e8ebaf2a2c2c21 0x39fa3aebca8b0b08 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z561 : W := mkw 0x1073497625d89ae8 0x041cd25d897626ba 0xffffcffe3ff8ffff 0xfffff3ff8ffe3fff

def z562 : W := mkw 0x030002800a002400 0x00c000a002800900 0x010000c003000700 0x0040003000c001c0

def z563 : W := mkw 0x181100020fd8bee8 0x4604400083f62fba 0x300000000ff8fffc 0x4c00000003fe3fff

def z564 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xc50f3cf1f3070702 0xb143cf3c7cc1c1c0

def z565 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xffff0ff03fc0ffff 0xffffc3fc0ff03fff

def z566 : W := mkw 0x030002804a012510 0x00c000a012804944 0xf70033c1cf073f33 0x7dc00cf073c1cfcc

def z567 : W := mkw 0xcfeffffdbb664001 0xb3fbffff6ed99000 0xcffffffff3070003 0xb3fffffffcc1c000

def z568 : W := mkw 0x2700a28b0a2c2c20 0x09c028a2c28b0b08 0x5300c3ce0f383f03 0x54c030f383ce0fc0

def z569 : W := mkw 0x1071492665dbdbfc 0x041c52499976f6ff 0xfef0cf3e3fffffff 0xffbc33cf8fffffff

def z570 : W := mkw 0x488b005001400240 0x5222c01400500090 0x000f000000000000 0x0003c00000000000

def z571 : W := mkw 0x2703a2db4b6d2f70 0x09c0e8b6d2db4bdc 0xf70ff3ffcfff3ff3 0xfdc3fcfff3ffcffc

def z572 : W := mkw 0xc7effffdb1400241 0x31fbffff6c500090 0xdffffffff3c007c3 0xf7fffffffcf001f0

def z573 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x38f00c303cf8f8fc 0xce3c030c0f3e3e3f

def z574 : W := mkw 0x10300126249898a8 0x040c00498926262a 0x7400033e3cf8f8fc 0x5d0000cf8f3e3e3f

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0xc50030c1c0000002 0x31400c3070000000

def z576 : W := mkw 0xc7eeffffb0080821 0x31fbbfffec020208 0xfffffffffc383833 0xffffffffff0e0e0c

def z577 : W := mkw 0x44624bfdb0000001 0x111892ff6c000000 0xcef0cffff0000003 0xb3bc33fffc000000

def z578 : W := mkw 0x0000000200080820 0x0000000080020208 0xa400c00e00380030 0x29003003800e000c

def z579 : W := mkw 0x8bddfc0005d2c000 0xa2f77f000174b000 0x8bfffc0000c0c003 0xa2ffff0000303000

def z580 : W := mkw 0xcff8ebad2e803481 0x73fe3aeb4ba00d20 0x0af0c30e0c003801 0x02bc30c383000e00

def z581 : W := mkw 0x2700a28b40092d30 0x09c028a2d0024b4c 0xd700f3cfc0003f33 0x35c03cf3f0000fcc

def z582 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x010f3cf1f3c7c7cc 0x8043cf3c7cf1f1f3

def z583 : W := mkw 0x0000000200080820 0x0000000080020208 0x300000000c383830 0x4c000000030e0e0c

def z584 : W := mkw 0x8047fc50d177c354 0xa011ff14345df0d5 0xf50ffcf1f3ffc7fe 0xfd43ff3c7cfff1ff

def z585 : W := mkw 0x5bf84ba62e98bca8 0x56fe12e98ba62f2a 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z586 : W := mkw 0x2706b6dbda2d2d30 0x09c1adb6f68b4b4c 0xf70fffffff3f3f33 0xfdc3ffffffcfcfcc

def z587 : W := mkw 0x00041400d0034114 0x000105003400d045 0xf4003c31f0c7c0fe 0xfd000f0c7c31f03f

def z588 : W := mkw 0x0760ebad20000000 0x01d83aeb48000000 0xcff0fffff0000003 0xb3fc3ffffc000000

def z589 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x5cf00f3e30c0f8fc 0x973c03cf8c303e3f

def z590 : W := mkw 0x4b8802800a002400 0x52e200a002800900 0x0000000000000000 0x0000000000000000

def z591 : W := mkw 0x8bd8e8000eb48000 0xa2f63a0003ad2000 0xaaf0cc000cf8c003 0xeabc3300033e3000

def z592 : W := mkw 0x8464fd2db0000001 0x21193f4b6c000000 0xcef0ff3ff0000003 0xb3bc3fcffc000000

def z593 : W := mkw 0xefffffffffed3ff1 0x7bfffffffffb4ffc 0xffffffffffff3ff3 0xffffffffffffcffc

def z594 : W := mkw 0x0007145091424244 0x0001c51424509091 0xa10f3c3033c7c0ce 0xe843cf0c0cf1f033

def z595 : W := mkw 0xcff8ebad2eb48001 0xb3fe3aeb4bad2000 0x0af0c30e0c380001 0x02bc30c3830e0000

def z596 : W := mkw 0xafddfe894ff7e510 0xabf77fa253fdf944 0xabfffcc1cfffc703 0xeaffff3073fff1c0

def z597 : W := mkw 0xd7f8ebaf249898a9 0x35fe3aebc926262a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z598 : W := mkw 0xcffbebfd2fc036c1 0x73fefaff4bf00db0 0x5bffc3fe0fc03fc3 0xd6fff0ff83f00ff0

def z599 : W := mkw 0x8b8fb450db674354 0xa2e3ed1436d9d0d5 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z600 : W := mkw 0x0300a0000a240000 0x00c0280002890000 0x0200c0000c380001 0x00803000030e0000

def z601 : W := mkw 0x43ba03f004801080 0x10ee80fc01200420 0x5bff03f00cc038c3 0xd6ffc0fc03300e30

def z602 : W := mkw 0x2700a28b0a2c2c20 0x09c028a2c28b0b08 0xc700f3cfcc383803 0x31c03cf3f30e0e00

def z603 : W := mkw 0x10100002049898a8 0x040400008126262a 0xf4000c303cf8f8fe 0xfd00030c0f3e3e3f

def z604 : W := mkw 0x10000002000818a8 0x040000008002062a 0x10000000000038fc 0x0400000000000e3f

def z605 : W := mkw 0x083101200fc036c0 0x420c404803f00db0 0x5af003300fc03fc3 0xd6bc00cc03f00ff0

def z606 : W := mkw 0x030000000a000000 0x00c0000002800000 0x030000000f000003 0x40c0000003c00000

def z607 : W := mkw 0x0003005001400240 0x0000c01400500090 0xf50f0cf033c0c7fe 0xfd43c33c0cf031ff

def z608 : W := mkw 0x1000000200188828 0x040000008006220a 0x200000000038c03c 0x08000000000e300f

def z609 : W := mkw 0x240716dbd14b6f74 0x0901c5b6f452dbdd 0xf50f3ffff3c7fffe 0xfd43cffffcf1ffff

def z610 : W := mkw 0x0006145090000000 0x0001851424000000 0x000f0c3030000000 0x8003c30c0c000000

def z611 : W := mkw 0xc7e8ebad20000001 0x31fa3aeb48000000 0xcef0cf3e30000003 0xb3bc33cf8c000000

def z612 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x0af0cf3e3cf8f8cd 0x82bc33cf8f3e3e33

def z613 : W := mkw 0x2407b45bd16f4b74 0x0901ed16f45bd2dd 0xf50ffcfff3ffc7fe 0xfd43ff3ffcfff1ff

def z614 : W := mkw 0x0b1102800fc036c0 0x42c440a003f00db0 0x530003c00fc03fc3 0x54c000f003f00ff0

def z615 : W := mkw 0x4bbf17f0dfc377d4 0x52efc5fc37f0ddf5 0x5bff33f1cfc73fc3 0xd6ffccfc73f1cff0

def z616 : W := mkw 0xc7aeb7fdb0000001 0x31ebadff6c000000 0x450f33fff0000000 0x1143ccfffc000000

def z617 : W := mkw 0xc7cefed990000001 0x31f3bfb664000000 0x8bfffcc1c0000003 0xa2ffff3070000000

def z618 : W := mkw 0xc3ee5ff4b0000001 0x30fb97fd2c000000 0x4bff0ff030000003 0x92ffc3fc0c000000

def z619 : W := mkw 0xcf8fb6d99b402641 0x73e3edb666d00990 0x010f30c1c3000700 0x0043cc3070c001c0

def z620 : W := mkw 0x00020050d0010354 0x00008014340040d5 0xf50030f1f30707fe 0x7d400c3c7cc1c1ff

def z621 : W := mkw 0x000000000036c000 0x80000000000db000 0x20000000003fc000 0x08000000000ff000

def z622 : W := mkw 0x0040480420000000 0x0010120108000000 0x8400cc0e30000000 0x210033038c000000

def z623 : W := mkw 0xaf8db68b4b6f6d30 0xabe36da2d2dbdb4c 0xf70ff3cfcf3f3f33 0x7dc3fcf3f3cfcfcc

def z624 : W := mkw 0x2400000b40090930 0x09000002d002424c 0x0400000fc0000030 0x01000003f000000c

def z625 : W := mkw 0x6fb8a3ab0eac3ca0 0x5bee28eac3ab0f28 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z626 : W := mkw 0x00371570d5c353d4 0x000dc55c3570d4f5 0xffff3ff1ffc7ffff 0xffffcffc7ff1ffff

def z627 : W := mkw 0x00061450d0010354 0x00018514340040d5 0xd50f3cf1f00007fe 0xb543cf3c7c0001ff

def z628 : W := mkw 0x0030012004801080 0x000c004801200420 0xfef00f303cc0f8ff 0xffbc03cc0f303e3f

def z629 : W := mkw 0x8b8fb450db674354 0xa2e3ed1436d9d0d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z630 : W := mkw 0x4b8b02d00b402640 0x52e2c0b402d00990 0x530f03c00f003f03 0x54c3c0f003c00fc0

def z631 : W := mkw 0x8045fc000176c000 0xa0117f00005db000 0xa10ffc0003ffc002 0xe843ff0000fff000

def z632 : W := mkw 0x4bba03f00e8036c0 0x52ee80fc03a00db0 0x5af003f00c003fc1 0x16bc00fc03000ff0

def z633 : W := mkw 0x0700a28b00080820 0x01c028a2c0020208 0xf700f3cfcc383833 0x7dc03cf3f30e0e0c

def z634 : W := mkw 0x0007145001424240 0x0001c51400509090 0xf10f3cf003c7c7c2 0xfc43cf3c00f1f1f0

def z635 : W := mkw 0x2700a2894a252510 0x09c028a252894944 0xc700f3cfc3070703 0x31c03cf3f0c1c1c0

def z636 : W := mkw 0xcbfffd74bff6c001 0xb2ffff5d2ffdb000 0xabfffc303fffc003 0xeaffff0c0ffff000

def z637 : W := mkw 0x1bf949262fd898a8 0x06fe52498bf6262a 0xffffcf3e3ff8f8ff 0xfffff3cf8ffe3e3f

def z638 : W := mkw 0x00000000d0010114 0x0000000034004045 0x04000001f000003c 0x010000007c00000f

def z639 : W := mkw 0x43a803a000000000 0x10ea00e800000000 0x0af0030000000001 0x02bc00c000000000

def z640 : W := mkw 0x187149262ffed8a8 0x861c52498bffb62a 0xfef0cf3e3ffff8ff 0xffbc33cf8ffffe3f

def z641 : W := mkw 0x2400a00940250110 0x0900280250094044 0x00003001c0070000 0x00000c007001c000

def z642 : W := mkw 0x00020050d0010354 0x00008014340040d5 0xf4000cf1f0c0c7fe 0xfd00033c7c3031ff

def z643 : W := mkw 0x0050480004908000 0x0014120001242000 0x0af0c0000c380001 0x02bc3000030e0000

def z644 : W := mkw 0x8bdcfc000eb48000 0xa2f73f0003ad2000 0x8bfffc000c380003 0xa2ffff00030e0000

def z645 : W := mkw 0x0001000001424000 0x0000400000509000 0x2000000003c7c000 0x4800000000f1f000

def z646 : W := mkw 0x0300a0004a250110 0x00c0280012894044 0xf700f0c1cf3f0733 0x7dc03c3073cfc1cc

def z647 : W := mkw 0xbffdffaf6ffffdb8 0xafff7febdbffff6e 0xffffffffffffffff 0xffffffffffffffff

def z648 : W := mkw 0x8b9db4000fe64000 0xa2e76d0003f99000 0x0bff30000fc70003 0xc2ffcc0003f1c000

def z649 : W := mkw 0x6fbba3f94fe537d0 0x5beee8fe53f94df4 0x5bff33f1cfc73fc3 0xd6ffccfc73f1cff0

def z650 : W := mkw 0x2707b6d9db676754 0x09c1edb676d9d9d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z651 : W := mkw 0x200000024a2d2d30 0x08000000928b4b4c 0xf50030c1cf3f3f32 0x7d400c3073cfcfcc

def z652 : W := mkw 0x0010000004800000 0x0004000001200000 0x0af000000cc00003 0xc2bc000003300000

def z653 : W := mkw 0xa744fe8b4a3fed30 0xa9d13fa2d28ffb4c 0xf700ffcfcf3fff33 0x7dc03ff3f3cfffcc

def z654 : W := mkw 0x442717fdf1434355 0x1109c5ff7c50d0d5 0xf50f3ffff3c7c7fe 0xfd43cffffcf1f1ff

def z655 : W := mkw 0x0b9800000e800000 0x02e6000003a00000 0x0af000000c000001 0x02bc000003000000

def z656 : W := mkw 0x48bb017005c012c0 0x522ec05c017004b0 0x5aff03300cc038c3 0xd6bfc0cc03300e30

def z657 : W := mkw 0x8855fc000ff6c000 0xa2157f0003fdb000 0xa000fc000fffc000 0x68003f0003fff000

def z658 : W := mkw 0x10775d76b5dadaec 0x041dd75dad76b6bb 0xfeffcf3e3cf8f8ff 0xffbff3cf8f3e3e3f

def z659 : W := mkw 0x0004140000024000 0x0001050000009000 0xa0003c000007c000 0x28000f000001f000

def z660 : W := mkw 0x88df5c5095d2c244 0xa237d7142574b091 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z661 : W := mkw 0x3720a3af6a2d3db8 0x0dc828ebda8b4f6e 0xf700f3ffff3f3fff 0x7dc03cffffcfcfff

def z662 : W := mkw 0x8744fe8db0000001 0x21d13fa36c000000 0xc700ffcff0000003 0x31c03ff3fc000000

def z663 : W := mkw 0xd0fe5d76b49898a9 0x343f975dad26262a 0xfeffcf3e3cf8f8ff 0xffbff3cf8f3e3e3f

def z664 : W := mkw 0x030002800a002400 0x00c000a002800900 0x020003000c003801 0x008000c003000e00

def z665 : W := mkw 0x0000028000002400 0x000000a000000900 0x500003c000003f00 0x140000f000000fc0

def z666 : W := mkw 0x0001000041434354 0x000040001050d0d5 0xf50030c1c3c7c7fe 0x7d400c3070f1f1ff

def z667 : W := mkw 0x402717f0d14377d4 0x5009c5fc3450ddf5 0xf50f3ff1f3c7fffe 0xfd43cffc7cf1ffff

def z668 : W := mkw 0x081514000ff6c000 0x8205450003fdb000 0xa10f3c000fffc002 0xe843cf0003fff000

def z669 : W := mkw 0x67aaa3fb4a2d2d30 0x19eaa8fed28b4b4c 0xfffff3ffcf3f3f33 0xfffffcfff3cfcfcc

def z670 : W := mkw 0x43ae17f090000000 0x10eb85fc24000000 0xcfff3ff1f0000003 0xb3ffcffc7c000000

def z671 : W := mkw 0x0020012000000000 0x0008004800000000 0x4af0033000000003 0x92bc00cc00000000

def z672 : W := mkw 0x6fbba3fb0fec3ee0 0x5beee8fec3fb0fb8 0x5bffc3fe0ff83fc3 0xd6fff0ff83fe0ff0

def z673 : W := mkw 0x6f8ba2db4b6d2f70 0x5be2e8b6d2db4bdc 0xf70ff3cfcf3f3f33 0x7dc3fcf3f3cfcfcc

def z674 : W := mkw 0xafd8ea8b0ebcac20 0xabf63aa2c3af2b08 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z675 : W := mkw 0x402303f0014036c0 0x5008c0fc00500db0 0x510f03f003c03fc2 0xd443c0fc00f00ff0

def z676 : W := mkw 0xcffefffdbeb48001 0xb3ffbfff6fad2000 0xcffffffffc380003 0xb3ffffffff0e0000

def z677 : W := mkw 0x40aa017000000000 0x102a805c00000000 0x08ff003000000000 0x823fc00c00000000

def z678 : W := mkw 0x200100024b6f6f74 0x0800400092dbdbdd 0x300000000ffffffc 0x4c00000003ffffff

def z679 : W := mkw 0x0700a28900000000 0x01c028a240000000 0x010030c1c0000000 0x00400c3070000000

def z680 : W := mkw 0xc7aeb7f990000001 0x31ebadfe64000000 0x4bff33f1c0000003 0x92ffccfc70000000

def z681 : W := mkw 0x4722a3fdb0000001 0x11c8a8ff6c000000 0xc700f3fff0000003 0x31c03cfffc000000

def z682 : W := mkw 0x0707b6d9d1434354 0x01c1edb67450d0d5 0xf70ffffff3c7c7ff 0xfdc3fffffcf1f1ff

def z683 : W := mkw 0xd7feffffb49898a9 0x35ffbfffed26262a 0xcffffffffc383803 0xb3ffffffff0e0e00

def z684 : W := mkw 0x4bbb03f04fc377d4 0x52eec0fc13f0ddf5 0x7bff03f00fc7ffff 0xdeffc0fc03f1ffff

def z685 : W := mkw 0x8bddfc00dff7c114 0xa2f77f0037fdf045 0xaffffc01ffffc03f 0xebffff007ffff00f

def z686 : W := mkw 0x4bb803a00e803480 0x52ee00e803a00d20 0x5af003300cc038c3 0xd6bc00cc03300e30

def z687 : W := mkw 0x8bdffc500ff6c240 0xa2f7ff1403fdb090 0xfbfffcf00fffc7c3 0xfeffff3c03fff1f0

def z688 : W := mkw 0x1000000620080828 0x040000018802020a 0x0400000e3000003c 0x010000038c00000f

def z689 : W := mkw 0x2700a2894a252510 0x09c028a252894944 0xa300f0c1cf3f0703 0x68c03c3073cfc1c0

def z690 : W := mkw 0x000000000a240000 0x0000000002890000 0x200000000f3f0000 0x4800000003cfc000

def z691 : W := mkw 0x9044fc06203ec828 0xa4113f01880fb20a 0xa400fc0e303fc03c 0x29003f038c0ff00f

def z692 : W := mkw 0x5bbb03f62fc83ee8 0x56eec0fd8bf20fba 0x5fff03fe3fc03fff 0xd7ffc0ff8ff00fff

def z693 : W := mkw 0xcb8fb6d00b666640 0xf2e3edb402d99990 0x010f30c003070700 0x0043cc3000c1c1c0

def z694 : W := mkw 0x0003005001400240 0x0000c01400500090 0x010f00c003000700 0x0043c03000c001c0

def z695 : W := mkw 0x0040480000108000 0x0010120000042000 0xa000cc000038c000 0x28003300000e3000

def z696 : W := mkw 0x4bab03f00b402640 0x52eac0fc02d00990 0x4bff03f003000703 0x92ffc0fc00c001c0

def z697 : W := mkw 0x9bddfc020ffed8a8 0xa6f77f0083ffb62a 0xbbfffc000ffff8ff 0xeeffff0003fffe3f

def z698 : W := mkw 0x6f8ba2d94b652750 0x5be2e8b652d949d4 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z699 : W := mkw 0x0400028900000000 0x010000a240000000 0x440003cfc0000000 0x110000f3f0000000

def z700 : W := mkw 0x0007145091424000 0x0001c51424509000 0xe50f3cf1f3c7c002 0xf943cf3c7cf1f000

def z701 : W := mkw 0x0001000001400240 0x0000400000500090 0x1000000003c007c0 0x4400000000f001f0

def z702 : W := mkw 0xcffffffdbff6f6c1 0xf3ffffff6ffdbdb0 0xffffffffffffffc3 0xfffffffffffffff0

def z703 : W := mkw 0x48b8012004801080 0x522e004801200420 0x08f0000000000000 0x023c000000000000

def z704 : W := mkw 0xcbfffd700ff6d2c0 0xf2ffff5c03fdb4b0 0xabfffc300fffc0c3 0xeaffff0c03fff030

def z705 : W := mkw 0xafd8ea8b4ebdad30 0xabf63aa2d3af6b4c 0xfff0f3cfcf3f3f33 0x7ffc3cf3f3cfcfcc

def z706 : W := mkw 0x0b8900000b400000 0x02e2400002d00000 0x010f000003000000 0x0043c00000c00000

def z707 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x5fff03f03fc03fff 0xd7ffc0fc0ff00fff

def z708 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xfff0fffffcf8f8ff 0xfffc3fffff3e3e3f

def z709 : W := mkw 0xaf8fb6d9db676754 0xabe3edb676d9d9d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z710 : W := mkw 0xc7aeb7f990000001 0x31ebadfe64000000 0xcffff3ffc0000003 0xb3fffcfff0000000

def z711 : W := mkw 0xa7ccfe8b40092d30 0x29f33fa2d0024b4c 0xdfffffcfc0003f33 0xb7fffff3f0000fcc

def z712 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x550f3cf1f3c7c7fc 0x9543cf3c7cf1f1ff

def z713 : W := mkw 0x2f99a00b4fed0930 0x0be66802d3fb424c 0xaffff00fcfff0033 0xebfffc03f3ffc00c

def z714 : W := mkw 0x4c3303fdbff6c001 0x930cc0ff6ffdb000 0x640003ffffffc000 0x590000fffffff000

def z715 : W := mkw 0x2400028b40092d30 0x090000a2d0024b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z716 : W := mkw 0x3770ebad6eb5b598 0x0ddc3aeb5bad6d66 0x09f03cf1f3c7c7cc 0x827c0f3c7cf1f1f3

def z717 : W := mkw 0x4bab03f00b402640 0x52eac0fc02d00990 0x5bff03f00f003f03 0xd6ffc0fc03c00fc0

def z718 : W := mkw 0xafddfe890ff6e400 0xabf77fa243fdb900 0xabfffc000fffc003 0xeaffff0003fff000

def z719 : W := mkw 0x200000024a2d2d30 0x08000000928b4b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z720 : W := mkw 0x5bcb4ad62b58ae68 0x56f2d2b58ad62b9a 0xa50fccce3338c73c 0x2943f3338cce31cf

def z721 : W := mkw 0x48bb01700fc036c0 0x522ec05c03f00db0 0x5aff03300fc03fc3 0xd6bfc0cc03f00ff0

def z722 : W := mkw 0xd79eb6db949898a9 0x35e7adb6e526262a 0x310f30c1ccf8f8fc 0x4c43cc30733e3e3f

def z723 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xeffffcc1cfffc003 0xfbffff3073fff000

def z724 : W := mkw 0x63aa03f24a2d2d30 0x18ea80fc928b4b4c 0x7bff03f00f3f3f33 0xdeffc0fc03cfcfcc

def z725 : W := mkw 0x8bddfc000ff6d080 0xa2f77f0003fdb420 0xbbfffc000ffff8c3 0xeeffff0003fffe30

def z726 : W := mkw 0x033303f00fc036c0 0x00ccc0fc03f00db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z727 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xdfff33f1cfc03fc3 0xf7ffccfc73f00ff0

def z728 : W := mkw 0x0388a0000a240000 0x00e2280002890000 0xabfff0000f3f0003 0xeafffc0003cfc000

def z729 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x2bfff0000fffc001 0x4afffc0003fff000

def z730 : W := mkw 0x6f88a28b4a2d2d30 0x5be228a2d28b4b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z731 : W := mkw 0x403303f005c036c0 0x500cc0fc01700db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z732 : W := mkw 0x10161452949898a8 0x04058514a526262a 0xf50f3cf1fcf8f8fe 0xfd43cf3c7f3e3e3f

def z733 : W := mkw 0x9badb5262b6e58a8 0xa6eb6d498adb962a 0x550f333e330738fc 0x1543cccf8cc1ce3f

def z734 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xabfff0000f3f0003 0x6afffc0003cfc000

def z735 : W := mkw 0x4fbb03f99fc036c1 0x53eec0fe67f00db0 0x5bff03f1cfc03fc3 0xd6ffc0fc73f00ff0

def z736 : W := mkw 0x84ccfc0db0000001 0x21333f036c000000 0x8cfffc0ff0000000 0xa33fff03fc000000

def z737 : W := mkw 0x483303f00ff6f6c0 0xd20cc0fc03fdbdb0 0x700003f00fffffc0 0x5c0000fc03fffff0

def z738 : W := mkw 0x0f11a2890ff6c000 0x83c468a243fdb000 0xe700f3cfcfffc003 0x79c03cf3f3fff000

def z739 : W := mkw 0x2707b6db9b6e6e64 0x09c1edb6e6db9b99 0x020fcf3e3cf8f8cd 0x8083f3cf8f3e3e33

def z740 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xcffffffff0c0c0cf 0xb3fffffffc303033

def z741 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xfff0cffe3ff8ffff 0xfffc33ff8ffe3fff

def z742 : W := mkw 0xf7f8ebaf2ebcbca9 0x3dfe3aebcbaf2f2a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z743 : W := mkw 0xd7eefffdb0108009 0x35fbbfff6c042002 0xcffffffff000c00f 0xb3fffffffc003003

def z744 : W := mkw 0x43aa03f00a0036c0 0x50ea80fc02800db0 0x5bff03f00f003fc3 0xd6ffc0fc03c00ff0

def z745 : W := mkw 0x48bb03f005c036c0 0x522ec0fc01700db0 0x59ff03f003c03fc2 0xd67fc0fc00f00ff0

def z746 : W := mkw 0xc4ee5ffdb0000001 0x313b97ff6c000000 0xceffcffff0000003 0xb3bff3fffc000000

def z747 : W := mkw 0x43bb03f005c012c0 0x10eec0fc017004b0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z748 : W := mkw 0x0bd948000ff6c000 0x82f6520003fdb000 0xabffcc000fffc003 0xeafff30003fff000

def z749 : W := mkw 0x542203fff0091bfd 0x150880fffc0246ff 0x540003fff0003ffc 0x150000fffc000fff

def z750 : W := mkw 0xc7eefffdba240001 0x31fbbfff6e890000 0xcffffffffc380003 0xb3ffffffff0e0000

def z751 : W := mkw 0x00061450d0010110 0x0001851434004044 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z752 : W := mkw 0x08555c000ff6c000 0x8215570003fdb000 0xabfffc000fffc003 0xeaffff0003fff000

def z753 : W := mkw 0x4bbb03f00fc02400 0x12eec0fc03f00900 0x5bff03f00fc03f03 0xd6ffc0fc03f00fc0

def z754 : W := mkw 0x742203ff60093ff8 0x5d0880ffd8024ffe 0x540003fff0003ffc 0x150000fffc000fff

def z755 : W := mkw 0x8fddfc090ff6c000 0xa3f77f0243fdb000 0xaffffc0fcfffc003 0xebffff03f3fff000

def z756 : W := mkw 0x4bbb03f00fe436c0 0x52eec0fc03f90db0 0x7bff03f00fff3fc3 0xdeffc0fc03ffcff0

def z757 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x1bff03c00fc03fc1 0x46ffc0f003f00ff0

def z758 : W := mkw 0xa3ccfc024a2d2d30 0x28f33f00928b4b4c 0xbbfffc000f3f3f33 0xeeffff0003cfcfcc

def z759 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xfbfffc300fffc0c3 0xfeffff0c03fff030

def z760 : W := mkw 0xc0ee5d74b0000001 0x303b975d2c000000 0xcffffffff0000003 0xb3fffffffc000000

def z761 : W := mkw 0xc7eefffdb0024005 0x31fbbfff6c009001 0xcffffffff000c00f 0xb3fffffffc003003

def z762 : W := mkw 0x8bcdfc000b664000 0xa2f37f0002d99000 0xabfffc000f3f0003 0xeaffff0003cfc000

def z763 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xeffffffff3070003 0xfbfffffffcc1c000

def z764 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x2affcc000fffc001 0xcabff30003fff000

def z765 : W := mkw 0x8bd9e8000ff48000 0xa2f67a0003fd2000 0xabfff0000fff0003 0xeafffc0003ffc000

def z766 : W := mkw 0xc7eefffdb00012c1 0x71fbbfff6c0004b0 0xcffffffff00000c3 0xb3fffffffc000030

def z767 : W := mkw 0x642203fff0093ff1 0x590880fffc024ffc 0x540003fff0003ff0 0x150000fffc000ffc

def z768 : W := mkw 0x5bbb03f42fc036c8 0x56eec0fd0bf00db2 0x5bff03f03fc03fcf 0xd6ffc0fc0ff00ff3

def z769 : W := mkw 0xbff8ebaf2ebcbca8 0xaffe3aebcbaf2f2a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z770 : W := mkw 0x43ba03f00e803480 0x10ee80fc03a00d20 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z771 : W := mkw 0x602203f240093ff0 0x580880fc90024ffc 0x500003f000003ff0 0x140000fc00000ffc

def z772 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xf70ffcf1ffffc7ff 0xfdc3ff3c7ffff1ff

def z773 : W := mkw 0xc7eefd7db0000001 0x31fbbf5f6c000000 0x8ffffc3ff0000003 0xa3ffff0ffc000000

def z774 : W := mkw 0x0b9900000fe40000 0x02e6400003f90000 0x2bff00000fff0003 0xcaffc00003ffc000

def z775 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x4bff03f00f003f03 0x92ffc0fc03c00fc0

def z776 : W := mkw 0x502203f6f0093ffc 0x540880fdbc024fff 0x540003fff0003ffc 0x150000fffc000fff

def z777 : W := mkw 0x0060492620080820 0x0018124988020208 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z778 : W := mkw 0xa444fc0ff02f4935 0x29113f03fc0bd24d 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z779 : W := mkw 0x2f99028b4fc92d30 0x0be640a2d3f24b4c 0x5fff03cfcfc03f33 0xd7ffc0f3f3f00fcc

def z780 : W := mkw 0xc066fff00036f6c0 0xf019bffc000dbdb0 0xf000fff0003fffc0 0x3c003ffc000ffff0

def z781 : W := mkw 0x98ff5d74b5d2d2cc 0xa63fd75d2d74b4b3 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z782 : W := mkw 0x88ddfc000ff6c000 0xa2377f0003fdb000 0xa8fffc000fffc000 0xea3fff0003fff000

def z783 : W := mkw 0xc7e9ebad61434355 0x31fa7aeb5850d0d5 0x3af0c30e03c7c7fd 0x4ebc30c380f1f1ff

def z784 : W := mkw 0xb444fc0f603fc938 0xad113f03d80ff24e 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z785 : W := mkw 0x8bddfc000ff6e400 0xa2f77f0003fdb900 0xbbfffc000fffff03 0xeeffff0003ffffc0

def z786 : W := mkw 0x8bddfc000ff6f480 0xe2f77f0003fdbd20 0xabfffc000ffff803 0xeaffff0003fffe00

def z787 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xa9fffc0003ffc000 0xaa7fff0000fff000

def z788 : W := mkw 0xc7ee5ffdb0000001 0x31fb97ff6c000000 0x4fff0ffff0000003 0x93ffc3fffc000000

def z789 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x8effff3ff0000001 0xa3bfffcffc000000

def z790 : W := mkw 0x88dd5c000ff6c000 0xa237570003fdb000 0xaaffcc000fffc003 0xeabff30003fff000

def z791 : W := mkw 0x0bdd5c000fd2c000 0x02f7570003f4b000 0xabfffc000fffc003 0xeaffff0003fff000

def z792 : W := mkw 0x181100024fffdbfc 0x8604400093fff6ff 0x300000000ffffffc 0x4c00000003ffffff

def z793 : W := mkw 0x4bbc17a0de837594 0x52ef05e837a0dd65 0xaef03f01fc07f83d 0x2bbc0fc07f01fe0f

def z794 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x0bfff0000fff0003 0xc2fffc0003ffc000

def z795 : W := mkw 0x0bbb01700fc012c0 0x02eec05c03f004b0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z796 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xaafffc000cffc001 0xaabfff00033ff000

def z797 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x29ff3c000fffc000 0xca7fcf0003fff000

def z798 : W := mkw 0x4bbb03f09fc036c4 0x52eec0fc27f00db1 0x5bff03f03fc03fcf 0xd6ffc0fc0ff00ff3

def z799 : W := mkw 0x2400a28b4a2d2d30 0x090028a2d28b4b4c 0xf400f3cfcf3f3f30 0x7d003cf3f3cfcfcc

def z800 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x5300f3cfcf3f3f03 0x54c03cf3f3cfcfc0

def z801 : W := mkw 0x8bdd5c000ff6c000 0xa2f7570003fdb000 0x2bff0c000fffc003 0xcaffc30003fff000

def z802 : W := mkw 0xacdd5e8b45dbed30 0xab3757a2d176fb4c 0x5cff0fcfc0c0ff30 0x973fc3f3f0303fcc

def z803 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x0bfffffff0000001 0x82fffffffc000000

def z804 : W := mkw 0xc7ecffadb0000001 0x31fb3feb6c000000 0x8fffff0ff0000003 0xa3ffffc3fc000000

def z805 : W := mkw 0xc4ee5d7db0000001 0x313b975f6c000000 0x0cff0c3ff0000000 0x833fc30ffc000000

def z806 : W := mkw 0xc8ff5d74b5d2d2c1 0xf23fd75d2d74b4b0 0x08ff0c3030c0c0c0 0x823fc30c0c303030

def z807 : W := mkw 0x9044fc06f03fc93c 0xa4113f01bc0ff24f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z808 : W := mkw 0x47ea4bfdb0000001 0x11fa92ff6c000000 0xcfffcffff0000003 0xb3fff3fffc000000

def z809 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xeffffffff000c03f 0xbbfffffffc00300f

def z810 : W := mkw 0xc7eefffdba000001 0x31fbbfff6e800000 0xcfffffffff000003 0xf3ffffffffc00000

def z811 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700ffffff3f3f33 0xfdc03fffffcfcfcc

def z812 : W := mkw 0x642203fff0092f75 0x190880fffc024bdd 0x540003fff0003ffc 0x150000fffc000fff

def z813 : W := mkw 0x8bdae850deb58354 0xa2f6ba1437ad60d5 0x5ef0c0f1fc3807fd 0x17bc303c7f0e01ff

def z814 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xa50f3cf1f3c7c7fc 0xa943cf3c7cf1f1ff

def z815 : W := mkw 0x0bb903a00fc03480 0x02ee40e803f00d20 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z816 : W := mkw 0x8466fd7db0000001 0x2119bf5f6c000000 0xcffffffff0000003 0xb3fffffffc000000

def z817 : W := mkw 0x0700a28b40090930 0x01c028a2d002424c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z818 : W := mkw 0xc4eefd7db0000001 0x313bbf5f6c000000 0xceffff3ff0000003 0xb3bfffcffc000000

def z819 : W := mkw 0x0b9b00500fc036c0 0x42e6c01403f00db0 0x5bff00f00fc03fc3 0xd6ffc03c03f00ff0

def z820 : W := mkw 0x8bddfe800ff6e400 0xa2f77fa003fdb900 0xabfffcc00fffc703 0xeaffff3003fff1c0

def z821 : W := mkw 0x4bbb03f4bfc036c1 0x52eec0fd2ff00db0 0x5bff03f03fc03fc3 0xd6ffc0fc0ff00ff0

def z822 : W := mkw 0xd7eefffdb0001089 0x35fbbfff6c000422 0xcffffffff00000cf 0xb3fffffffc000033

def z823 : W := mkw 0x0b9902800fc036c0 0x42e640a003f00db0 0x5bff03c00fc03fc3 0xd6ffc0f003f00ff0

def z824 : W := mkw 0x0788a28900000000 0x01e228a240000000 0xcffff3cfc0000003 0xb3fffcf3f0000000

def z825 : W := mkw 0x4bbba3f00fe436c0 0x52eee8fc03f90db0 0x5bffc3f00ff83fc3 0xd6fff0fc03fe0ff0

def z826 : W := mkw 0x8744fe8dba002401 0x21d13fa36e800900 0xd700ffcfff003f03 0x75c03ff3ffc00fc0

def z827 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xfff0ff3e3ffff8ff 0xfffc3fcf8ffffe3f

def z828 : W := mkw 0xc7eefff900000000 0x31fbbffe40000000 0xcfffffffc0000003 0xb3fffffff0000000

def z829 : W := mkw 0x9444fc0ff01bc93d 0x25113f03fc06f24f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z830 : W := mkw 0x4bb903a00fc036c0 0x52ee40e803f00db0 0x1bff03000fc03fc3 0xc6ffc0c003f00ff0

def z831 : W := mkw 0x87ccfe8db0000001 0x21f33fa36c000000 0xcfffffcff0000003 0xb3fffff3fc000000

def z832 : W := mkw 0x4bbb03f00fd2f6c0 0xd2eec0fc03f4bdb0 0x5bff03f00fc0ffc3 0xd6ffc0fc03f03ff0

def z833 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xeffffffff0c0c003 0xfbfffffffc303000

def z834 : W := mkw 0x44665ffdb0000001 0x111997ff6c000000 0xcffffffff0000003 0xb3fffffffc000000

def z835 : W := mkw 0x8855fc000ff6f6c0 0xe2157f0003fdbdb0 0xb000fc000fffffc0 0x6c003f0003fffff0

def z836 : W := mkw 0x48bb017005c036c0 0x522ec05c01700db0 0x18ff003000c03fc0 0x863fc00c00300ff0

def z837 : W := mkw 0xe0ee5d76fa2d2d31 0x383b975dbe8b4b4c 0x38ff0c303f3f3f30 0xce3fc30c0fcfcfcc

def z838 : W := mkw 0x0061492461434354 0x001852491850d0d5 0xfef0cf3e33c7c7ff 0xffbc33cf8cf1f1ff

def z839 : W := mkw 0x8fddfe890ff6c000 0xa3f77fa243fdb000 0xabfffcc1cfffc003 0xeaffff3073fff000

def z840 : W := mkw 0x642203fbd0093ff4 0x590880fef4024ffd 0x540003fff0003ffc 0x150000fffc000fff

def z841 : W := mkw 0xc7eefffdb0002641 0x71fbbfff6c000990 0xcffffffff0000703 0xb3fffffffc0001c0

def z842 : W := mkw 0x88dd5c0005d2c000 0xa23757000174b000 0xabfffc000fffc003 0xeaffff0003fff000

def z843 : W := mkw 0x0bd9e8000ff48000 0x02f67a0003fd2000 0xabfffc000fffc003 0xeaffff0003fff000

def z844 : W := mkw 0x8bcdfc000b76c000 0xa2f37f0002ddb000 0xabfffc00033fc003 0xaaffff0000cff000

def z845 : W := mkw 0x8bddfc000fe40000 0x22f77f0003f90000 0xabfffc000fff0003 0xeaffff0003ffc000

def z846 : W := mkw 0x8bddfc000ff6d2c0 0xe2f77f0003fdb4b0 0xabfffc000fffc0c3 0xeaffff0003fff030

def z847 : W := mkw 0x58ff5d74b5d2d2cc 0x563fd75d2d74b4b3 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z848 : W := mkw 0x43ba03f0048036c0 0x50ee80fc01200db0 0x5bff03f00cc03fc3 0xd6ffc0fc03300ff0

def z849 : W := mkw 0x47aa03f900000000 0x11ea80fe40000000 0x4fff03ffc0000003 0x93ffc0fff0000000

def z850 : W := mkw 0x089900000fc036c0 0x4226400003f00db0 0x18ff00000fc03fc0 0xc63fc00003f00ff0

def z851 : W := mkw 0x83ddfc0005d2c000 0x20f77f000174b000 0xabfffc000fffc003 0xeaffff0003fff000

def z852 : W := mkw 0xc7eefffdb0000245 0x31fbbfff6c000091 0xcffffffff00000cf 0xb3fffffffc000033

def z853 : W := mkw 0x6cbba17b45ed1bf0 0x5b2ee85ed17b46fc 0xacfff03fc0ff00f0 0xab3ffc0ff03fc03c

def z854 : W := mkw 0x10775d76f5dbdbfc 0x041dd75dbd76f6ff 0x0bfff3cfcf3f3f01 0x02fffcf3f3cfcfc0

def z855 : W := mkw 0x4bb903a00fc03480 0x52ee40e803f00d20 0x5bff03c00fc03f03 0xd6ffc0f003f00fc0

def z856 : W := mkw 0x88ddfc0005f6c000 0xa2377f00017db000 0xa9fffc0003ffc002 0xea7fff0000fff000

def z857 : W := mkw 0x8fddfe890ff6e400 0xa3f77fa243fdb900 0xffffffcfcfffff03 0xfffffff3f3ffffc0

def z858 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xaffffc003fffc03f 0xebffff000ffff00f

def z859 : W := mkw 0x48bb017005c012c0 0x522ec05c017004b0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z860 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xa700f3cfcf3f3f31 0x29c03cf3f3cfcfcc

def z861 : W := mkw 0x88ddfc0005f6c000 0xa2377f00017db000 0xaafffc000cffc003 0xeabfff00033ff000

def z862 : W := mkw 0xa444fc0bd03fc934 0xa9113f02f40ff24d 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z863 : W := mkw 0xc7cefed990000001 0x31f3bfb664000000 0xcfffffcfc0000003 0xb3fffff3f0000000

def z864 : W := mkw 0x0766fffdb0000000 0x01d9bfff6c000000 0xcffffffff0000003 0xb3fffffffc000000

def z865 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x8dfffcfff0000000 0xa37fff3ffc000000

def z866 : W := mkw 0x8bddfc0005f6c000 0xa2f77f00017db000 0xabfffc0000ffc003 0xaaffff00003ff000

def z867 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xdffffffff3000703 0xf7fffffffcc001c0

def z868 : W := mkw 0x4bbb03f005c036c0 0x52eec0fc01700db0 0x5bff03f000c03fc3 0x96ffc0fc00300ff0

def z869 : W := mkw 0x089900000ff6c000 0x8226400003fdb000 0x28ff00000fffc000 0xca3fc00003fff000

def z870 : W := mkw 0x281100024fc93ff0 0x4a04400093f24ffc 0x100000000fc03ff0 0x4400000003f00ffc

def z871 : W := mkw 0x8bddfe800ff6c000 0xa2f77fa003fdb000 0xebffffc00fffc003 0xfafffff003fff000

def z872 : W := mkw 0xc7eaebfd20000001 0x31fabaff48000000 0xcffff3ffc0000003 0xb3fffcfff0000000

def z873 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x59ff03f003c03fc0 0x967fc0fc00f00ff0

def z874 : W := mkw 0x47aeb7f990000000 0x11ebadfe64000000 0xcffffffff0000003 0xb3fffffffc000000

def z875 : W := mkw 0x87ecfd2db0000001 0x21fb3f4b6c000000 0xcfffff3ff0000003 0xb3ffffcffc000000

def z876 : W := mkw 0x8bd9e8000ff6c000 0xa2f67a0003fdb000 0x2bffc0000fffc003 0xcafff00003fff000

def z877 : W := mkw 0x0003005041410350 0x0000c014105040d4 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z878 : W := mkw 0x8c55fc0dbfc036c1 0x63157f036ff00db0 0x9400fc0fffc03fc0 0x65003f03fff00ff0

def z879 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700f3ffff3f3fff 0x7dc03cffffcfcfff

def z880 : W := mkw 0x00524850d4918354 0x00149214352460d5 0xfef0ccf1fcf8c7ff 0xffbc333c7f3e31ff

def z881 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xdfff0ff03fc03fc3 0xf7ffc3fc0ff00ff0

def z882 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xdffffffffc003803 0xf7ffffffff000e00

def z883 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x0bff03f00fc03fc1 0x82ffc0fc03f00ff0

def z884 : W := mkw 0x88dd5c0005f6c000 0xa2375700017db000 0x28ff0c0000ffc000 0x8a3fc300003ff000

def z885 : W := mkw 0x9bddfc042ff6c008 0xa6f77f010bfdb002 0xabfffc003fffc00f 0xeaffff000ffff003

def z886 : W := mkw 0x4fbb03f90fc036c0 0x53eec0fe43f00db0 0x5fff03ffcfc03fc3 0xd7ffc0fff3f00ff0

def z887 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xcffff3cfc0000003 0x33fffcf3f0000000

def z888 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xfbff33f00fc73fc3 0xfeffccfc03f1cff0

def z889 : W := mkw 0x4bbb03f00fe676c0 0xd2eec0fc03f99db0 0x5bff03f00fc73fc3 0xd6ffc0fc03f1cff0

def z890 : W := mkw 0xc4eefd7db0000001 0x313bbf5f6c000000 0xcdfffcfff0000002 0xb37fff3ffc000000

def z891 : W := mkw 0xc7eefffdb0000241 0x31fbbfff6c000090 0xdffffffff00007c3 0xb7fffffffc0001f0

def z892 : W := mkw 0x281100024ffffff0 0xca04400093fffffc 0x300000000ffffff0 0x4c00000003fffffc

def z893 : W := mkw 0x4722a3fdba240001 0x11c8a8ff6e890000 0xe700f3ffff3f0003 0x79c03cffffcfc000

def z894 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xeffffffffc380003 0xfbffffffff0e0000

def z895 : W := mkw 0x8fddfe890ff6c000 0xa3f77fa243fdb000 0xabffff0e0fffc003 0xeaffffc383fff000

def z896 : W := mkw 0x43ab03f0014036c0 0x50eac0fc00500db0 0x5bff03f003c03fc3 0xd6ffc0fc00f00ff0

def z897 : W := mkw 0x43ab03f00b402640 0x10eac0fc02d00990 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z898 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x19ff00f00fc03fc0 0xc67fc03c03f00ff0

def z899 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xefffff0e0fffc003 0xfbffffc383fff000

def z900 : W := mkw 0x8bddfc04bff6c001 0xa2f77f012ffdb000 0xabfffc003fffc003 0xeaffff000ffff000

def z901 : W := mkw 0xc4eefffdb0000001 0x313bbfff6c000000 0xccfffffff0000000 0xb33ffffffc000000

def z902 : W := mkw 0x83ccfc000a36c000 0xa0f33f00028db000 0xabfffc000f3fc003 0xeaffff0003cff000

def z903 : W := mkw 0x5bbb03f00fd0b6c8 0x56eec0fc03f42db2 0x5bff03f00fc0ffcf 0xd6ffc0fc03f03ff3

def z904 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xdffffffff0c000c3 0xf7fffffffc300030

def z905 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xabfffc000f3fc001 0x2affff0003cff000

def z906 : W := mkw 0x742203fff0093db9 0x1d0880fffc024f6e 0x540003fff0003ffc 0x150000fffc000fff

def z907 : W := mkw 0xe788a28b4a2d2d31 0x39e228a2d28b4b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z908 : W := mkw 0x8c55fc0dbff6c001 0xa3157f036ffdb000 0xa400fc0fffffc000 0x69003f03fffff000

def z909 : W := mkw 0xe7eefffdba242401 0x39fbbfff6e890900 0xcffffffff0000003 0xb3fffffffc000000

def z910 : W := mkw 0x88dd5c000ff6c000 0xa237570003fdb000 0xa9ff3c000fffc002 0xea7fcf0003fff000

def z911 : W := mkw 0x038802800a002400 0x00e200a002800900 0x5bff03c00f003f03 0xd6ffc0f003c00fc0

def z912 : W := mkw 0x0bb901200fc036c0 0x42ee404803f00db0 0x5bff03300fc03fc3 0xd6ffc0cc03f00ff0

def z913 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xfffffc000fffc033 0xffffff0003fff00c

def z914 : W := mkw 0x2400a00b402d0930 0x09002802d00b424c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z915 : W := mkw 0xc7ecffad20000001 0x31fb3feb48000000 0xcfffffcfc0000003 0xb3fffff3f0000000

def z916 : W := mkw 0xc7eaebfdb0000001 0x31fabaff6c000000 0x4fffc3fff0000003 0x93fff0fffc000000

def z917 : W := mkw 0x4fbba3f90fc036c0 0x53eee8fe43f00db0 0x5bff33f1cfc03fc3 0xd6ffccfc73f00ff0

def z918 : W := mkw 0x4b9b02d00fc02640 0x52e6c0b403f00990 0x5bff03c00fc03f03 0xd6ffc0f003f00fc0

def z919 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x7bff03f00fc0ffff 0xdeffc0fc03f03fff

def z920 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x3af0cf3e3cf8f8fd 0xcebc33cf8f3e3e3f

def z921 : W := mkw 0xc7eefffdba36c001 0xb1fbbfff6e8db000 0xefffffffff3fc003 0xfbffffffffcff000

def z922 : W := mkw 0x10251526214a58a8 0x040945498852962a 0xf50f3f3e33c7f8fe 0xfd43cfcf8cf1fe3f

def z923 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0x310f3cf1f3c7c7fc 0xcc43cf3c7cf1f1ff

def z924 : W := mkw 0x342203fff0093ffc 0x0d0880fffc024fff 0x540003fff0003ffc 0x150000fffc000fff

def z925 : W := mkw 0x8bddfe800ff6f6c0 0xe2f77fa003fdbdb0 0xfbffffc00fffffc3 0xfefffff003fffff0

def z926 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xbbfffc000fffc0ff 0xeeffff0003fff03f

def z927 : W := mkw 0x8bddfc000ff6c240 0xa2f77f0003fdb090 0xbbfffc000fffc7c3 0xeeffff0003fff1f0

def z928 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xfbffff000ffff803 0xfeffffc003fffe00

def z929 : W := mkw 0xc7eefffdb0108001 0x31fbbfff6c042000 0xeffffffff038c003 0xbbfffffffc0e3000

def z930 : W := mkw 0x4322a3f00a2436c0 0x50c8a8fc02890db0 0xf300f3f00f3f3fc3 0x7cc03cfc03cfcff0

def z931 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x4dff3ffff0000000 0x937fcffffc000000

def z932 : W := mkw 0x0f11a2890fc036c0 0x43c468a243f00db0 0xd700f3cfcfc03fc3 0x75c03cf3f3f00ff0

def z933 : W := mkw 0x0050480204988820 0x0014120081262208 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z934 : W := mkw 0xcbddfe800ff6e400 0xf2f77fa003fdb900 0xabfffc000fffc003 0xeaffff0003fff000

def z935 : W := mkw 0xcfddfe890ff6c001 0xb3f77fa243fdb000 0xabfffc000fffc003 0xeaffff0003fff000

def z936 : W := mkw 0xc7eefffdb0003481 0x71fbbfff6c000d20 0xcffffffff0003803 0xb3fffffffc000e00

def z937 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x5bff0ff03fc0ffcf 0xd6ffc3fc0ff03ff3

def z938 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xa300f3cfcf3f3f03 0x68c03cf3f3cfcfc0

def z939 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700ffcfff3fff3f 0x7dc03ff3ffcfffcf

def z940 : W := mkw 0x43ee5ff4b0000000 0x10fb97fd2c000000 0xcffffffff0000003 0xb3fffffffc000000

def z941 : W := mkw 0x87cefed990000000 0x21f3bfb664000000 0xcffffffff0000003 0xb3fffffffc000000

def z942 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x0bff03c00fc03f03 0xc2ffc0f003f00fc0

def z943 : W := mkw 0x4c3303fdbfc036c1 0x530cc0ff6ff00db0 0x540003ffffc03fc0 0x550000fffff00ff0

def z944 : W := mkw 0x4bbb01700fc036c0 0x52eec05c03f00db0 0x1bff00300fc03fc3 0xc6ffc00c03f00ff0

def z945 : W := mkw 0x7ff8ebaf2ebcbca8 0x5ffe3aebcbaf2f2a 0x0af0c30e0c383801 0x02bc30c3830e0e00

def z946 : W := mkw 0x67aaa3fb402d0930 0x19eaa8fed00b424c 0xeffff3ffc03f0033 0xbbfffcfff00fc00c

def z947 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x0bfffc000fffc001 0x82ffff0003fff000

def z948 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700f3ffcfff3ff3 0xfdc03cfff3ffcffc

def z949 : W := mkw 0x8bddfc009ff6c004 0xa2f77f0027fdb001 0xabfffc003fffc00f 0xeaffff000ffff003

def z950 : W := mkw 0xa444fc0ff0090931 0x29113f03fc02424c 0x8400fc0ff0000030 0x21003f03fc00000c

def z951 : W := mkw 0xc7eefffdb012c001 0xb1fbbfff6c04b000 0xcffffffff000c003 0xb3fffffffc003000

def z952 : W := mkw 0x4bbb03f42fc036c0 0x52eec0fd0bf00db0 0x5fff03fe3fc03fc3 0xd7ffc0ff8ff00ff0

def z953 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xffff03f00fc03ff3 0xffffc0fc03f00ffc

def z954 : W := mkw 0x8fddfe8dbff6c001 0xa3f77fa36ffdb000 0xefffffcfffffc003 0xfbfffff3fffff000

def z955 : W := mkw 0xc466fffdb036c001 0xb119bfff6c0db000 0xe400fffff03fc000 0x39003ffffc0ff000

def z956 : W := mkw 0x48bb01700fc036c0 0x522ec05c03f00db0 0x59ff00f00fc03fc2 0xd67fc03c03f00ff0

def z957 : W := mkw 0x381100024ffdbff8 0x4e04400093ff6ffe 0x300000000ffffffc 0x4c00000003ffffff

def z958 : W := mkw 0x83dcfc000eb48000 0x20f73f0003ad2000 0xabfffc000fffc003 0xeaffff0003fff000

def z959 : W := mkw 0x0300a0024a2d0930 0x00c02800928b424c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z960 : W := mkw 0x10704926249898a8 0x041c12498926262a 0xaef0cf3e3cf8f8fd 0xabbc33cf8f3e3e3f

def z961 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xeffffc303fffc003 0xfbffff0c0ffff000

def z962 : W := mkw 0x030002824a092d30 0x00c000a092824b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z963 : W := mkw 0x181100024fdbfffc 0x4604400093f6ffff 0x300000000ffffffc 0x4c00000003ffffff

def z964 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x4ffff3fff0000001 0x13fffcfffc000000

def z965 : W := mkw 0x8bddfc000ff6c244 0xa2f77f0003fdb091 0xabfffc000fffc0cf 0xeaffff0003fff033

def z966 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x5bff03f00f003fc1 0x16ffc0fc03c00ff0

def z967 : W := mkw 0xcbbba3f00fe436c0 0xf2eee8fc03f90db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z968 : W := mkw 0x83eefd74b0000000 0x20fbbf5d2c000000 0xcffffffff0000003 0xb3fffffffc000000

def z969 : W := mkw 0x00071452914a4a64 0x0001c514a4529299 0xf60fcf3e3cf8f8ff 0xfd83f3cf8f3e3e3f

def z970 : W := mkw 0xc7aeb7fdb0000001 0x31ebadff6c000000 0x4fff33fff0000003 0x93ffccfffc000000

def z971 : W := mkw 0x47eaebfd20000000 0x11fabaff48000000 0xcffffffff0000003 0xb3fffffffc000000

def z972 : W := mkw 0x642203fb40092d30 0x190880fed0024b4c 0x540003ffc0003f30 0x150000fff0000fcc

def z973 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xf70f3ff1ffc7ffff 0xfdc3cffc7ff1ffff

def z974 : W := mkw 0x80ccfc000036c000 0xa0333f00000db000 0xa8fffc00003fc000 0xaa3fff00000ff000

def z975 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700f3cfcfffffff 0x7dc03cf3f3ffffff

def z976 : W := mkw 0x00071450d1434354 0x0001c5143450d0d5 0xf70ffffff3c7c7ff 0xfdc3fffffcf1f1ff

def z977 : W := mkw 0x8bddfc000ff6e640 0xe2f77f0003fdb990 0xabfffc000fffc703 0xeaffff0003fff1c0

def z978 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xdffffffff00000ff 0xb7fffffffc00003f

def z979 : W := mkw 0x4b9b02d00fc036c0 0x52e6c0b403f00db0 0x1bff00c00fc03fc3 0xc6ffc03003f00ff0

def z980 : W := mkw 0x4bbb03f00fc276c4 0x52eec0fc03f09db1 0x5bff03f00fc0ffcf 0xd6ffc0fc03f03ff3

def z981 : W := mkw 0x4bba03f00e803480 0x52ee80fc03a00d20 0x5bff03f00f003f03 0xd6ffc0fc03c00fc0

def z982 : W := mkw 0x8fddfc0d2ff6c001 0xa3f77f034bfdb000 0xabfffc0e0fffc003 0xeaffff0383fff000

def z983 : W := mkw 0x8bddfc042ff6c000 0xa2f77f010bfdb000 0xaffffc0e3fffc003 0xebffff038ffff000

def z984 : W := mkw 0xcfeefffdba240001 0xb3fbbfff6e890000 0xcffffffff0000003 0xb3fffffffc000000

def z985 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x8bffffcfc0000003 0xa2fffff3f0000000

def z986 : W := mkw 0x1043485621588a68 0x0410d2158856229a 0xf50fccfe33f8c7fe 0xfd43f33f8cfe31ff

def z987 : W := mkw 0x4fbb03fd2fc036c1 0x53eec0ff4bf00db0 0x5bff03fe0fc03fc3 0xd6ffc0ff83f00ff0

def z988 : W := mkw 0xc7eefffdb0001081 0x31fbbfff6c000420 0xdffffffff00038c3 0xb7fffffffc000e30

def z989 : W := mkw 0x8b9db4000fe64000 0xa2e76d0003f99000 0xabfff0000fff0003 0xeafffc0003ffc000

def z990 : W := mkw 0x0b99a0000ff6c000 0x82e6680003fdb000 0xabfff0000fffc003 0xeafffc0003fff000

def z991 : W := mkw 0x281100024fffef74 0x8a04400093fffbdd 0x300000000ffffffc 0x4c00000003ffffff

def z992 : W := mkw 0x0b9db4000fe64000 0x02e76d0003f99000 0xabfffc000fffc003 0xeaffff0003fff000

def z993 : W := mkw 0xc7eefffdb0024001 0x31fbbfff6c009000 0xeffffffff007c003 0xbbfffffffc01f000

def z994 : W := mkw 0x381100024ffffdb8 0x8e04400093ffff6e 0x300000000ffffffc 0x4c00000003ffffff

def z995 : W := mkw 0xc7eefffdba002401 0x31fbbfff6e800900 0xcffffffffc003803 0xb3ffffffff000e00

def z996 : W := mkw 0x0b9900000fc02400 0x02e6400003f00900 0x1bff00000fc03f03 0xc6ffc00003f00fc0

def z997 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xfbffc3f00ff83fc3 0xfefff0fc03fe0ff0

def z998 : W := mkw 0x40aa03f0000036c0 0x502a80fc00000db0 0x58ff03f000003fc0 0x963fc0fc00000ff0

def z999 : W := mkw 0xe78fb6d9db676755 0x39e3edb676d9d9d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z1000 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xdfffc3fe0fc03fc3 0xf7fff0ff83f00ff0

def z1001 : W := mkw 0xc7eefffdba240001 0x31fbbfff6e890000 0xcffffffff3070003 0xb3fffffffcc1c000

def z1002 : W := mkw 0x083301700fc036c0 0x420cc05c03f00db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1003 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x4bfff3ffc0000003 0x92fffcfff0000000

def z1004 : W := mkw 0x0355fc000ff6c000 0x00d57f0003fdb000 0xabfffc000fffc003 0xeaffff0003fff000

def z1005 : W := mkw 0xc4ee5ffdb0000001 0x313b97ff6c000000 0xcdff3ffff0000002 0xb37fcffffc000000

def z1006 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xf700ffcfcfffff33 0xfdc03ff3f3ffffcc

def z1007 : W := mkw 0x4bbb03f00ff4b6c0 0xd2eec0fc03fd2db0 0x5bff03f00ff83fc3 0xd6ffc0fc03fe0ff0

def z1008 : W := mkw 0xc7eefffdb0264001 0xb1fbbfff6c099000 0xcffffffff0070003 0xb3fffffffc01c000

def z1009 : W := mkw 0xa444fc0b402d0930 0x29113f02d00b424c 0xa400fc0fc03f0030 0x29003f03f00fc00c

def z1010 : W := mkw 0xc7eefffdba242401 0x31fbbfff6e890900 0xffffffffff3f3f03 0xffffffffffcfcfc0

def z1011 : W := mkw 0x83dcfc0004b6c000 0xa0f73f00012db000 0xabfffc000cffc003 0xeaffff00033ff000

def z1012 : W := mkw 0xd0ff5d74b5d2d2cd 0x343fd75d2d74b4b3 0x08ff0c3030c0c0cc 0x823fc30c0c303033

def z1013 : W := mkw 0x1070492464919198 0x041c124919246466 0xfdf03cf1f3c7c7fe 0xff7c0f3c7cf1f1ff

def z1014 : W := mkw 0x4fbba3f90fe436c0 0x53eee8fe43f90db0 0xfffff3ffcfff3fc3 0xfffffcfff3ffcff0

def z1015 : W := mkw 0xb444fc0ff03d8939 0x2d113f03fc0f624e 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z1016 : W := mkw 0x87ecffad20000000 0x21fb3feb48000000 0xcffffffff0000003 0xb3fffffffc000000

def z1017 : W := mkw 0x83ccfc0000240000 0x20f33f0000090000 0xabfffc00003f0003 0xaaffff00000fc000

def z1018 : W := mkw 0xc466fffdb00036c1 0x7119bfff6c000db0 0xd400fffff0003fc0 0x35003ffffc000ff0

def z1019 : W := mkw 0xaf88a28b4a2d2d30 0xabe228a2d28b4b4c 0xf700f3cfcf3f3f33 0x7dc03cf3f3cfcfcc

def z1020 : W := mkw 0xc7cefeddb0000001 0x31f3bfb76c000000 0x8ffffccff0000003 0xa3ffff33fc000000

def z1021 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x1aff03300fc03fc1 0xc6bfc0cc03f00ff0

def z1022 : W := mkw 0x87cefc5db0000001 0x21f3bf176c000000 0xcffffcfff0000003 0xb3ffff3ffc000000

def z1023 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x5bff03c00f003f03 0x56ffc0f003c00fc0

def z1024 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x3300f3cfcf3f3f31 0x4cc03cf3f3cfcfcc

def z1025 : W := mkw 0x8055fc0005f6c000 0xa0157f00017db000 0xabfffc000fffc003 0xeaffff0003fff000

def z1026 : W := mkw 0x8bdcfc000eb48000 0xa2f73f0003ad2000 0xabfffc000f3f0003 0xeaffff0003cfc000

def z1027 : W := mkw 0x0700a2890a242400 0x01c028a242890900 0xf700f3cfcf3f3f03 0x7dc03cf3f3cfcfc0

def z1028 : W := mkw 0x8bddfc009ff6c000 0xa2f77f0027fdb000 0xaffffc01ffffc003 0xebffff007ffff000

def z1029 : W := mkw 0x8fddfc099ff6c001 0xa3f77f0267fdb000 0xabfffc01cfffc003 0xeaffff0073fff000

def z1030 : W := mkw 0x4bbba3f00fc036c0 0x52eee8fc03f00db0 0xdbfff3f00fc03fc3 0xf6fffcfc03f00ff0

def z1031 : W := mkw 0x10704926249898a8 0x041c12498926262a 0x5ef0cf3e3cf8f8fd 0x97bc33cf8f3e3e3f

def z1032 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x4effcffff0000001 0x93bff3fffc000000

def z1033 : W := mkw 0xc7eefffdb0348001 0xb1fbbfff6c0d2000 0xcffffffff0380003 0xb3fffffffc0e0000

def z1034 : W := mkw 0x4bbb03f00fc276c0 0x52eec0fc03f09db0 0x7bff03f00fc7ffc3 0xdeffc0fc03f1fff0

def z1035 : W := mkw 0x0b9b02d00fc02640 0x02e6c0b403f00990 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1036 : W := mkw 0x8bddfe800ff6e400 0xa2f77fa003fdb900 0xabffff000ffff803 0xeaffffc003fffe00

def z1037 : W := mkw 0x00341520d4835194 0x000d05483520d465 0xfef03f31fcc7f8ff 0xffbc0fcc7f31fe3f

def z1038 : W := mkw 0x4bab03f00b4036c0 0x52eac0fc02d00db0 0x5bff03f003003fc3 0x96ffc0fc00c00ff0

def z1039 : W := mkw 0x47aaa3fdb0000001 0x11eaa8ff6c000000 0xcffff3fff0000003 0xb3fffcfffc000000

def z1040 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0x8fffffcff0000001 0x23fffff3fc000000

def z1041 : W := mkw 0x301100024ffffffc 0x0c04400093ffffff 0x300000000ffffffc 0x4c00000003ffffff

def z1042 : W := mkw 0x48bb03f005c036c0 0x522ec0fc01700db0 0x5aff03f00cc03fc3 0xd6bfc0fc03300ff0

def z1043 : W := mkw 0x281100024fef7ff4 0x4a04400093fbdffd 0x300000000ffffffc 0x4c00000003ffffff

def z1044 : W := mkw 0x47ae17fdb0000001 0x11eb85ff6c000000 0xcfff3ffff0000003 0xb3ffcffffc000000

def z1045 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0x8bfffc000f3f0003 0xa2ffff0003cfc000

def z1046 : W := mkw 0xc7eefffdb0002401 0x31fbbfff6c000900 0xdffffffff0003f03 0xb7fffffffc000fc0

def z1047 : W := mkw 0x48bb03f00fc036c0 0x522ec0fc03f00db0 0x58ff03f00fc03fc0 0xd63fc0fc03f00ff0

def z1048 : W := mkw 0x0005140041434110 0x000145001050d044 0xf50f3cf1f3c7c7fe 0xfd43cf3c7cf1f1ff

def z1049 : W := mkw 0x44aa03fdb0000001 0x112a80ff6c000000 0x4cff03fff0000000 0x933fc0fffc000000

def z1050 : W := mkw 0x8bdcfc000eb6c000 0xa2f73f0003adb000 0xabfffc000c3fc003 0xaaffff00030ff000

def z1051 : W := mkw 0xc7eefffdb0000001 0x31fbbfff6c000000 0xfffffffff0000033 0xfffffffffc00000c

def z1052 : W := mkw 0x3444fc0ff03fc93c 0x0d113f03fc0ff24f 0xa400fc0ff03fc03c 0x29003f03fc0ff00f

def z1053 : W := mkw 0x9bddfc000ff6d088 0xa6f77f0003fdb422 0xabfffc000fffc0cf 0xeaffff0003fff033

def z1054 : W := mkw 0x8b9db4000ff6c000 0xa2e76d0003fdb000 0x2bff30000fffc003 0xcaffcc0003fff000

def z1055 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0x5aff03f00cc03fc1 0x96bfc0fc03300ff0

def z1056 : W := mkw 0x83cdfc000b664000 0x20f37f0002d99000 0xabfffc000fffc003 0xeaffff0003fff000

def z1057 : W := mkw 0x0b9d14000ff6c000 0x82e7450003fdb000 0xabff3c000fffc003 0xeaffcf0003fff000

def z1058 : W := mkw 0x4bbba3f00ff6f6c0 0xd2eee8fc03fdbdb0 0xfbfff3f00fffffc3 0xfefffcfc03fffff0

def z1059 : W := mkw 0x83cdfc000176c000 0xa0f37f00005db000 0xabfffc0003ffc003 0xeaffff0000fff000

def z1060 : W := mkw 0x4bbb03f00fc036c0 0x52eec0fc03f00db0 0xfbff0ff00fc0ffc3 0xfeffc3fc03f03ff0

def z1061 : W := mkw 0x4bbba3f00fe436c0 0x52eee8fc03f90db0 0x5bff33f00fc73fc3 0xd6ffccfc03f1cff0

def z1062 : W := mkw 0xa444fc0ff03fc931 0xa9113f03fc0ff24c 0xa400fc0ff03fc030 0x29003f03fc0ff00c

def z1063 : W := mkw 0xc7eefffdba0036c1 0x71fbbfff6e800db0 0xdfffffffff003fc3 0xf7ffffffffc00ff0

def z1064 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xfbfffcc00fffc703 0xfeffff3003fff1c0

def z1065 : W := mkw 0x4bbb03f00fd0b6c0 0x52eec0fc03f42db0 0x7bff03f00ff8ffc3 0xdeffc0fc03fe3ff0

def z1066 : W := mkw 0xa044fc02403fc930 0xa8113f00900ff24c 0xa000fc00003fc030 0x28003f00000ff00c

def z1067 : W := mkw 0xcfbba3f90fc036c1 0x73eee8fe43f00db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1068 : W := mkw 0x6f8fb6d9db676754 0x5be3edb676d9d9d5 0x010f30c1c3070700 0x0043cc3070c1c1c0

def z1069 : W := mkw 0x281100024fffc930 0x8a04400093fff24c 0x200000000fffc030 0x4800000003fff00c

def z1070 : W := mkw 0xc7eefffdba002401 0x31fbbfff6e800900 0xcffffffff3000703 0xb3fffffffcc001c0

def z1071 : W := mkw 0x8344fe800a36e400 0xa0d13fa0028db900 0xf300ffc00f3fff03 0x7cc03ff003cfffc0

def z1072 : W := mkw 0x43aa03f000002400 0x10ea80fc00000900 0x5bff03f000003f03 0x96ffc0fc00000fc0

def z1073 : W := mkw 0x8bddfc000ff6c000 0xa2f77f0003fdb000 0xabfffc303fffc0cf 0xeaffff0c0ffff033

def z1074 : W := mkw 0x4bbb03f09fc036c0 0x52eec0fc27f00db0 0x5fff03f1ffc03fc3 0xd7ffc0fc7ff00ff0

def z1075 : W := mkw 0x4fbba3fdbfc036c1 0x53eee8ff6ff00db0 0xdffff3ffffc03fc3 0xf7fffcfffff00ff0

def z1076 : W := mkw 0x00300122048818a0 0x000c004881220628 0xfef0cf3e3cf8f8ff 0xffbc33cf8f3e3e3f

def z1077 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0x5700f3cfcf3f3f31 0x15c03cf3f3cfcfcc

def z1078 : W := mkw 0x2700a28b4a2d2d30 0x09c028a2d28b4b4c 0xc700f3cfcf3f3f03 0x31c03cf3f3cfcfc0

def z1079 : W := mkw 0x4fbba3f90fc036c0 0x53eee8fe43f00db0 0x5bffc3fe0fc03fc3 0xd6fff0ff83f00ff0

def z1080 : W := mkw 0x642203fff0090931 0x190880fffc02424c 0x440003fff0000030 0x110000fffc00000c

def z1081 : W := mkw 0xc7eefffdb0240001 0x31fbbfff6c090000 0xeffffffff03f0003 0xbbfffffffc0fc000

def z1082 : W := mkw 0x6fbba3f90fe436c0 0x5beee8fe43f90db0 0x5bff03f00fc03fc3 0xd6ffc0fc03f00ff0

def z1083 : W := mkw 0x4bba03f00e8036c0 0x52ee80fc03a00db0 0x5bff03f00c003fc3 0x96ffc0fc03000ff0

def z1084 : W := mkw 0xcfeefffdba002401 0x73fbbfff6e800900 0xcffffffff0000003 0xb3fffffffc000000

def z1085 : W := mkw 0x281100024fed2d30 0x0a04400093fb4b4c 0x300000000fff3f30 0x4c00000003ffcfcc

def z1086 : W := mkw 0x2788a28b4a2d2d30 0x09e228a2d28b4b4c 0xfffff3cfcf3f3f33 0xfffffcf3f3cfcfcc

def z1087 : W := mkw 0x87ccfc0900000000 0x21f33f0240000000 0x8ffffc0fc0000003 0xa3ffff03f0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z11,z6]),(0,[z1,z12,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z13,z5,z6])],[(0,[z1,z2,z3,z4,z5,z14,z6]),(0,[z1,z15,z2,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z17,z6])],[(1,[z1,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6]),(0,[z1,z21,z2,z3,z4,z5,z6])],[],[(0,[z22,z1,z2,z18,z4,z5,z6]),(0,[z1,z15,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z23]),(0,[z1,z2,z3,z24,z4,z5,z6]),(1,[z1,z2,z3,z4,z25,z5]),(0,[z1,z2,z3,z4,z5,z6,z26])],[(1,[z1,z2,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z5,z28,z6]),(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z3,z4,z30,z5,z6]),(0,[z1,z2,z3,z4,z5,z31,z6]),(0,[z1,z32,z2,z3,z4,z5,z6]),(1,[z1,z33,z2,z3,z5,z6])],[(1,[z1,z34,z2,z3,z4,z5]),(0,[z35,z1,z36,z3,z4,z5,z6]),(1,[z37,z2,z38,z4,z5,z6]),(0,[z39,z2,z3,z40,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z6])]],
   [[(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z43,z2,z44,z3,z5,z6]),(1,[z1,z2,z3,z4,z5,z45])],[(0,[z1,z2,z46,z3,z4,z5,z6]),(1,[z1,z47,z3,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z49]),(1,[z1,z50,z2,z3,z6,z51]),(0,[z1,z2,z52,z3,z4,z5,z6])],[(0,[z1,z2,z3,z53,z4,z5,z6]),(0,[z1,z2,z3,z54,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z1,z56,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z57,z6]),(0,[z1,z2,z3,z4,z5,z58,z59])],[(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z61]),(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z1,z63,z2,z3,z4,z5,z59])],[(0,[z39,z1,z47,z2,z3,z5,z6]),(0,[z1,z64,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z65,z4,z5,z6])],[(0,[z1,z2,z3,z4,z66,z5,z6]),(0,[z1,z2,z3,z67,z4,z5,z6]),(0,[z1,z2,z3,z10,z11,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z68])],[(1,[z1,z2,z3,z5,z69,z6]),(0,[z1,z2,z3,z10,z70,z5,z6])]],
   [[(0,[z37,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z71,z4,z5,z6])],[(0,[z1,z2,z3,z4,z72,z5,z6]),(0,[z73,z2,z3,z4,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z75]),(0,[z1,z76,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z77,z4,z5,z6])],[(0,[z1,z2,z3,z78,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z79]),(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z81,z1,z2,z3,z4,z5,z6])],[(1,[z82,z2,z83,z4,z5,z6]),(0,[z1,z2,z83,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z84]),(0,[z1,z2,z3,z85,z4,z5,z6]),(0,[z1,z86,z2,z3,z4,z5,z6])],[(0,[z1,z87,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z88,z6]),(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z90,z3,z11,z5,z6]),(0,[z1,z2,z3,z4,z91,z5,z6]),(0,[z1,z2,z3,z4,z92,z5,z6]),(0,[z1,z2,z93,z3,z70,z4,z5])],[(0,[z22,z1,z2,z3,z94,z5,z6]),(0,[z95,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z90,z3,z70,z5,z6]),(0,[z1,z2,z3,z96,z4,z5,z6])],[(1,[z97,z1,z2,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z1,z98,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6]),(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z1,z2,z93,z3,z4,z101,z5])]],
   [[(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z104,z5,z6]),(0,[z1,z32,z2,z3,z105,z5,z6])],[(1,[z1,z106,z2,z3,z4,z6]),(0,[z107,z1,z2,z3,z4,z5,z6]),(0,[z1,z63,z2,z3,z108,z5,z6]),(0,[z1,z2,z3,z4,z5,z69,z6]),(0,[z1,z2,z3,z10,z109,z5,z6])],[(0,[z1,z2,z3,z4,z5,z110,z6]),(0,[z73,z111,z2,z3,z4,z5,z6]),(0,[z112,z1,z2,z3,z4,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z114,z6])],[(0,[z1,z115,z2,z3,z4,z5,z6])],[(0,[z1,z116,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z117,z5,z6]),(0,[z1,z118,z2,z3,z11,z5,z6]),(0,[z1,z2,z93,z3,z4,z5,z59]),(0,[z1,z2,z93,z4,z5,z119,z6])],[(0,[z111,z1,z120,z2,z3,z4,z6]),(0,[z1,z2,z121,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z122]),(0,[z1,z2,z3,z123,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z124]),(0,[z1,z2,z3,z4,z125,z5,z6]),(0,[z1,z50,z2,z3,z5,z6,z51]),(0,[z1,z2,z3,z126,z4,z5,z6])],[(1,[z22,z44,z3,z4,z5,z6]),(0,[z22,z1,z44,z3,z4,z5,z6]),(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z6]),(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z130,z5,z6]),(0,[z1,z2,z3,z10,z67,z5,z6]),(0,[z1,z50,z2,z131,z3,z4,z6])],[(0,[z1,z2,z3,z132,z4,z5,z6]),(0,[z1,z2,z133,z3,z4,z5,z6]),(0,[z1,z47,z134,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z135,z136,z6]),(0,[z1,z2,z3,z10,z4,z5,z137]),(0,[z1,z2,z3,z4,z5,z138,z6]),(1,[z1,z2,z3,z4,z101,z139])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z140]),(0,[z1,z141,z2,z3,z4,z5,z6])],[(0,[z1,z142,z3,z4,z5,z6,z143])],[(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z144,z6]),(0,[z1,z2,z145,z3,z4,z5,z6]),(0,[z1,z2,z146,z3,z4,z5,z6])],[(1,[z147,z1,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z148,z6]),(0,[z1,z149,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z5,z6]),(0,[z1,z2,z3,z4,z151,z6,z59])],[(0,[z1,z2,z3,z4,z5,z152,z6]),(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z1,z63,z12,z2,z3,z4,z5])],[(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z155,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z156,z4,z5,z6]),(0,[z157,z1,z2,z3,z4,z5,z6])],[(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z73,z1,z2,z3,z4,z144,z6]),(0,[z159,z2,z3,z4,z5,z6,z61]),(0,[z1,z2,z3,z4,z5,z6,z160])],[(0,[z161,z1,z2,z3,z4,z5,z6]),(1,[z159,z2,z3,z4,z5,z61]),(0,[z1,z118,z2,z3,z109,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z162]),(0,[z163,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z164,z2,z3,z4,z5,z6]),(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z166,z5,z6]),(0,[z1,z167,z2,z3,z4,z5,z6]),(0,[z1,z168,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z169,z6])],[(0,[z111,z1,z170,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(0,[z1,z2,z3,z4,z5,z6,z171]),(0,[z1,z2,z3,z172,z4,z104,z5]),(0,[z1,z12,z2,z3,z4,z173,z6]),(0,[z1,z12,z2,z3,z174,z4,z5])],[(1,[z1,z175,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z131,z3,z174,z4,z6])],[(0,[z1,z2,z3,z94,z4,z5,z6]),(1,[z1,z176,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z177,z6]),(0,[z1,z134,z2,z3,z9,z5,z6])],[(0,[z1,z2,z178,z3,z4,z5,z6]),(0,[z1,z118,z2,z3,z67,z5,z6])],[(0,[z1,z179,z2,z3,z4,z5,z6]),(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z6,z139])],[(0,[z1,z2,z3,z181,z4,z5,z6]),(0,[z1,z2,z3,z70,z5,z6,z58]),(0,[z1,z2,z3,z70,z4,z5,z139]),(0,[z1,z2,z3,z4,z182,z5,z6])],[(0,[z1,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z183,z4,z5,z6]),(0,[z1,z170,z2,z3,z4,z184,z6]),(1,[z1,z2,z3,z4,z185,z6]),(0,[z1,z32,z2,z3,z174,z4,z5])]],
   [[(0,[z1,z2,z3,z186,z4,z5,z6]),(1,[z1,z15,z187,z4,z5,z6]),(0,[z1,z2,z93,z3,z4,z5,z6]),(0,[z1,z2,z188,z3,z4,z5,z6]),(0,[z1,z2,z3,z174,z4,z101,z5])],[(0,[z1,z2,z189,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z190]),(0,[z1,z191,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z3,z193,z5,z6]),(1,[z1,z2,z3,z4,z5,z194])],[(1,[z1,z2,z3,z4,z5,z195]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z1,z2,z3,z4,z5,z6,z137]),(0,[z1,z197,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z105,z5,z6])],[(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z199])],[(0,[z22,z1,z2,z3,z4,z5,z195]),(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z1,z201,z2,z3,z4,z5,z6]),(0,[z1,z187,z3,z16,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(0,[z1,z2,z203,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z204,z5]),(0,[z1,z2,z3,z4,z205,z6,z59]),(0,[z1,z2,z3,z4,z206,z5,z6])],[(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z1,z47,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z1,z12,z2,z3,z4,z5,z58])],[(0,[z1,z2,z209,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z212,z4,z5,z6])]],
   [[(0,[z1,z213,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z214,z5,z6]),(0,[z1,z215,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z216,z6]),(0,[z1,z217,z2,z3,z4,z5,z6])],[(0,[z1,z218,z2,z3,z4,z5,z6])],[(0,[z1,z34,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z187,z4,z5,z6]),(0,[z219,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z220]),(0,[z1,z2,z221,z3,z4,z5,z6]),(0,[z1,z222,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z223,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z5,z58])],[(0,[z1,z224,z2,z3,z4,z5,z6]),(0,[z1,z2,z225,z3,z4,z5,z6])],[(0,[z1,z175,z2,z44,z3,z4,z6])],[(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z2,z3,z4,z228,z5,z6])],[(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z230,z5,z6])]],
   [[(0,[z180,z1,z231,z2,z3,z4,z5]),(0,[z1,z2,z232,z3,z4,z5,z6]),(0,[z1,z192,z2,z131,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z233])],[(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z235]),(0,[z1,z170,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z236,z4,z5,z6]),(0,[z1,z2,z3,z237,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z238,z6])],[(0,[z1,z2,z3,z4,z5,z6,z239]),(0,[z1,z2,z3,z4,z5,z240,z6]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z242,z6]),(0,[z1,z134,z2,z3,z48,z5,z6]),(0,[z1,z142,z231,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z243,z5,z6]),(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z245,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z246]),(0,[z1,z192,z2,z3,z174,z4,z6]),(0,[z1,z2,z3,z4,z101,z6,z51])],[(0,[z1,z2,z3,z4,z5,z6,z247]),(0,[z1,z248,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z5,z6]),(0,[z1,z2,z3,z250,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z251,z6]),(0,[z1,z2,z252,z3,z4,z5,z6]),(0,[z1,z2,z3,z253,z4,z5,z6])],[(0,[z1,z106,z2,z44,z3,z4,z6]),(0,[z1,z2,z3,z4,z254,z5,z6]),(0,[z37,z1,z2,z38,z4,z5,z6])],[(0,[z255,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z256,z5,z6]),(0,[z1,z257,z2,z3,z4,z5,z6]),(0,[z1,z2,z258,z3,z4,z5,z6]),(0,[z1,z118,z2,z3,z4,z5,z259]),(0,[z1,z2,z3,z260,z4,z5,z6]),(0,[z1,z2,z131,z3,z10,z4,z6]),(0,[z261,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z63,z2,z3,z70,z4,z5]),(0,[z1,z2,z262,z3,z4,z5,z6])],[(0,[z147,z1,z15,z3,z4,z5,z6]),(0,[z1,z2,z3,z263,z4,z5,z6]),(1,[z1,z2,z3,z4,z173,z6]),(0,[z1,z2,z3,z174,z4,z5,z6])],[(0,[z264,z1,z2,z3,z265,z5,z6]),(0,[z1,z63,z2,z3,z4,z101,z5])],[(0,[z22,z1,z2,z3,z4,z27,z6]),(0,[z1,z2,z266,z3,z4,z5,z6]),(0,[z180,z1,z2,z3,z4,z5,z267]),(0,[z1,z268,z2,z3,z4,z104,z6]),(1,[z1,z2,z3,z85,z4,z5])],[(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z37,z147,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z270,z6]),(0,[z1,z2,z3,z4,z184,z74,z6]),(0,[z1,z2,z3,z4,z5,z6,z271]),(1,[z1,z2,z3,z272,z5,z6]),(0,[z1,z63,z2,z3,z272,z5,z6])],[(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z1,z2,z67,z4,z104,z5,z6]),(1,[z1,z2,z3,z4,z274,z6])],[(0,[z1,z2,z3,z4,z275,z5,z6]),(0,[z1,z2,z3,z276,z4,z5,z6]),(0,[z1,z277,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z278,z5,z6])],[(0,[z1,z2,z279,z3,z4,z5,z6]),(1,[z73,z2,z3,z4,z74,z6]),(0,[z1,z2,z3,z280,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z25,z5])]],
   [[(0,[z1,z281,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z282,z5,z6]),(0,[z1,z2,z3,z71,z5,z6,z59]),(0,[z1,z50,z2,z3,z4,z6,z139])],[(0,[z283,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z284,z6]),(0,[z1,z192,z50,z2,z3,z4,z6]),(0,[z285,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z9,z265,z5,z6])],[(0,[z1,z176,z2,z3,z4,z5,z6]),(0,[z2,z3,z40,z4,z265,z5,z6]),(0,[z1,z286,z2,z3,z4,z5,z6])],[(0,[z287,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z267]),(0,[z1,z2,z3,z288,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z61,z143]),(0,[z1,z289,z2,z3,z4,z5,z6]),(1,[z1,z290,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z291]),(0,[z1,z2,z3,z292,z4,z5,z6])],[(0,[z1,z2,z293,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z294,z5,z6]),(0,[z1,z2,z3,z4,z295,z5,z6]),(0,[z1,z192,z2,z3,z4,z92,z6]),(0,[z1,z2,z3,z70,z4,z109,z5])]],
   [[(1,[z1,z2,z3,z4,z296,z6]),(0,[z1,z2,z3,z10,z104,z5,z6]),(0,[z1,z50,z2,z3,z5,z6,z58]),(0,[z1,z2,z3,z4,z101,z6,z139])],[(0,[z1,z2,z3,z4,z297,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z298,z4,z5,z6])],[(0,[z299,z1,z2,z3,z4,z5,z6]),(0,[z147,z1,z3,z16,z4,z5,z6]),(1,[z1,z2,z3,z260,z4,z5])],[(0,[z1,z2,z3,z4,z300,z5,z6]),(0,[z1,z301,z2,z3,z4,z5,z6]),(0,[z1,z170,z2,z3,z4,z302,z6]),(0,[z1,z2,z3,z67,z5,z6,z51])],[(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z1,z304,z2,z3,z4,z5,z6]),(1,[z1,z134,z3,z9,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z6]),(0,[z1,z118,z2,z90,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z6,z51])],[(0,[z305,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z306,z4,z5,z6]),(0,[z82,z1,z15,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z2,z3,z308,z4,z5,z6]),(0,[z1,z2,z3,z309,z4,z5,z6])],[(1,[z1,z2,z3,z4,z31,z6]),(1,[z1,z2,z131,z4,z92,z6]),(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z311,z5,z6])],[(1,[z1,z2,z293,z4,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z314,z2,z3,z4,z5,z6]),(0,[z1,z231,z3,z4,z5,z210,z6]),(0,[z1,z2,z90,z3,z104,z5,z6]),(0,[z1,z2,z3,z96,z4,z11,z5])]],
   [[(0,[z35,z1,z44,z3,z4,z5,z6]),(0,[z1,z315,z2,z3,z4,z5,z6]),(0,[z264,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z316,z3,z4,z5,z6]),(0,[z317,z1,z2,z3,z4,z5,z6]),(0,[z1,z318,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z143]),(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z139])],[(0,[z22,z1,z2,z293,z4,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z176,z2,z44,z3,z5,z6]),(1,[z180,z2,z3,z4,z5,z267]),(0,[z1,z192,z2,z3,z10,z4,z6]),(1,[z1,z2,z3,z4,z114,z6])],[(0,[z1,z2,z3,z4,z321,z5,z6]),(0,[z1,z12,z2,z3,z70,z5,z6])],[(0,[z1,z2,z90,z3,z109,z5,z6]),(0,[z1,z63,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z322,z6]),(0,[z1,z2,z3,z70,z4,z5,z6]),(0,[z1,z2,z323,z3,z4,z5,z6])],[(0,[z35,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z40,z48,z5,z6]),(0,[z73,z1,z120,z2,z3,z4,z6]),(0,[z1,z324,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z325]),(0,[z1,z326,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z327]),(0,[z1,z2,z3,z4,z328,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z1,z192,z2,z4,z5,z136,z6]),(1,[z1,z2,z3,z96,z4,z5])],[(0,[z264,z1,z134,z2,z3,z5,z6]),(0,[z1,z120,z170,z3,z4,z5,z6]),(0,[z1,z2,z329,z3,z4,z5,z6]),(0,[z1,z118,z2,z3,z104,z5,z6]),(0,[z1,z50,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z330,z5,z6]),(0,[z1,z2,z3,z174,z331,z5,z6])],[(0,[z1,z2,z187,z3,z4,z5,z6])]],
   [[(0,[z111,z2,z3,z4,z5,z144,z6]),(0,[z1,z2,z90,z3,z67,z5,z6]),(0,[z332,z1,z2,z3,z4,z5,z6])],[(0,[z333,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z334,z5,z6]),(0,[z1,z2,z3,z335,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z59])],[(0,[z1,z2,z336,z3,z4,z5,z6]),(0,[z1,z2,z3,z337,z4,z5,z6]),(0,[z1,z338,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z204,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z6])],[(0,[z1,z2,z3,z4,z339,z5,z6]),(0,[z1,z2,z3,z4,z340,z5,z6]),(1,[z1,z2,z3,z4,z5,z341])],[(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z343,z6]),(0,[z159,z1,z231,z2,z3,z4,z5]),(0,[z344,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z38,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z345]),(0,[z1,z2,z3,z346,z4,z5,z6]),(0,[z1,z347,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z119,z139])],[(1,[z1,z2,z3,z4,z5,z251]),(0,[z1,z2,z3,z348,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z349,z6]),(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z351,z4,z5,z6]),(0,[z1,z118,z50,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z352])]],
   [[(0,[z73,z1,z170,z2,z3,z4,z6]),(0,[z1,z353,z2,z3,z4,z5,z6])],[(0,[z1,z2,z187,z83,z4,z5,z6]),(0,[z1,z2,z3,z354,z4,z5,z6]),(0,[z1,z2,z3,z355,z4,z5,z6]),(0,[z1,z2,z3,z109,z5,z6,z51])],[(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z1,z357,z2,z3,z4,z5,z6]),(0,[z1,z63,z2,z3,z4,z185,z6]),(0,[z1,z358,z2,z3,z4,z5,z6])],[(1,[z39,z2,z3,z40,z5,z6]),(0,[z1,z2,z3,z4,z5,z359,z6]),(0,[z1,z360,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z174,z5,z6])],[(0,[z1,z2,z3,z4,z361,z5,z6]),(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z1,z363,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z364])],[],[(0,[z1,z2,z3,z365,z4,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z3,z367,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z51])]],
   [[(0,[z1,z2,z3,z4,z5,z368,z6]),(0,[z1,z369,z2,z3,z4,z5,z6]),(0,[z1,z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z296,z5,z6]),(0,[z1,z2,z3,z370,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z139,z59]),(0,[z1,z2,z3,z4,z371,z5,z6])],[(0,[z1,z372,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z40,z5,z6])],[(0,[z1,z373,z2,z3,z4,z5,z6]),(0,[z147,z82,z1,z2,z4,z5,z6]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z92,z5,z136,z6])],[(0,[z1,z15,z187,z3,z4,z5,z6]),(0,[z1,z120,z3,z4,z5,z302,z6]),(0,[z1,z2,z375,z3,z4,z5,z6]),(1,[z1,z268,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z376,z6]),(0,[z1,z2,z131,z3,z4,z136,z6]),(0,[z1,z2,z3,z377,z4,z5,z6]),(0,[z1,z32,z2,z3,z174,z4,z6])],[(1,[z1,z2,z3,z4,z378,z6]),(0,[z1,z2,z3,z4,z265,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z380,z4,z5,z6]),(0,[z1,z2,z381,z3,z4,z5,z6]),(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z3,z348,z5,z6]),(0,[z1,z2,z3,z4,z5,z383,z6]),(0,[z1,z384,z2,z3,z4,z5,z6])],[(0,[z22,z1,z2,z3,z4,z378,z6]),(0,[z1,z2,z3,z385,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z386]),(0,[z1,z2,z3,z4,z5,z6,z387]),(0,[z1,z50,z2,z3,z4,z6,z51]),(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z1,z2,z3,z4,z105,z5,z6])]],
   [[(0,[z1,z2,z389,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z390]),(0,[z1,z2,z391,z3,z4,z5,z6]),(0,[z1,z392,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z5,z6,z51]),(0,[z1,z2,z131,z3,z4,z92,z6]),(1,[z1,z2,z3,z331,z5,z6])],[(0,[z1,z2,z3,z4,z393,z104,z6]),(0,[z1,z2,z3,z4,z5,z6,z394]),(0,[z1,z2,z3,z4,z395,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z396,z4,z5,z6]),(0,[z1,z2,z397,z3,z4,z5,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z399,z6]),(0,[z1,z2,z3,z4,z400,z5,z6]),(0,[z1,z2,z3,z4,z151,z5,z6])],[(0,[z2,z3,z4,z74,z5,z144,z6]),(1,[z1,z2,z3,z193,z5,z6])],[(0,[z1,z401,z2,z3,z4,z5,z6])],[(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z378,z5,z6]),(0,[z1,z2,z3,z403,z4,z5,z6]),(0,[z1,z3,z4,z184,z5,z302,z6])],[(0,[z1,z404,z2,z3,z4,z5,z6]),(0,[z405,z1,z2,z3,z4,z5,z6]),(0,[z406,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z407,z6]),(0,[z1,z408,z2,z3,z4,z5,z6]),(0,[z1,z409,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z180,z1,z142,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z411,z6]),(0,[z1,z47,z2,z3,z9,z5,z6]),(0,[z1,z142,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z109,z5,z119]),(0,[z1,z12,z2,z3,z4,z412,z6])]],
   [[(0,[z36,z2,z44,z3,z4,z5,z6]),(0,[z1,z413,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z414,z6]),(0,[z1,z415,z2,z3,z4,z5,z6]),(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z417,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z418]),(0,[z1,z2,z3,z4,z419,z5,z6]),(1,[z1,z192,z2,z4,z136,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z109,z5])],[(0,[z1,z2,z3,z421,z4,z5,z6]),(0,[z422,z1,z2,z3,z4,z5,z6]),(0,[z1,z423,z2,z3,z4,z5,z6]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z1,z32,z50,z2,z3,z4,z6]),(0,[z1,z2,z426,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z331,z5,z6])],[(0,[z22,z1,z2,z3,z4,z5,z418]),(0,[z427,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z139])],[(0,[z1,z2,z3,z428,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z6]),(0,[z1,z2,z3,z429,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z430,z6])],[(0,[z1,z2,z3,z85,z4,z104,z5])],[(1,[z1,z2,z431,z4,z5,z6]),(0,[z1,z432,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z433,z4,z5,z6]),(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z259]),(0,[z434,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z435,z3,z4,z5,z6]),(0,[z1,z436,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(0,[z1,z63,z2,z3,z4,z274,z6])],[(0,[z82,z2,z83,z3,z4,z5,z6]),(0,[z1,z437,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z93,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z438])],[(0,[z1,z2,z3,z439,z4,z5,z6]),(0,[z1,z440,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z441,z6]),(0,[z1,z2,z3,z4,z442,z5,z6]),(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z1,z2,z3,z4,z205,z5,z6])],[(0,[z1,z444,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z445,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z446])],[(0,[z1,z2,z3,z4,z447,z5,z6]),(0,[z147,z1,z2,z16,z4,z5,z6]),(0,[z1,z142,z2,z3,z4,z5,z143]),(0,[z1,z2,z3,z4,z92,z6,z139]),(1,[z1,z12,z2,z3,z109,z5]),(0,[z1,z2,z3,z4,z101,z5,z6])],[(0,[z1,z2,z448,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z450]),(0,[z1,z2,z3,z67,z5,z6,z58]),(0,[z1,z192,z2,z3,z4,z136,z6]),(0,[z1,z451,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z136,z6]),(0,[z1,z2,z3,z452,z4,z5,z6]),(0,[z453,z1,z2,z3,z4,z5,z6]),(0,[z1,z454,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z455,z6]),(0,[z1,z2,z3,z4,z456,z5,z6]),(0,[z1,z457,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z205,z6]),(0,[z1,z32,z2,z93,z3,z4,z5])]],
   [[(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z458,z5,z6]),(1,[z1,z142,z3,z4,z5,z143]),(0,[z1,z2,z3,z70,z4,z5,z58])],[(0,[z1,z2,z3,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(0,[z1,z32,z2,z3,z10,z4,z6])],[(0,[z1,z2,z3,z460,z4,z5,z6]),(0,[z1,z461,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z462]),(0,[z1,z2,z3,z4,z11,z92,z6])],[(0,[z1,z2,z3,z4,z5,z267,z143])],[(0,[z1,z2,z3,z4,z5,z6,z463])],[(0,[z1,z464,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z465,z5,z6]),(0,[z1,z466,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z467,z4,z5,z6])],[(0,[z468,z1,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z265,z5,z6]),(0,[z1,z2,z469,z3,z4,z5,z6]),(0,[z1,z47,z2,z3,z48,z5,z6]),(0,[z1,z2,z470,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z471,z5,z6])],[(0,[z1,z2,z431,z3,z4,z5,z6])],[(0,[z1,z2,z431,z44,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z472]),(0,[z473,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z474,z6]),(0,[z1,z2,z3,z4,z5,z119,z6])],[(0,[z1,z175,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z475]),(0,[z1,z2,z3,z4,z476,z5,z6]),(0,[z1,z2,z3,z4,z5,z477,z6]),(0,[z1,z2,z478,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z479])],[(0,[z1,z2,z3,z4,z5,z480,z6]),(0,[z1,z2,z3,z4,z5,z6,z481]),(0,[z1,z482,z2,z3,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z302,z6]),(0,[z1,z2,z3,z260,z4,z5,z136]),(0,[z1,z2,z3,z483,z4,z5,z6]),(0,[z1,z63,z32,z2,z3,z4,z5]),(0,[z1,z12,z2,z3,z11,z5,z6]),(0,[z1,z2,z484,z3,z4,z5,z6])],[(0,[z1,z87,z2,z44,z3,z4,z5]),(1,[z264,z2,z3,z265,z5,z6]),(0,[z180,z159,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z485,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z2,z131,z3,z4,z101,z6])],[(0,[z1,z2,z3,z4,z487,z5,z6]),(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z1,z2,z3,z4,z74,z302,z6]),(0,[z1,z2,z3,z4,z489,z5,z6]),(0,[z1,z2,z3,z4,z184,z5,z6])],[(0,[z1,z490,z2,z3,z4,z5,z6]),(0,[z1,z15,z2,z187,z4,z5,z6]),(1,[z1,z170,z3,z4,z184,z6]),(0,[z1,z491,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z412,z6]),(0,[z1,z2,z3,z4,z412,z5,z6])]],
   [[(0,[z1,z3,z9,z4,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z492,z6]),(0,[z1,z2,z3,z4,z5,z6,z493]),(0,[z1,z63,z2,z93,z4,z5,z6]),(0,[z1,z2,z494,z3,z4,z5,z6])],[(0,[z1,z495,z2,z3,z4,z5,z6])],[(0,[z111,z1,z2,z3,z4,z74,z6]),(0,[z1,z496,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6]),(0,[z1,z3,z4,z5,z210,z6,z143]),(0,[z1,z498,z2,z3,z4,z5,z6])],[(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z500,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z501,z5,z6])],[(0,[z1,z106,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z502]),(0,[z1,z2,z3,z4,z5,z503,z6]),(0,[z1,z2,z3,z4,z5,z504,z6]),(0,[z1,z2,z3,z109,z5,z6,z58])],[(0,[z1,z2,z3,z4,z505,z5,z6]),(0,[z1,z2,z3,z506,z4,z5,z6]),(0,[z1,z507,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z508,z6]),(0,[z1,z509,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z73,z1,z2,z3,z4,z74,z6]),(0,[z1,z2,z3,z4,z5,z510,z6]),(0,[z1,z2,z511,z3,z4,z5,z6]),(0,[z1,z512,z2,z3,z4,z5,z6])],[(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z35,z36,z2,z3,z4,z5,z6]),(0,[z1,z515,z2,z3,z4,z5,z6]),(1,[z1,z118,z2,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z516]),(0,[z1,z517,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z109,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z518,z5,z6]),(0,[z1,z118,z2,z3,z4,z296,z6]),(0,[z1,z2,z3,z172,z4,z5,z6]),(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z69,z6,z59]),(0,[z1,z2,z3,z70,z5,z6,z51])],[(0,[z1,z520,z2,z3,z4,z5,z6]),(0,[z1,z521,z2,z3,z4,z5,z6]),(0,[z522,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z523,z5,z6]),(0,[z1,z12,z2,z3,z4,z109,z5])],[(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z525,z5,z6]),(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z58])],[(0,[z159,z1,z142,z2,z3,z4,z5]),(0,[z1,z2,z3,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z527]),(0,[z1,z170,z3,z4,z184,z5,z6]),(0,[z1,z2,z3,z4,z528,z5,z6]),(0,[z1,z529,z2,z3,z4,z5,z6])],[(0,[z37,z1,z15,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z530,z5,z6]),(0,[z1,z2,z531,z3,z4,z5,z6]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z67,z5,z6]),(0,[z1,z2,z131,z3,z4,z5,z6]),(0,[z1,z2,z3,z174,z4,z5,z119])],[(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z1,z2,z4,z5,z119,z6,z59]),(0,[z1,z2,z3,z11,z5,z6,z51])],[(0,[z1,z2,z3,z4,z534,z5,z6]),(0,[z1,z118,z2,z3,z4,z31,z6]),(0,[z1,z192,z2,z3,z4,z5,z45]),(0,[z1,z2,z3,z4,z535,z5,z6])],[(0,[z536,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z70,z5,z58])]],
   [[(0,[z264,z1,z47,z2,z3,z5,z6]),(1,[z1,z2,z90,z67,z5,z6])],[(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z538,z6]),(0,[z82,z1,z2,z3,z4,z5,z6]),(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z540]),(0,[z1,z2,z3,z4,z5,z541,z6])],[(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z543,z4,z5,z6])],[(1,[z1,z43,z2,z3,z5,z6]),(0,[z39,z1,z134,z2,z3,z5,z6]),(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z184,z6]),(0,[z1,z2,z3,z4,z393,z5,z6]),(1,[z1,z2,z3,z172,z4,z5])],[(0,[z180,z1,z2,z3,z4,z5,z61]),(0,[z1,z2,z3,z545,z4,z5,z6]),(0,[z1,z2,z3,z4,z546,z5,z6]),(0,[z1,z547,z2,z3,z4,z5,z6]),(0,[z1,z548,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z272,z4,z5,z6]),(1,[z1,z2,z3,z10,z11,z6]),(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z2,z3,z4,z550,z5,z6])],[(0,[z37,z2,z3,z38,z4,z5,z6]),(0,[z551,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z552]),(0,[z553,z1,z2,z3,z4,z5,z6])],[(0,[z1,z554,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z555,z6]),(0,[z1,z556,z2,z3,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6])],[(0,[z1,z192,z2,z3,z4,z101,z6]),(0,[z1,z2,z3,z4,z5,z558,z6]),(0,[z1,z2,z3,z4,z11,z101,z6])]],
   [[(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z50,z2,z90,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z560])],[(0,[z1,z2,z561,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z562,z2,z3,z4,z5,z6]),(0,[z1,z2,z563,z3,z4,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6])],[],[(1,[z1,z2,z3,z565,z5,z6]),(0,[z82,z1,z2,z83,z4,z5,z6])],[(0,[z1,z566,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z184,z144,z6]),(0,[z1,z2,z3,z4,z5,z6,z567]),(0,[z1,z2,z3,z4,z92,z6,z51])],[(0,[z22,z1,z36,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z565,z5,z6]),(0,[z1,z2,z568,z3,z4,z5,z6]),(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z569,z3,z4,z5,z6]),(0,[z1,z2,z3,z570,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z5,z59])],[(0,[z1,z2,z3,z571,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z572]),(0,[z1,z2,z3,z4,z5,z210,z61]),(0,[z1,z118,z2,z3,z4,z5,z251]),(0,[z1,z2,z3,z4,z5,z114,z6])],[(1,[z1,z120,z3,z4,z302,z6]),(0,[z1,z2,z3,z4,z204,z5,z136]),(0,[z1,z573,z2,z3,z4,z5,z6]),(0,[z1,z574,z2,z3,z4,z5,z6])]],
   [[(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z268,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z341])],[(0,[z1,z2,z3,z4,z5,z6,z576]),(0,[z1,z2,z3,z577,z4,z5,z6]),(0,[z1,z2,z90,z67,z4,z5,z6]),(0,[z1,z2,z3,z174,z4,z6,z139])],[(0,[z1,z34,z2,z44,z3,z4,z5]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z579,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z580]),(0,[z1,z2,z3,z4,z101,z5,z58])],[(0,[z1,z12,z2,z3,z4,z5,z139]),(0,[z1,z2,z581,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z144,z302,z6]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z583,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z584,z5,z6])],[(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z565,z5,z6]),(0,[z1,z2,z3,z4,z585,z5,z6]),(0,[z1,z2,z3,z586,z4,z5,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z120,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z393,z6]),(0,[z1,z33,z2,z3,z4,z5,z6])],[(0,[z1,z588,z2,z3,z4,z5,z6]),(0,[z1,z589,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z136,z6]),(0,[z1,z63,z2,z3,z4,z5,z119]),(0,[z1,z2,z3,z4,z11,z5,z6])],[(0,[z1,z2,z3,z590,z4,z5,z6]),(0,[z1,z2,z3,z4,z591,z5,z6]),(0,[z1,z2,z3,z4,z592,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z593]),(0,[z1,z2,z3,z4,z5,z194,z6]),(0,[z1,z2,z3,z4,z136,z6,z139]),(0,[z594,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z70,z174,z4,z5])]],
   [[(0,[z22,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z193,z5,z6]),(1,[z1,z2,z3,z348,z5,z6]),(0,[z1,z2,z131,z4,z92,z5,z6]),(0,[z1,z2,z3,z4,z185,z5,z6]),(1,[z1,z2,z93,z4,z5,z119]),(0,[z1,z50,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z595])],[(1,[z1,z2,z3,z94,z5,z6]),(0,[z1,z2,z3,z4,z5,z596,z6]),(0,[z1,z290,z2,z3,z4,z109,z6]),(0,[z1,z32,z2,z3,z4,z5,z139])],[(0,[z1,z2,z3,z4,z5,z6,z597]),(0,[z1,z32,z2,z3,z4,z92,z6])],[(0,[z1,z2,z3,z265,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z598]),(0,[z1,z2,z3,z4,z599,z5,z6]),(0,[z1,z63,z2,z4,z5,z6,z59]),(0,[z1,z290,z2,z3,z4,z5,z6])],[(0,[z1,z600,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z601,z4,z5,z6])],[(0,[z1,z2,z602,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z137])],[(1,[z111,z2,z3,z4,z144,z6]),(0,[z1,z603,z2,z3,z4,z5,z6]),(0,[z1,z604,z2,z3,z4,z5,z6]),(0,[z1,z605,z2,z3,z4,z5,z6]),(0,[z1,z606,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z108,z5,z6]),(0,[z1,z50,z2,z3,z10,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z341])],[(0,[z37,z1,z2,z83,z4,z5,z6]),(0,[z607,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z48,z5,z6]),(0,[z1,z608,z2,z3,z4,z5,z6]),(0,[z1,z2,z609,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z119,z58])]],
   [[(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z1,z47,z3,z4,z48,z5,z6]),(0,[z1,z357,z2,z3,z5,z136,z6])],[(0,[z1,z2,z3,z4,z5,z611,z6]),(0,[z1,z612,z2,z3,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z5,z6]),(0,[z1,z2,z613,z3,z4,z5,z6]),(0,[z1,z614,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z5,z6])],[(0,[z1,z2,z3,z4,z615,z5,z6]),(0,[z1,z2,z3,z4,z5,z616,z6]),(0,[z1,z2,z3,z4,z5,z617,z6]),(0,[z1,z118,z2,z4,z104,z5,z6]),(0,[z1,z118,z2,z3,z70,z5,z6]),(0,[z1,z2,z3,z4,z5,z618,z6]),(0,[z1,z2,z3,z4,z5,z6,z619])],[(0,[z620,z1,z2,z3,z4,z5,z6]),(0,[z621,z1,z2,z3,z4,z5,z6])],[(0,[z1,z622,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z623,z6])],[(0,[z1,z2,z624,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z625,z5,z6]),(1,[z1,z2,z3,z5,z135,z6]),(0,[z1,z2,z93,z3,z4,z5,z119])],[(0,[z1,z626,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z3,z4,z5,z194]),(0,[z1,z2,z3,z174,z4,z11,z6]),(0,[z627,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z187,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z108,z5,z6])],[(0,[z264,z1,z2,z3,z40,z5,z6]),(0,[z1,z628,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z629,z5,z6]),(0,[z1,z2,z3,z630,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z195,z6]),(0,[z1,z2,z3,z4,z631,z5,z6]),(0,[z1,z2,z3,z632,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z302,z6]),(0,[z1,z633,z2,z3,z4,z5,z6])],[(0,[z634,z1,z2,z3,z4,z5,z6])],[],[(1,[z1,z87,z2,z3,z4,z5]),(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z636]),(0,[z1,z2,z637,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z212,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z418]),(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z639,z4,z5,z6]),(0,[z1,z2,z640,z3,z4,z5,z6])],[(0,[z1,z2,z641,z3,z4,z5,z6]),(0,[z642,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z159,z1,z2,z3,z4,z5,z61]),(0,[z1,z134,z3,z9,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z135,z6])],[(0,[z1,z643,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z180,z2,z3,z4,z5,z267,z6])],[(0,[z1,z2,z3,z9,z40,z5,z6]),(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z1,z646,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z647,z6])],[(0,[z1,z2,z3,z4,z648,z5,z6])],[(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z649,z5,z6])],[(0,[z1,z2,z3,z650,z4,z5,z6]),(0,[z1,z2,z651,z3,z4,z5,z6]),(0,[z1,z652,z2,z3,z4,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z210]),(0,[z1,z12,z2,z3,z104,z5,z6]),(1,[z1,z357,z2,z3,z5,z6]),(1,[z1,z63,z2,z4,z5,z59]),(0,[z1,z2,z3,z4,z5,z653,z6]),(0,[z1,z2,z3,z654,z4,z5,z6])],[(0,[z97,z1,z2,z44,z4,z5,z6]),(0,[z82,z1,z2,z38,z4,z5,z6]),(0,[z1,z655,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z656,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z259]),(0,[z1,z2,z3,z4,z657,z5,z6])]],
   [[(0,[z1,z2,z658,z3,z4,z5,z6]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z660,z5,z6]),(0,[z1,z2,z3,z661,z4,z5,z6]),(0,[z1,z2,z3,z4,z662,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z663]),(0,[z1,z2,z3,z11,z5,z6,z58])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z664,z2,z3,z4,z5,z6]),(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z667,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z173,z6])],[(0,[z264,z2,z3,z4,z265,z5,z6]),(0,[z1,z668,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z174,z4,z5,z59]),(0,[z1,z2,z3,z4,z669,z5,z6])],[(0,[z1,z2,z3,z670,z4,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z672,z5,z6]),(0,[z1,z2,z3,z4,z673,z5,z6]),(0,[z1,z2,z3,z4,z5,z674,z6])],[(0,[z1,z2,z3,z675,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z676]),(0,[z1,z142,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z677,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z274,z6]),(0,[z1,z2,z3,z4,z25,z5,z6])],[(0,[z1,z2,z678,z3,z4,z5,z6]),(0,[z1,z679,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z680,z6]),(0,[z1,z2,z3,z681,z4,z5,z6]),(0,[z1,z682,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z151,z6])],[(0,[z1,z2,z3,z4,z5,z6,z683]),(0,[z264,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z684,z5,z6]),(0,[z1,z12,z50,z2,z3,z5,z6]),(0,[z1,z32,z2,z3,z4,z101,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z685,z6]),(0,[z1,z2,z3,z174,z4,z6,z51])],[(0,[z1,z2,z3,z686,z4,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6])],[(0,[z37,z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z40,z4,z5,z6]),(0,[z1,z688,z2,z3,z4,z5,z6]),(0,[z1,z2,z689,z3,z4,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z71,z5,z6]),(0,[z1,z32,z2,z3,z4,z109,z5])],[(0,[z1,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z267,z6]),(0,[z2,z3,z4,z5,z267,z6,z61]),(0,[z1,z2,z3,z4,z5,z691,z6]),(0,[z1,z2,z3,z4,z692,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z693]),(1,[z1,z32,z2,z3,z174,z4])],[(0,[z694,z1,z2,z3,z4,z5,z6]),(0,[z2,z83,z3,z38,z4,z5,z6]),(0,[z1,z695,z2,z3,z4,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z143]),(0,[z1,z2,z3,z696,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z697,z6]),(0,[z1,z2,z3,z4,z698,z5,z6]),(0,[z1,z699,z2,z3,z4,z5,z6]),(0,[z700,z1,z2,z3,z4,z5,z6])],[(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z702])],[(0,[z22,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z703,z4,z5,z6]),(0,[z1,z2,z3,z104,z5,z6,z58]),(0,[z1,z2,z3,z4,z5,z6,z704]),(0,[z1,z2,z3,z4,z136,z6,z51])],[(0,[z1,z2,z3,z4,z5,z705,z6]),(0,[z1,z706,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z212,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z707,z5,z6]),(0,[z1,z708,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z709,z6]),(0,[z1,z2,z3,z4,z5,z710]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z509,z2,z4,z5,z59]),(0,[z1,z2,z3,z126,z11,z6])],[(0,[z712,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z713,z5,z6]),(0,[z1,z2,z3,z4,z25,z139]),(0,[z1,z2,z3,z669,z5,z58]),(0,[z1,z2,z3,z4,z714,z5]),(0,[z1,z32,z33,z2,z3,z174])],[(0,[z22,z44,z3,z4,z5,z6]),(0,[z1,z2,z715,z4,z5,z6]),(0,[z424,z2,z3,z4,z5,z267]),(0,[z1,z716,z16,z4,z5,z6]),(0,[z1,z2,z3,z717,z5,z6])],[(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z2,z719,z4,z5,z6]),(0,[z1,z2,z3,z720,z5,z6]),(0,[z1,z2,z3,z10,z70,z139]),(0,[z1,z2,z3,z4,z412,z58]),(0,[z1,z2,z3,z4,z101,z139])],[(0,[z1,z2,z3,z565,z378,z6]),(0,[z1,z2,z3,z721,z5,z6]),(0,[z1,z2,z3,z104,z5,z259]),(0,[z1,z2,z93,z3,z71,z5])],[(0,[z1,z142,z303,z3,z4,z5]),(0,[z1,z3,z4,z5,z6,z722])],[(0,[z1,z2,z3,z4,z723,z6]),(0,[z1,z2,z3,z4,z724,z5]),(0,[z1,z491,z2,z3,z6,z51]),(0,[z1,z12,z2,z3,z331,z5])],[(0,[z1,z2,z3,z4,z725,z6])]],
   [[(1,[z1,z716,z4,z5,z6]),(0,[z1,z2,z3,z348,z5,z194]),(0,[z1,z2,z3,z4,z11,z25])],[(0,[z1,z726,z2,z3,z5,z6]),(0,[z1,z2,z3,z727,z5,z6]),(0,[z1,z118,z2,z85,z104,z5])],[(0,[z1,z2,z3,z94,z5,z195]),(0,[z1,z192,z357,z2,z3,z6]),(0,[z1,z728,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z2,z4,z730,z5,z6]),(0,[z1,z2,z3,z731,z5,z6]),(0,[z1,z2,z3,z4,z296,z259]),(0,[z1,z2,z3,z4,z714,z6])],[(0,[z1,z87,z2,z3,z4,z5]),(0,[z1,z732,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z733,z6]),(0,[z1,z2,z3,z108,z185,z6])],[(0,[z1,z2,z3,z4,z734,z6]),(0,[z1,z2,z3,z4,z378,z418]),(0,[z22,z106,z44,z3,z4,z6]),(0,[z1,z87,z2,z431,z4,z5]),(0,[z1,z134,z316,z3,z5,z6]),(0,[z1,z2,z3,z735,z5,z6]),(0,[z1,z50,z2,z3,z5,z259]),(0,[z1,z12,z268,z2,z3,z6]),(0,[z1,z2,z3,z4,z736,z5]),(0,[z1,z2,z3,z737,z4,z6])],[(0,[z1,z175,z2,z3,z4,z6]),(0,[z1,z142,z3,z4,z5,z722]),(0,[z1,z738,z2,z3,z4,z5]),(0,[z1,z2,z3,z10,z11,z25]),(0,[z1,z32,z2,z3,z4,z114])],[(0,[z2,z739,z38,z4,z5,z6]),(0,[z1,z192,z2,z3,z4,z204]),(0,[z1,z12,z2,z3,z182,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z740]),(0,[z1,z2,z3,z565,z5,z418]),(0,[z1,z741,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z742]),(0,[z1,z2,z3,z4,z5,z743]),(0,[z1,z357,z2,z3,z31,z6]),(0,[z1,z2,z3,z744,z5,z6]),(0,[z1,z2,z3,z174,z105,z6])],[(0,[z1,z2,z3,z745,z5,z6]),(0,[z1,z2,z3,z4,z5,z746]),(0,[z1,z21,z2,z3,z174,z4]),(0,[z1,z2,z3,z11,z101,z58])],[(0,[z1,z2,z3,z747,z5,z6]),(0,[z587,z2,z3,z40,z5,z6]),(0,[z1,z748,z2,z3,z4,z6]),(0,[z1,z3,z9,z720,z5,z6]),(0,[z1,z2,z3,z4,z465,z139]),(0,[z1,z2,z3,z331,z5,z119])],[(0,[z1,z2,z3,z4,z749,z6]),(0,[z1,z2,z3,z4,z5,z750]),(0,[z751,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z193,z136,z6]),(0,[z1,z32,z2,z3,z681,z4]),(0,[z1,z2,z3,z71,z5,z58])],[(0,[z22,z44,z3,z4,z5,z195]),(0,[z1,z752,z2,z3,z4,z6]),(0,[z1,z118,z2,z104,z31,z6]),(0,[z1,z32,z2,z3,z4,z430]),(0,[z1,z2,z3,z11,z173,z6])],[(0,[z1,z2,z3,z753,z5,z6])],[(0,[z1,z2,z3,z4,z5,z259])],[(0,[z642,z2,z3,z4,z74,z6]),(0,[z1,z2,z3,z4,z136,z341])]],
   [[(0,[z1,z2,z3,z4,z754,z6]),(0,[z1,z2,z3,z4,z755,z6]),(0,[z1,z2,z3,z756,z5,z6]),(0,[z1,z2,z3,z4,z204,z5])],[(0,[z1,z2,z3,z757,z5,z6]),(0,[z1,z187,z716,z4,z5,z6]),(0,[z1,z2,z3,z10,z657,z6])],[],[(0,[z1,z2,z3,z4,z92,z341]),(0,[z1,z2,z3,z4,z5,z758]),(0,[z1,z2,z3,z70,z5,z137])],[(0,[z1,z2,z3,z4,z759,z6]),(0,[z1,z2,z3,z4,z5,z760])],[(0,[z1,z192,z2,z348,z136,z6]),(0,[z1,z2,z3,z4,z274,z59])],[(0,[z22,z175,z44,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z2,z3,z4,z762,z6])],[(0,[z22,z176,z44,z3,z5,z6]),(0,[z1,z34,z43,z2,z3,z5]),(0,[z1,z2,z3,z109,z173,z6]),(0,[z1,z2,z3,z309,z109,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z3,z4,z101,z45]),(0,[z1,z192,z2,z4,z204,z136])],[(0,[z1,z2,z3,z4,z767,z6]),(0,[z1,z2,z3,z105,z136,z6])],[(0,[z1,z2,z3,z768,z5,z6]),(0,[z1,z32,z2,z3,z174,z4])],[(0,[z2,z3,z4,z5,z769,z6]),(0,[z1,z2,z3,z770,z5,z6]),(0,[z1,z2,z131,z3,z4,z204]),(0,[z1,z2,z3,z4,z771,z6])],[(0,[z772,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z2,z3,z67,z173,z6]),(0,[z1,z774,z2,z3,z4,z6])],[],[(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z4,z776,z6]),(0,[z1,z777,z3,z4,z5,z6]),(0,[z1,z2,z3,z212,z5,z6])],[(0,[z1,z2,z3,z5,z778,z6]),(0,[z1,z2,z3,z779,z4,z6]),(0,[z1,z168,z2,z4,z5,z59]),(0,[z1,z2,z3,z5,z780,z6])]],
   [[(0,[z1,z2,z4,z5,z781,z6]),(0,[z111,z277,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z782,z6]),(0,[z1,z2,z3,z4,z11,z204]),(0,[z1,z2,z3,z4,z205,z109])],[(0,[z159,z2,z3,z4,z5,z783]),(0,[z1,z2,z3,z5,z784,z6]),(0,[z1,z2,z3,z4,z785,z6]),(0,[z1,z2,z3,z174,z193,z6])],[(1,[z2,z739,z4,z5,z6]),(0,[z1,z2,z3,z4,z786,z6]),(0,[z1,z2,z3,z4,z787,z6]),(0,[z1,z2,z3,z4,z5,z788]),(0,[z1,z2,z3,z70,z331,z5]),(0,[z1,z32,z2,z3,z174,z105])],[(0,[z22,z44,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z5,z789]),(0,[z159,z464,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z790,z6]),(0,[z1,z192,z2,z543,z4,z6])],[(0,[z1,z791,z2,z3,z4,z6]),(0,[z1,z2,z792,z3,z4,z5]),(0,[z2,z3,z4,z793,z5,z6]),(0,[z1,z2,z3,z4,z25,z5]),(0,[z1,z2,z3,z10,z96,z5])],[(0,[z1,z2,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z794,z6]),(0,[z1,z795,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z796,z6]),(0,[z1,z33,z2,z3,z5,z6]),(0,[z1,z2,z3,z11,z780,z6])],[(0,[z37,z2,z38,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z274])],[(0,[z1,z2,z3,z4,z797,z6]),(0,[z1,z2,z3,z85,z4,z5]),(0,[z1,z2,z3,z4,z5,z45])]],
   [[(0,[z1,z2,z3,z798,z5,z6]),(0,[z1,z2,z3,z272,z5,z6]),(0,[z1,z2,z3,z4,z204,z139]),(0,[z1,z2,z799,z4,z5,z6]),(1,[z1,z2,z3,z780,z6]),(0,[z1,z2,z3,z4,z25,z51])],[(0,[z1,z2,z800,z4,z5,z6]),(0,[z1,z2,z3,z4,z274,z6]),(0,[z1,z2,z3,z4,z114,z59])],[(0,[z1,z2,z3,z4,z801,z6]),(0,[z1,z2,z581,z4,z92,z6])],[(0,[z73,z2,z3,z4,z74,z6]),(1,[z1,z2,z4,z802,z6]),(0,[z1,z2,z3,z335,z11,z6]),(0,[z1,z32,z50,z2,z3,z58])],[(0,[z1,z2,z3,z4,z5,z803]),(0,[z1,z2,z3,z109,z31,z6])],[(0,[z1,z2,z3,z4,z5,z804]),(0,[z607,z2,z3,z265,z5,z6]),(0,[z1,z2,z3,z4,z5,z805]),(0,[z1,z2,z4,z5,z6,z806])],[(0,[z1,z2,z3,z4,z714,z101])],[(0,[z1,z2,z293,z94,z5,z6]),(0,[z1,z176,z175,z2,z3,z6]),(0,[z1,z2,z3,z5,z807,z6]),(0,[z1,z50,z2,z3,z193,z6])]],
   [[(0,[z37,z2,z739,z4,z5,z6]),(0,[z1,z2,z3,z808,z4,z5]),(0,[z1,z2,z3,z172,z4,z393]),(0,[z1,z2,z3,z4,z412,z109])],[(0,[z1,z444,z3,z9,z5,z6]),(0,[z1,z2,z3,z67,z31,z6]),(0,[z1,z118,z268,z2,z3,z6]),(0,[z1,z192,z2,z4,z802,z6]),(0,[z1,z347,z2,z3,z174,z4])],[(0,[z1,z2,z3,z4,z5,z809]),(0,[z207,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z290,z2,z3,z4,z6])],[(0,[z1,z2,z811,z4,z5,z6]),(0,[z82,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z812,z6]),(0,[z2,z3,z4,z813,z5,z6]),(0,[z814,z2,z3,z4,z5,z6]),(0,[z1,z815,z2,z3,z5,z6])],[(0,[z1,z176,z87,z2,z3,z5]),(0,[z1,z3,z4,z720,z5,z6])],[(0,[z553,z2,z3,z4,z144,z6])],[(0,[z97,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z816,z5]),(0,[z1,z817,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z260,z4,z5]),(0,[z1,z353,z50,z2,z3,z6])],[(0,[z1,z2,z3,z4,z27,z195]),(0,[z1,z819,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z1,z47,z3,z720,z5,z6]),(0,[z1,z2,z3,z272,z185,z6]),(0,[z1,z63,z2,z3,z212,z5])]],
   [[(0,[z1,z106,z2,z3,z4,z6]),(0,[z1,z87,z43,z2,z3,z5]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z2,z3,z4,z101,z341])],[(0,[z22,z44,z293,z4,z5,z6]),(0,[z1,z106,z2,z431,z4,z6]),(0,[z1,z2,z3,z793,z5,z6]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z823,z2,z3,z5,z6]),(0,[z1,z2,z146,z4,z92,z6]),(0,[z1,z2,z93,z77,z4,z5]),(0,[z1,z824,z2,z3,z4,z5])],[(0,[z1,z2,z3,z825,z5,z6]),(0,[z1,z2,z3,z826,z5,z6])],[(0,[z1,z827,z3,z4,z5,z6]),(0,[z1,z32,z2,z3,z4,z25])],[(0,[z1,z2,z18,z4,z378,z6]),(0,[z1,z2,z3,z4,z5,z828]),(0,[z1,z353,z2,z4,z136,z6])],[(0,[z1,z2,z3,z5,z829,z6]),(0,[z1,z2,z3,z830,z5,z6]),(0,[z180,z2,z3,z4,z5,z267]),(0,[z2,z3,z4,z5,z783,z61]),(0,[z1,z2,z3,z4,z831,z5]),(0,[z1,z2,z3,z832,z5,z6]),(0,[z1,z2,z3,z4,z114,z6])],[(0,[z1,z2,z3,z4,z5,z833]),(0,[z1,z2,z3,z834,z4,z5]),(0,[z1,z2,z3,z10,z193,z6]),(0,[z1,z192,z2,z260,z4,z136]),(0,[z1,z2,z3,z4,z205,z139]),(0,[z1,z2,z3,z835,z5,z6]),(0,[z1,z2,z3,z836,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z119,z837]),(0,[z1,z2,z3,z96,z331,z5])]],
   [[(0,[z1,z838,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z839,z6])],[(0,[z1,z2,z3,z4,z840,z6]),(0,[z1,z63,z2,z4,z205,z59]),(0,[z1,z2,z3,z96,z4,z5]),(0,[z1,z491,z2,z3,z5,z58]),(0,[z1,z12,z50,z2,z3,z139])],[(0,[z147,z1,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z841]),(0,[z1,z2,z3,z105,z101,z6])],[(0,[z1,z2,z3,z4,z842,z6]),(0,[z39,z440,z2,z3,z5,z6]),(0,[z1,z843,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z844,z6]),(0,[z1,z2,z3,z4,z845,z6]),(0,[z1,z2,z3,z4,z846,z6]),(0,[z1,z32,z2,z3,z126,z4]),(0,[z1,z2,z3,z331,z101,z5])],[(0,[z1,z12,z2,z3,z172,z5])],[(0,[z1,z2,z484,z67,z5,z6]),(0,[z1,z2,z131,z4,z802,z6])],[(0,[z1,z2,z3,z4,z813,z6]),(0,[z159,z2,z3,z4,z5,z61])],[(0,[z1,z2,z4,z847,z5,z6]),(0,[z1,z2,z3,z848,z5,z6]),(0,[z1,z357,z2,z131,z3,z6]),(0,[z1,z2,z3,z4,z5,z341])]],
   [[(0,[z1,z2,z18,z4,z5,z418]),(0,[z1,z2,z3,z849,z4,z5]),(0,[z1,z2,z3,z331,z5,z59]),(0,[z1,z2,z93,z253,z4,z5])],[(0,[z1,z850,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z41,z139])],[(0,[z1,z176,z2,z3,z5,z6]),(0,[z1,z175,z2,z431,z4,z6]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z2,z3,z4,z5,z251])],[(0,[z1,z176,z2,z431,z5,z6]),(0,[z1,z2,z853,z104,z5,z6])],[(1,[z2,z3,z4,z5,z783]),(0,[z1,z15,z716,z4,z5,z6]),(0,[z1,z2,z3,z4,z31,z259])],[(0,[z1,z2,z3,z94,z378,z6]),(0,[z2,z854,z3,z4,z5,z6]),(0,[z1,z2,z3,z855,z5,z6]),(0,[z1,z192,z2,z4,z136,z45]),(0,[z1,z2,z3,z71,z205,z6]),(0,[z1,z2,z3,z10,z11,z137])],[(0,[z7,z1,z16,z4,z5,z6]),(0,[z1,z2,z3,z4,z856,z6]),(0,[z1,z2,z3,z4,z185,z6]),(0,[z1,z2,z3,z4,z857,z6]),(0,[z1,z33,z2,z3,z173,z6])],[(0,[z39,z2,z3,z40,z5,z6]),(0,[z1,z15,z187,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z2,z3,z4,z74,z813,z6]),(0,[z1,z2,z3,z4,z5,z194]),(0,[z1,z2,z93,z3,z4,z412])],[(0,[z1,z2,z3,z4,z5,z195]),(0,[z1,z2,z860,z4,z5,z6]),(0,[z1,z2,z3,z4,z861,z6]),(0,[z1,z2,z3,z172,z5,z51]),(0,[z1,z2,z3,z105,z5,z6])],[(0,[z37,z80,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z862,z6]),(0,[z1,z2,z3,z4,z5,z863])],[(0,[z1,z864,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z2,z3,z4,z866,z6]),(0,[z1,z12,z2,z3,z321,z5]),(0,[z1,z2,z3,z212,z5,z58])],[(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z430,z6,z51]),(0,[z1,z290,z2,z3,z6,z51])],[(0,[z73,z149,z2,z3,z4,z6]),(0,[z1,z2,z4,z853,z5,z6]),(0,[z1,z2,z3,z868,z5,z6]),(0,[z1,z2,z3,z272,z274,z6]),(0,[z1,z2,z3,z11,z5,z137])],[(0,[z1,z2,z3,z104,z173,z6]),(0,[z1,z869,z2,z3,z4,z6]),(0,[z1,z32,z357,z2,z3,z6]),(0,[z1,z2,z3,z870,z4,z5])],[(0,[z22,z44,z3,z4,z378,z6]),(0,[z2,z83,z739,z4,z5,z6]),(0,[z1,z268,z2,z3,z4,z6]),(0,[z1,z192,z357,z2,z136,z6]),(0,[z1,z2,z3,z4,z204,z51]),(0,[z1,z2,z93,z3,z212,z5])]],
   [[(0,[z1,z2,z3,z4,z871,z6]),(0,[z1,z63,z2,z4,z5,z41])],[(0,[z1,z2,z3,z94,z5,z418]),(0,[z1,z2,z3,z4,z5,z872]),(0,[z1,z2,z3,z204,z5,z135]),(0,[z1,z50,z2,z3,z105,z6])],[(0,[z1,z2,z3,z873,z5,z6]),(0,[z1,z2,z3,z174,z4,z45])],[(0,[z1,z2,z3,z874,z4,z5]),(0,[z1,z2,z3,z4,z875,z5]),(0,[z1,z2,z3,z4,z205,z45]),(0,[z1,z32,z2,z3,z4,z204])],[(0,[z1,z2,z3,z10,z533,z6]),(0,[z1,z2,z3,z331,z5,z6]),(0,[z1,z12,z2,z3,z96,z5])],[(0,[z1,z2,z3,z4,z876,z6]),(0,[z877,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z837]),(0,[z1,z2,z323,z4,z5,z119]),(0,[z1,z32,z2,z3,z174,z331])],[(0,[z1,z176,z34,z2,z3,z5])],[(0,[z39,z2,z3,z793,z5,z6]),(0,[z1,z50,z2,z3,z173,z6]),(0,[z1,z2,z3,z101,z109,z51]),(0,[z1,z12,z2,z3,z5,z878])]],
   [[(0,[z1,z2,z879,z4,z5,z6]),(0,[z1,z880,z2,z3,z4,z6]),(0,[z1,z3,z716,z4,z5,z6]),(1,[z1,z3,z720,z5,z6]),(0,[z1,z357,z2,z3,z11,z6]),(0,[z1,z2,z3,z108,z5,z119]),(0,[z1,z2,z3,z109,z5,z137])],[(0,[z1,z2,z3,z881,z5,z6]),(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z614,z2,z3,z109,z5])],[(0,[z1,z2,z3,z883,z5,z6]),(0,[z1,z353,z2,z104,z5,z6]),(0,[z1,z2,z3,z4,z884,z6])],[(0,[z22,z44,z3,z4,z5,z418]),(0,[z97,z1,z176,z2,z5,z6]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z168,z2,z3,z70,z5])],[(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z293,z4,z27,z6]),(0,[z1,z2,z3,z888,z5,z6]),(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z168,z2,z104,z5,z6]),(0,[z1,z491,z2,z3,z4,z139])],[(0,[z2,z3,z4,z5,z267,z783]),(0,[z1,z118,z2,z669,z5,z6]),(0,[z1,z2,z3,z67,z5,z137]),(0,[z1,z192,z2,z4,z136,z6])],[(0,[z1,z2,z3,z4,z5,z890]),(0,[z1,z32,z2,z3,z108,z5])],[(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z4,z802,z136,z6]),(0,[z1,z2,z252,z3,z4,z101]),(0,[z1,z2,z3,z4,z25,z114]),(0,[z1,z2,z3,z70,z4,z114])]],
   [[(0,[z1,z2,z3,z892,z4,z5]),(0,[z1,z2,z3,z893,z4,z6]),(0,[z1,z2,z3,z4,z173,z6]),(0,[z1,z2,z3,z10,z105,z6])],[(0,[z82,z2,z739,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z894]),(1,[z1,z3,z4,z733,z6]),(0,[z1,z2,z3,z4,z101,z114])],[(0,[z1,z2,z431,z4,z5,z6]),(0,[z1,z2,z3,z4,z895,z6]),(0,[z1,z2,z3,z896,z5,z6]),(0,[z1,z2,z3,z193,z136,z6])],[(0,[z1,z2,z3,z897,z5,z6]),(0,[z264,z2,z3,z793,z5,z6]),(0,[z1,z2,z3,z898,z5,z6]),(0,[z1,z2,z3,z4,z899,z6]),(0,[z1,z2,z3,z104,z31,z6]),(0,[z1,z50,z2,z3,z6,z702])],[(0,[z1,z106,z43,z2,z3,z6]),(0,[z1,z2,z3,z4,z900,z6])],[(0,[z1,z2,z3,z4,z5,z901]),(0,[z1,z2,z3,z11,z284,z6]),(0,[z1,z2,z3,z4,z101,z702]),(0,[z1,z12,z290,z2,z3,z6]),(1,[z1,z2,z3,z4,z714])],[(0,[z1,z2,z3,z193,z92,z6])],[(0,[z1,z2,z3,z11,z5,z259]),(0,[z1,z2,z3,z4,z902,z6]),(0,[z1,z2,z3,z5,z878,z58])]],
   [[(0,[z1,z2,z3,z903,z5,z6]),(0,[z1,z2,z3,z70,z5,z259]),(0,[z1,z118,z2,z3,z172,z5])],[(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z118,z2,z172,z104,z5]),(0,[z1,z12,z2,z3,z109,z5])],[(0,[z1,z2,z3,z4,z5,z904])],[(0,[z1,z2,z3,z4,z905,z6]),(0,[z1,z2,z3,z4,z906,z6]),(0,[z1,z2,z3,z4,z205,z6])],[(0,[z1,z2,z4,z5,z6,z907]),(0,[z1,z142,z3,z4,z5,z143]),(0,[z1,z50,z2,z3,z31,z6]),(0,[z1,z2,z3,z4,z5,z908])],[(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z2,z3,z70,z126,z5]),(0,[z1,z911,z2,z3,z5,z6])],[(0,[z1,z912,z2,z3,z5,z6]),(0,[z1,z192,z2,z4,z136,z194]),(0,[z1,z192,z33,z2,z3,z6]),(0,[z1,z2,z3,z174,z4,z394])],[(0,[z1,z2,z3,z4,z913,z6]),(0,[z1,z176,z106,z2,z3,z6]),(0,[z1,z2,z3,z4,z296,z6]),(0,[z1,z100,z2,z3,z6,z51])]],
   [[(0,[z1,z63,z2,z4,z5,z837]),(0,[z1,z50,z2,z3,z780,z6]),(0,[z1,z33,z2,z3,z11,z6])],[(0,[z1,z2,z914,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z268,z2,z3,z6,z51])],[(0,[z1,z2,z3,z917,z5,z6])],[(0,[z1,z134,z3,z9,z5,z6])],[(0,[z1,z2,z3,z918,z5,z6]),(1,[z1,z2,z853,z5,z6])],[(0,[z1,z2,z3,z919,z5,z6]),(0,[z1,z175,z43,z2,z3,z6]),(0,[z1,z920,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z31,z6]),(0,[z1,z268,z2,z3,z172,z4]),(0,[z1,z2,z3,z85,z4,z393]),(0,[z1,z2,z3,z172,z108,z5]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z131,z4,z92,z6]),(0,[z1,z2,z3,z5,z878,z6])],[(0,[z1,z2,z293,z4,z5,z6]),(0,[z1,z922,z2,z3,z4,z6]),(0,[z923,z2,z3,z4,z5,z6])],[(0,[z1,z2,z739,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z924,z4,z6]),(0,[z1,z2,z129,z3,z70,z5]),(0,[z1,z63,z2,z108,z5,z59])],[(0,[z264,z2,z3,z265,z5,z6]),(0,[z1,z2,z3,z71,z174,z5]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z1,z2,z3,z4,z780,z6])],[(0,[z1,z2,z18,z565,z5,z6]),(0,[z1,z170,z397,z3,z4,z6]),(0,[z1,z2,z3,z4,z296,z251]),(0,[z1,z118,z2,z853,z5,z6])],[(0,[z1,z2,z3,z4,z926,z6]),(0,[z1,z2,z3,z780,z6,z51]),(0,[z1,z2,z3,z70,z5,z878]),(0,[z1,z32,z2,z3,z212,z174])],[(0,[z854,z44,z3,z4,z5,z6]),(0,[z97,z1,z175,z2,z4,z6]),(0,[z1,z118,z268,z2,z104,z6]),(0,[z1,z32,z2,z3,z4,z322])],[(0,[z1,z2,z3,z4,z927,z6]),(0,[z1,z2,z3,z4,z928,z6]),(0,[z1,z2,z3,z4,z5,z929]),(0,[z1,z3,z4,z5,z722,z143]),(0,[z1,z2,z3,z930,z4,z6]),(0,[z1,z2,z3,z174,z4,z205]),(1,[z1,z2,z3,z5,z878])],[(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z932,z2,z3,z4,z5]),(0,[z1,z12,z2,z3,z4,z114])],[(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z2,z3,z70,z4,z274]),(0,[z1,z2,z3,z10,z780,z6])]],
   [[(0,[z1,z2,z3,z4,z31,z251])],[(0,[z97,z1,z87,z2,z4,z5]),(0,[z1,z2,z3,z4,z6,z934]),(0,[z1,z2,z3,z4,z6,z935]),(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z2,z3,z4,z101,z274])],[(0,[z1,z2,z3,z937,z5,z6]),(0,[z1,z2,z938,z4,z5,z6]),(0,[z1,z304,z3,z4,z5,z143]),(0,[z1,z2,z3,z193,z5,z45])],[(0,[z1,z2,z939,z4,z5,z6]),(0,[z1,z2,z3,z940,z4,z5]),(0,[z1,z2,z3,z4,z941,z5]),(0,[z1,z120,z469,z3,z4,z6])],[(0,[z1,z2,z3,z942,z5,z6]),(0,[z73,z2,z3,z4,z813,z6]),(0,[z1,z2,z3,z172,z5,z58]),(0,[z1,z2,z3,z4,z943,z5])],[(0,[z82,z2,z232,z4,z5,z6]),(0,[z1,z357,z2,z3,z6,z139]),(0,[z1,z2,z3,z109,z5,z878])],[(0,[z1,z2,z3,z4,z27,z418]),(0,[z350,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z944,z5,z6])],[(0,[z2,z3,z4,z945,z5,z6]),(0,[z1,z2,z3,z946,z5,z6]),(0,[z1,z290,z2,z3,z6,z58])]],
   [[(0,[z1,z2,z18,z94,z5,z6]),(0,[z1,z2,z293,z4,z5,z195]),(0,[z1,z87,z106,z2,z3,z4]),(0,[z1,z2,z3,z4,z802,z6]),(0,[z1,z2,z3,z212,z5,z137])],[(0,[z1,z120,z3,z4,z733,z6]),(0,[z1,z2,z3,z4,z412,z139])],[(0,[z1,z175,z87,z2,z3,z4]),(0,[z1,z268,z2,z3,z85,z4])],[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z1,z2,z145,z67,z5,z6]),(0,[z1,z2,z3,z193,z101,z6]),(0,[z1,z2,z3,z70,z174,z51])],[(0,[z1,z2,z3,z4,z949,z6]),(0,[z2,z3,z4,z813,z144,z6]),(0,[z1,z2,z3,z348,z5,z45]),(0,[z1,z192,z2,z135,z136,z6]),(0,[z1,z2,z3,z5,z950,z6])],[(0,[z1,z2,z3,z4,z5,z951])],[(0,[z1,z2,z3,z952,z5,z6]),(0,[z1,z118,z2,z543,z5,z6]),(0,[z1,z2,z3,z4,z5,z837])],[(0,[z1,z2,z3,z953,z5,z6])]],
   [[(0,[z1,z2,z93,z4,z5,z837]),(0,[z1,z2,z3,z10,z11,z6])],[(0,[z1,z118,z290,z2,z3,z6]),(0,[z1,z2,z3,z4,z954,z6]),(0,[z1,z2,z3,z108,z101,z5]),(0,[z1,z2,z3,z4,z955,z6])],[],[(0,[z1,z854,z3,z4,z5,z6]),(0,[z1,z2,z3,z956,z5,z6]),(0,[z111,z2,z3,z4,z813,z6]),(0,[z1,z2,z716,z4,z5,z6]),(0,[z1,z2,z3,z957,z4,z5])],[(0,[z1,z2,z3,z4,z378,z6]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z2,z426,z4,z5,z119])],[(0,[z22,z44,z3,z565,z5,z6]),(0,[z22,z854,z3,z4,z5,z6]),(0,[z1,z959,z2,z4,z5,z6]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z1,z170,z3,z4,z733,z6]),(0,[z1,z118,z2,z104,z5,z259])],[(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z962,z2,z4,z5,z6]),(0,[z1,z2,z963,z3,z4,z5]),(0,[z1,z357,z2,z3,z260,z5]),(0,[z1,z2,z3,z108,z5,z59])],[(0,[z1,z2,z3,z565,z5,z6]),(0,[z1,z2,z3,z4,z5,z964]),(0,[z1,z2,z3,z104,z5,z137])]],
   [[(0,[z1,z2,z3,z4,z965,z6]),(0,[z1,z63,z2,z4,z151,z59]),(0,[z1,z2,z3,z10,z96,z11])],[(0,[z147,z1,z716,z4,z5,z6]),(0,[z1,z2,z3,z71,z5,z139])],[(0,[z1,z2,z3,z193,z5,z6]),(0,[z1,z2,z4,z5,z802,z6]),(0,[z1,z33,z2,z131,z3,z6])],[(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z2,z3,z5,z6,z967]),(0,[z1,z120,z3,z4,z302,z6]),(0,[z1,z2,z3,z10,z130,z6])],[(0,[z1,z2,z3,z4,z968,z5]),(0,[z1,z969,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z970]),(0,[z1,z2,z90,z5,z653,z6]),(0,[z1,z63,z2,z71,z5,z59]),(0,[z1,z2,z3,z543,z6,z51])],[(0,[z1,z2,z3,z971,z4,z5]),(0,[z1,z2,z3,z71,z5,z259]),(0,[z1,z2,z3,z4,z972,z6]),(0,[z1,z2,z3,z174,z4,z412]),(0,[z1,z33,z2,z3,z6,z139])],[(0,[z1,z12,z2,z3,z4,z274])],[(0,[z22,z43,z44,z3,z5,z6]),(0,[z973,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z974,z6]),(0,[z1,z2,z3,z174,z4,z657])]],
   [[(0,[z1,z2,z3,z4,z5,z418]),(0,[z1,z2,z975,z4,z5,z6]),(0,[z976,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z2,z3,z4,z205,z58]),(0,[z1,z50,z2,z3,z5,z137])],[(0,[z1,z2,z3,z4,z5,z978]),(0,[z1,z2,z3,z4,z5,z783]),(0,[z1,z2,z3,z979,z5,z6]),(0,[z1,z12,z2,z3,z662,z5])],[(0,[z1,z2,z3,z980,z5,z6]),(0,[z1,z2,z3,z981,z5,z6])],[(0,[z1,z2,z3,z4,z982,z6]),(0,[z1,z2,z3,z4,z983,z6]),(0,[z1,z50,z2,z3,z4,z45])],[(0,[z1,z2,z3,z4,z5,z984]),(0,[z1,z2,z3,z71,z151,z6])],[(0,[z113,z2,z3,z4,z5,z61])],[(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z3,z4,z378,z195]),(0,[z1,z986,z2,z3,z5,z6]),(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z268,z2,z90,z3,z6])],[(0,[z22,z431,z44,z4,z5,z6]),(0,[z1,z2,z3,z4,z989,z6]),(0,[z1,z2,z3,z174,z4,z714])]],
   [[(0,[z22,z34,z44,z3,z4,z5]),(0,[z147,z1,z189,z4,z5,z6]),(0,[z1,z990,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z92,z45])],[(0,[z1,z2,z3,z565,z5,z195]),(0,[z2,z3,z40,z793,z5,z6]),(0,[z1,z2,z3,z4,z5,z137]),(0,[z1,z12,z2,z3,z412,z109])],[(0,[z1,z34,z106,z2,z3,z4]),(0,[z1,z2,z3,z991,z4,z5]),(0,[z111,z2,z3,z4,z144,z6]),(0,[z1,z2,z4,z5,z837,z59])],[(0,[z97,z1,z34,z2,z4,z5]),(0,[z1,z992,z2,z3,z4,z6]),(0,[z1,z2,z90,z3,z172,z5]),(0,[z1,z2,z3,z193,z5,z194])],[(0,[z22,z97,z44,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z993]),(0,[z1,z268,z2,z3,z6,z58])],[(0,[z1,z2,z3,z994,z4,z5])],[(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z2,z3,z4,z204,z274]),(0,[z1,z2,z3,z205,z69,z6]),(0,[z1,z996,z2,z3,z5,z6])],[(0,[z1,z2,z3,z997,z5,z6]),(0,[z1,z50,z2,z624,z3,z6])]],
   [[(0,[z180,z99,z2,z3,z4,z5]),(0,[z1,z2,z131,z3,z4,z25]),(0,[z1,z2,z3,z998,z5,z6]),(0,[z1,z2,z3,z96,z5,z51])],[(0,[z1,z3,z4,z5,z6,z999]),(0,[z1,z231,z569,z3,z4,z5]),(0,[z1,z3,z4,z184,z733,z6]),(0,[z1,z63,z2,z5,z69,z59]),(0,[z1,z2,z3,z309,z11,z6])],[(0,[z1,z2,z3,z1000,z5,z6]),(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z2,z3,z5,z135,z6]),(0,[z1,z2,z3,z10,z4,z45])],[(0,[z1,z1002,z2,z3,z5,z6]),(0,[z1,z2,z131,z4,z371,z6])],[(0,[z1,z2,z3,z4,z5,z1003]),(0,[z1,z1004,z2,z3,z4,z6]),(0,[z1,z175,z34,z2,z3,z4]),(0,[z1,z15,z658,z4,z5,z6]),(0,[z1,z357,z2,z3,z6,z51]),(0,[z1,z12,z2,z3,z5,z430])],[(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z2,z3,z109,z5,z259]),(0,[z1,z2,z3,z174,z4,z341])],[(0,[z1,z2,z1006,z4,z5,z6]),(0,[z1,z2,z3,z1007,z5,z6]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z3,z5,z1009,z6]),(0,[z1,z2,z3,z309,z4,z139])],[(0,[z1,z2,z3,z677,z5,z58])]],
   [[(0,[z1,z2,z3,z4,z5,z1010])],[(0,[z1,z3,z4,z733,z302,z6]),(0,[z1,z32,z2,z3,z331,z5])],[(0,[z1,z2,z3,z4,z1011,z6]),(0,[z1,z2,z3,z67,z5,z259])],[(0,[z2,z3,z793,z265,z5,z6]),(0,[z1,z118,z2,z104,z296,z6]),(0,[z1,z268,z2,z3,z193,z6])],[(0,[z1,z2,z4,z5,z6,z1012])],[(0,[z1,z2,z18,z4,z27,z6]),(0,[z1,z1013,z2,z4,z5,z6]),(0,[z1,z2,z90,z853,z5,z6])],[(0,[z1,z170,z3,z4,z184,z6]),(0,[z1,z63,z2,z4,z669,z5]),(0,[z1,z2,z3,z4,z412,z6]),(0,[z1,z2,z3,z1014,z5,z6])],[(0,[z1,z2,z3,z70,z108,z5]),(0,[z1,z32,z2,z3,z4,z714])]],
   [[(0,[z1,z2,z3,z565,z27,z6]),(0,[z1,z2,z3,z5,z1015,z6]),(0,[z1,z2,z3,z109,z5,z462]),(0,[z1,z290,z2,z3,z10,z6]),(0,[z1,z290,z2,z3,z105,z6])],[(0,[z1,z2,z3,z10,z172,z5]),(0,[z1,z2,z3,z212,z174,z5])],[(0,[z1,z2,z3,z4,z1016,z5]),(0,[z1,z357,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1017,z6]),(0,[z1,z63,z2,z4,z5,z59]),(0,[z1,z2,z3,z71,z109,z5]),(0,[z1,z2,z3,z5,z1018,z6]),(0,[z1,z2,z3,z70,z173,z6]),(0,[z1,z32,z33,z2,z3,z6])],[(0,[z1,z2,z4,z5,z1019,z6]),(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z118,z2,z3,z96,z5]),(0,[z1,z2,z90,z3,z96,z5]),(0,[z1,z50,z2,z3,z4,z341])],[(0,[z97,z1,z106,z2,z4,z6]),(0,[z1,z2,z3,z1021,z5,z6]),(0,[z1,z2,z3,z4,z1022,z5]),(0,[z180,z2,z3,z4,z5,z783]),(0,[z1,z290,z2,z90,z3,z6])],[(0,[z1,z2,z3,z1023,z5,z6]),(0,[z1,z2,z1024,z4,z5,z6]),(0,[z1,z63,z2,z3,z4,z205]),(0,[z1,z32,z2,z3,z10,z109])],[(0,[z1,z2,z3,z4,z1025,z6]),(0,[z1,z118,z2,z104,z5,z6]),(0,[z1,z2,z3,z4,z412,z341]),(0,[z1,z2,z3,z4,z714,z139])],[(0,[z1,z2,z3,z4,z1026,z6]),(0,[z1,z628,z3,z48,z5,z6]),(0,[z1,z1027,z2,z4,z5,z6]),(0,[z1,z2,z3,z212,z109,z5])]],
   [[(0,[z1,z2,z3,z260,z5,z135]),(0,[z1,z509,z2,z3,z4,z101])],[(0,[z22,z87,z44,z3,z4,z5]),(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z2,z3,z1030,z5,z6])],[(0,[z1,z1031,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1032]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z1,z2,z3,z4,z151,z6])],[(0,[z97,z1,z43,z2,z5,z6]),(0,[z1,z1035,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1036,z6]),(0,[z1,z1037,z2,z3,z5,z6]),(0,[z1,z2,z3,z1038,z5,z6]),(0,[z1,z2,z3,z1039,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z2,z3,z1041,z4,z5]),(0,[z1,z2,z3,z1042,z5,z6]),(0,[z1,z509,z2,z4,z136,z6]),(0,[z1,z33,z2,z3,z6,z51])],[(0,[z1,z2,z3,z1043,z4,z5]),(0,[z264,z626,z2,z3,z5,z6]),(0,[z1,z2,z90,z5,z138,z6]),(0,[z1,z2,z131,z4,z523,z6])],[(0,[z1,z2,z3,z94,z27,z6]),(0,[z1,z2,z3,z1044,z4,z5]),(0,[z1,z2,z3,z71,z5,z6]),(0,[z1,z2,z3,z70,z5,z58])],[(0,[z1,z281,z3,z4,z302,z6]),(0,[z1,z2,z90,z67,z5,z6]),(0,[z1,z2,z3,z4,z274,z119]),(0,[z1,z12,z290,z2,z3,z109])]],
   [[(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z2,z3,z4,z5,z1046])],[(0,[z1,z118,z2,z104,z5,z251]),(0,[z1,z2,z3,z1047,z5,z6]),(0,[z1,z63,z2,z4,z185,z59]),(0,[z1,z2,z3,z10,z182,z6])],[(0,[z1,z43,z2,z3,z5,z6]),(0,[z1,z2,z3,z172,z4,z5]),(0,[z1,z2,z3,z105,z92,z6]),(0,[z1,z2,z3,z10,z4,z341])],[(0,[z1,z2,z293,z4,z378,z6]),(0,[z1,z43,z2,z431,z5,z6]),(0,[z1048,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z733,z6]),(0,[z1,z2,z3,z1049,z4,z5])],[(1,[z2,z3,z793,z5,z6]),(0,[z1,z192,z2,z4,z41,z6]),(0,[z1,z63,z2,z3,z71,z5])],[(0,[z22,z44,z18,z4,z5,z6])],[(0,[z1,z2,z293,z565,z5,z6]),(0,[z1,z2,z3,z4,z1050,z6]),(0,[z1,z2,z3,z11,z31,z6]),(0,[z1,z357,z2,z3,z204,z5]),(0,[z1,z2,z3,z70,z5,z702]),(0,[z1,z2,z3,z4,z5,z878])],[(0,[z1,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z2,z3,z1052,z5,z6]),(0,[z1,z2,z3,z70,z31,z6]),(0,[z1,z2,z3,z108,z274,z6])]],
   [[(0,[z1,z2,z3,z4,z1053,z6]),(0,[z1,z21,z2,z3,z109,z5])],[(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z2,z3,z853,z5,z6])],[(0,[z1,z2,z3,z1055,z5,z6])],[(0,[z1,z34,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z1057,z2,z3,z4,z6]),(0,[z1,z2,z3,z1058,z5,z6]),(0,[z1,z2,z3,z10,z11,z341]),(0,[z1,z12,z2,z3,z109,z173])],[(0,[z1,z34,z2,z431,z4,z5]),(0,[z1,z2,z3,z4,z1059,z6])],[(0,[z1,z47,z3,z48,z5,z6]),(0,[z1,z134,z3,z720,z5,z6]),(0,[z1,z50,z2,z3,z6,z51]),(0,[z1,z21,z50,z2,z3,z6]),(0,[z1,z2,z3,z4,z101,z182])],[(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z12,z2,z3,z108,z5])],[(0,[z1,z2,z293,z4,z5,z418]),(0,[z1,z2,z3,z1061,z5,z6]),(0,[z1,z192,z2,z3,z4,z25]),(0,[z1,z2,z3,z5,z1062,z6]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z12,z2,z3,z174,z11])]],
   [[(0,[z1,z2,z3,z151,z69,z6])],[(0,[z1,z2,z3,z4,z1064,z6]),(1,[z2,z3,z4,z813,z6]),(0,[z1,z3,z720,z48,z5,z6]),(0,[z1,z2,z3,z1065,z5,z6]),(0,[z1,z2,z3,z5,z1066,z6]),(0,[z1,z2,z3,z212,z5,z139])],[],[(0,[z1,z2,z3,z5,z6,z1067]),(0,[z1,z3,z4,z1068,z5,z6]),(0,[z1,z2,z3,z5,z69,z6]),(0,[z1,z2,z3,z1069,z4,z5]),(0,[z1,z2,z3,z4,z114,z119])],[(0,[z1,z2,z3,z4,z5,z1070]),(0,[z1,z2,z3,z1071,z5,z6]),(0,[z1,z2,z3,z4,z393,z6]),(0,[z1,z2,z3,z1072,z5,z6])],[(0,[z1,z2,z3,z4,z1073,z6]),(0,[z1,z2,z3,z1074,z5,z6]),(0,[z1,z268,z2,z3,z10,z6]),(0,[z1,z63,z2,z3,z4,z412]),(0,[z1,z2,z93,z3,z4,z205])],[(0,[z22,z44,z3,z94,z5,z6]),(0,[z1,z47,z561,z3,z5,z6]),(0,[z1,z2,z3,z1075,z5,z6]),(1,[z1,z2,z4,z5,z837])],[(0,[z1,z1076,z3,z4,z5,z6]),(0,[z1,z155,z3,z4,z184,z6]),(0,[z1,z2,z3,z348,z5,z6]),(0,[z1,z2,z3,z4,z136,z45]),(0,[z1,z2,z4,z92,z802,z6]),(0,[z1,z2,z93,z4,z5,z119])]],
   [[(0,[z1,z2,z3,z94,z5,z6]),(0,[z1,z2,z1077,z4,z5,z6]),(0,[z1,z2,z1078,z4,z5,z6]),(0,[z1,z2,z3,z1079,z5,z6]),(0,[z1,z2,z3,z4,z1080,z6])],[(0,[z1,z2,z18,z4,z5,z195]),(0,[z1,z315,z187,z4,z5,z6]),(0,[z2,z3,z4,z5,z783,z6]),(0,[z1,z2,z3,z4,z5,z1081])],[],[(0,[z1,z2,z3,z1082,z5,z6]),(0,[z1,z2,z3,z1083,z5,z6]),(0,[z1,z2,z3,z96,z5,z58])],[(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z118,z2,z393,z104,z6])],[(0,[z1,z2,z3,z108,z5,z6]),(0,[z1,z2,z3,z1085,z4,z5]),(0,[z1,z2,z1086,z4,z5,z6])],[(0,[z2,z3,z739,z4,z5,z6]),(0,[z1,z2,z67,z853,z5,z6]),(0,[z1,z63,z2,z272,z5,z59]),(0,[z1,z2,z3,z657,z5,z58])],[(0,[z1,z2,z3,z4,z1087,z5]),(0,[z1,z63,z2,z4,z274,z59]),(0,[z1,z12,z2,z3,z109,z114])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 538) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 538).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1064)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [538, 526] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 236).take 20).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 122, 20] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_47082

theorem PEqualNP.Outside.L_meta_47082 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3907577992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 3907577992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47082.solve