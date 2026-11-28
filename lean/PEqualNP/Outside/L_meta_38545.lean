import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38545

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
  Nat.testBit (4008373992 * 2 ^ 32 + 4008224936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8000180c280c294a#64 ++ 0x40000c06140614a5#64 ++ 0xf724f91c791c7fff#64 ++ 0xfb927c8e3c8e3fff#64 : BitVec 256),
   (0x60094261926194a5#64 ++ 0x3004a130c930ca52#64 ++ 0xffdb46e39ee39ce7#64 ++ 0xffeda371cf71ce73#64 : BitVec 256),
   (0x41628702c702c631#64 ++ 0xa0b1438163816318#64 ++ 0xdd638703e703e739#64 ++ 0x6eb1c381f381f39c#64 : BitVec 256),
   (0x80f407b407b407c1#64 ++ 0xc07a03da03da03e0#64 ++ 0xbafc07fc07fc07c1#64 ++ 0xdd7e03fe03fe03e0#64 : BitVec 256),
   (0x027fe80005db7800#64 ++ 0x013ff40002edbc00#64 ++ 0x7b7ff80007fff801#64 ++ 0x3dbffc0003fffc00#64 : BitVec 256),
   (0x047ff5db78000000#64 ++ 0x023ffaedbc000000#64 ++ 0xf4fffffff8000000#64 ++ 0xfa7ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0200080005db7800 0x0100040002edbc00 0x0b00000007fff801 0x0580000003fffc00

def z1 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z2 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z3 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdd638703e703e739 0x6eb1c381f381f39c

def z4 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z5 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xf724f91c791c7fff 0xfb927c8e3c8e3fff

def z6 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x229c00fc00fc00c0 0x914e007e007e0060

def z7 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdd43060386038421 0x6ea18301c301c210

def z8 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z9 : W := mkw 0x80f4059405940340 0xc07a02ca02ca01a0 0x0024011c011c0300 0x0012008e008e0180

def z10 : W := mkw 0x80f41fbc2fbc2fcb 0xc07a0fde17de17e5 0xfffcfffc7ffc7fff 0xfffe7ffe3ffe3fff

def z11 : W := mkw 0x80f687b407b647c1 0xc07b43da03db23e0 0xfbff87fc07ffe7c1 0xfdffc3fe03fff3e0

def z12 : W := mkw 0x027fe00005d35000 0x013ff00002e9a800 0x085b000006e38000 0x042d80000371c000

def z13 : W := mkw 0x827ff80c2ddf794a 0x413ffc0616efbca5 0xff7ff91c7fffffff 0xffbffc8e3fffffff

def z14 : W := mkw 0x008007b002200681 0x804003d801100340 0x008006e000000000 0x0040037000000000

def z15 : W := mkw 0x809402b402b405c1 0x404a015a015a02e0 0xbadc06fc06fc04c1 0xdd6e037e037e0260

def z16 : W := mkw 0x8000000400040140 0x40000002000200a0 0xf724811c611c67f9 0xfb92408e308e33fc

def z17 : W := mkw 0x627fea6197fbfca5 0x313ff530cbfdfe52 0xfffffee39ffffce7 0xffffff71cffffe73

def z18 : W := mkw 0x60000261922084a5 0x30000130c9104252 0x848006e3980004e6 0xc2400371cc000273

def z19 : W := mkw 0x0162850245024210 0x80b1428122812108 0x0020810061006318 0x001040803080318c

def z20 : W := mkw 0x4000020082008421 0x2000010041004210 0xdd43060386038421 0x6ea18301c301c210

def z21 : W := mkw 0x000018082808280a 0x00000c0414041405 0xd520f90079007f3f 0x6a907c803c803f9f

def z22 : W := mkw 0x821d780c28dd394a 0x410ebc06146e9ca5 0xf73cf91c79fc7fff 0xfb9e7c8e3cfe3fff

def z23 : W := mkw 0x0476b5db78000000 0x023b5aedbc000000 0x84a4bffff8000000 0xc2525ffffc000000

def z24 : W := mkw 0x60000220826194a5 0x300001104130ca52 0xdf43060386e39ce7 0x6fa18301c371ce73

def z25 : W := mkw 0x0476b59a68000000 0x023b5acd34000000 0x0024b91c60000000 0x00125c8e30000000

def z26 : W := mkw 0x647ff7fbfa6194a5 0x323ffbfdfd30ca52 0xfffffffffee39ce7 0xffffffffff71ce73

def z27 : W := mkw 0x007fe80000082800 0x003ff40000041400 0x737ff800011c7801 0x39bffc00008e3c00

def z28 : W := mkw 0x2009426112611485 0x1004a13089308a42 0xbad846e01ee01cc7 0xdd6c23700f700e63

def z29 : W := mkw 0x02000800004b7800 0x010004000025bc00 0x010000000003f800 0x008000000001fc00

def z30 : W := mkw 0x0074022007b00481 0x003a011003d80240 0xbafc06e007fc04c1 0xdd7e037003fe0260

def z31 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xf624f91c781c18c6 0xfb127c8e3c0e0c63

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0d806e000000000 0xd86c037000000000

def z33 : W := mkw 0x84fff7ff7fb407c1 0xc27ffbffbfda03e0 0xfefffffffffc07c1 0xff7ffffffffe03e0

def z34 : W := mkw 0x8000100c28040140 0x40000806140200a0 0xf624f91c791c07c1 0xfb127c8e3c8e03e0

def z35 : W := mkw 0x057ff5db7d024210 0x82bffaedbe812108 0xf4fffffff9006318 0xfa7ffffffc80318c

def z36 : W := mkw 0x81f687b647b647d1 0xc0fb43db23db23e8 0xbafc87fc67fc67d9 0xdd7e43fe33fe33ec

def z37 : W := mkw 0xa0fd47f517f517c5 0xd07ea3fa8bfa8be2 0xbafc47fc1ffc1fc7 0xdd7e23fe0ffe0fe3

def z38 : W := mkw 0x60694761976196a5 0xb034a3b0cbb0cb52 0xfffb47e39fe39fe7 0xfffda3f1cff1cff3

def z39 : W := mkw 0x847ffddf780c294a 0x423ffeefbc0614a5 0xf4fffffff91c6318 0xfa7ffffffc8e318c

def z40 : W := mkw 0x8080059400040340 0xc04002ca000201a0 0x0000011c00000300 0x0000008e00000180

def z41 : W := mkw 0x41028202c702c631 0xa081410163816318 0x4d038003e703e739 0x2681c001f381f39c

def z42 : W := mkw 0xe09d42f592f595e5 0x704ea17ac97acaf2 0xffdf46ff9eff9ce7 0xffefa37fcf7fce73

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0xf700400018001ce7 0xfb8020000c000e73

def z44 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x00ffbfffe0000000 0x007fdffff0000000

def z45 : W := mkw 0x040015db78000000 0x02000aedbc000000 0x848007fff8000000 0xc24003fffc000000

def z46 : W := mkw 0x450017dbfa008631 0xa2800bedfd004318 0x848007fff8000738 0xc24003fffc00039c

def z47 : W := mkw 0x0000020007000601 0x8000010003800300 0x0800000007000701 0x0400000003800380

def z48 : W := mkw 0x020be80005db7800 0x0105f40002edbc00 0x4b03f80007fff801 0x2581fc0003fffc00

def z49 : W := mkw 0x457ff7dbff02c631 0xa2bffbedff816318 0xfdffffffff03e739 0xfeffffffff81f39c

def z50 : W := mkw 0x41000702c2008631 0xa080038161004318 0x84000703e0000738 0x42000381f000039c

def z51 : W := mkw 0x640bf04bf8419024 0x3205f825fc20c812 0x4503f803f8039826 0x2281fc01fc01cc13

def z52 : W := mkw 0x60000220826194a5 0x300001104130ca52 0x0800000006e38000 0x040000000371c000

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0xd520810061006739 0x6a9040803080339c

def z54 : W := mkw 0xc1629f0eef0eef7b 0xe0b14f87778777bd 0xff67ff1fff1fffff 0xffb3ff8fff8fffff

def z55 : W := mkw 0x047ff7fb7a200481 0x023ffbfdbd100240 0xfefffffffee004c1 0xff7fffffff700260

def z56 : W := mkw 0x020be800004b7800 0x0105f4000025bc00 0x7b5bf80006e3f801 0x3dadfc000371fc00

def z57 : W := mkw 0x021d680000d93800 0x010eb400006c9c00 0x221c780000fc1800 0x110e3c00007e0c00

def z58 : W := mkw 0x0009400000411000 0x0004a00000208800 0x7b5b400006e39801 0x3dada0000371cc00

def z59 : W := mkw 0x047ff5db78411000 0x023ffaedbc208800 0xfffffffffee39801 0xffffffffff71cc00

def z60 : W := mkw 0x0062850240000000 0x0031428120000000 0xd4638703e0000000 0x6a31c381f0000000

def z61 : W := mkw 0x0276a00005924000 0x013b500002c92000 0x0000000000000000 0x0000000000000000

def z62 : W := mkw 0x0074000005900000 0x003a000002c80000 0x3a7c000007fc0001 0x1d3e000003fe0000

def z63 : W := mkw 0x0074059000000000 0x003a02c800000000 0xb0fc07fc00000000 0xd87e03fe00000000

def z64 : W := mkw 0x020be800004b7800 0x0105f4000025bc00 0x4103f8000003f800 0x2081fc000001fc00

def z65 : W := mkw 0x040bf04b78000000 0x0205f825bc000000 0x4403f803f8000000 0x2201fc01fc000000

def z66 : W := mkw 0x6009424192419425 0x3004a120c920ca12 0xdd4346039e039c27 0x6ea1a301cf01ce13

def z67 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x08db06e386e38000 0x046d8371c371c000

def z68 : W := mkw 0xe0095a6dba6dbdef 0x7004ad36dd36def7 0xffffffffffffffff 0xffffffffffffffff

def z69 : W := mkw 0x80f4059405940340 0xc07a02ca02ca01a0 0xb0fc07fc011c0300 0xd87e03fe008e0180

def z70 : W := mkw 0x000018082808280a 0x00000c0414041405 0xf524f91c7800783e 0xfa927c8e3c003c1f

def z71 : W := mkw 0xe000126dba2485ef 0x70000936dd1242f7 0x848007fff80007fe 0xc24003fffc0003ff

def z72 : W := mkw 0x047fe5d350000000 0x023ff2e9a8000000 0xb0ff07ff80000000 0xd87f83ffc0000000

def z73 : W := mkw 0x007fe00000000000 0x003ff00000000000 0x707ff80000000000 0x383ffc0000000000

def z74 : W := mkw 0x067ffddb7ddb7800 0x033ffeedbeedbc00 0xfffffffffffff801 0xfffffffffffffc00

def z75 : W := mkw 0xe0f407f597b487e5 0xf07a03facbda43f2 0xbefc07ff9ffc07e7 0xdf7e03ffcffe03f3

def z76 : W := mkw 0x027fed9005db7800 0x013ff6c802edbc00 0xfbfffffc07fff801 0xfdfffffe03fffc00

def z77 : W := mkw 0x0000022002200481 0x0000011001100240 0xbad806e006e004c1 0xdd6c037003700260

def z78 : W := mkw 0x41628722c722c6b1 0xa0b1439163916358 0xfffb87e3e7e3e7f9 0xfffdc3f1f3f1f3fc

def z79 : W := mkw 0x0400104b78000000 0x02000825bc000000 0x04000003f8000000 0x02000001fc000000

def z80 : W := mkw 0x0000080000082800 0x0000040000041400 0x0024b800011c6000 0x00125c00008e3000

def z81 : W := mkw 0x067ff5db7dd35000 0x033ffaedbee9a800 0xfcfffffffee38000 0xfe7fffffff71c000

def z82 : W := mkw 0x2000002000611084 0x1000001000308842 0x0200000000e018c6 0x0100000000700c63

def z83 : W := mkw 0x80f405b400b401c0 0x407a02da005a00e0 0xb2fc07fc00fc00c0 0xd97e03fe007e0060

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0xd500000000000421 0x6a80000000000210

def z85 : W := mkw 0xe0fd47f597f597e5 0xf07ea3facbfacbf2 0xffff47ff9fff9fe7 0xffffa3ffcfffcff3

def z86 : W := mkw 0x808000b4002401c0 0x4040005a001200e0 0x008000fc000000c0 0x8040007e00000060

def z87 : W := mkw 0x021d600000d11000 0x010eb00000688800 0x0018000000e00000 0x000c000000700000

def z88 : W := mkw 0x8200080405df794a 0x4100040202efbca5 0x0b00000007ffffff 0x0580000003ffffff

def z89 : W := mkw 0x041d70d938000000 0x020eb86c9c000000 0x209c78fc18000000 0x904e3c7e0c000000

def z90 : W := mkw 0x410002008702c631 0xa080010043816318 0x090000000703e739 0x048000000381f39c

def z91 : W := mkw 0xc1f407b487b6c7f1 0xe0fa03da43db63f8 0xbbfc07fc07ffe7f9 0xddfe03fe03fff3fc

def z92 : W := mkw 0x60000220826194a5 0x300001104130ca52 0xff0040001ee39ce7 0xff8020000f71ce73

def z93 : W := mkw 0x021d680000d93800 0x010eb400006c9c00 0x7b5f780006ff9801 0x3dafbc00037fcc00

def z94 : W := mkw 0x020be00000435000 0x0105f0000021a800 0x0003000000038000 0x000180000001c000

def z95 : W := mkw 0x416bc743d702c631 0xa0b5e3a1eb816318 0xfdfbc7e3ff03e739 0xfefde3f1ff81f39c

def z96 : W := mkw 0x009400b000b00080 0x004a005800580040 0x009800e000e00000 0x004c007000700000

def z97 : W := mkw 0x000018082808280a 0x00000c0414041405 0x4500f8007800783e 0x22807c003c003c1f

def z98 : W := mkw 0x8000000400040140 0x40000002000200a0 0xb224011c011c07c1 0xd912008e008e03e0

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x7300400000001801 0x3980200000000c00

def z100 : W := mkw 0x80629d0e680c294a 0x40314e87340614a5 0xf767ff1ff91c7fff 0xfbb3ff8ffc8e3fff

def z101 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x20df7eff98000000 0x906fbf7fcc000000

def z102 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x087fb80007ffe000 0x043fdc0003fff000

def z103 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xffff87ffe7ffe7f9 0xffffc3fff3fff3fc

def z104 : W := mkw 0x0014000000900000 0x000a000000480000 0x221c000000fc0000 0x110e0000007e0000

def z105 : W := mkw 0x82ffefb407ff7fc1 0xc17ff7da03ffbfe0 0xfbfffffc07ffffc1 0xfdfffffe03ffffe0

def z106 : W := mkw 0x040bf84b7808280a 0x0205fc25bc041405 0x4503f803f800783e 0x2281fc01fc003c1f

def z107 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf5fffffff9006739 0xfafffffffc80339c

def z108 : W := mkw 0x80800224022407c1 0xc0400112011203e0 0x00000000000007c0 0x00000000000003e0

def z109 : W := mkw 0xe089426597f597e5 0xf044a132cbfacbf2 0xffdb46e39fff9fe7 0xffeda371cfffcff3

def z110 : W := mkw 0x0074080005982800 0x003a040002cc1400 0x7b7cf80007fc7801 0x3dbe7c0003fe3c00

def z111 : W := mkw 0x027fed0245db7800 0x013ff68122edbc00 0xff7fff03e7fff801 0x7fbfff81f3fffc00

def z112 : W := mkw 0x410000008002c030 0x2080000040016018 0x010000000003e038 0x008000000001f01c

def z113 : W := mkw 0xe0001a2caa6dbdef 0x70000d165536def7 0xff24f91c7fffffff 0xff927c8e3fffffff

def z114 : W := mkw 0x00628800050a6800 0x0031440002853400 0x7b67f800071ff801 0x3db3fc00038ffc00

def z115 : W := mkw 0x437fe802c5dbf830 0x21bff40162edfc18 0x7f7ff803e7fff839 0x3fbffc01f3fffc1c

def z116 : W := mkw 0x827fe80405df794a 0x413ff40202efbca5 0x7b7ff80007ffffff 0x3dbffc0003ffffff

def z117 : W := mkw 0x457ff7dbfa008631 0xa2bffbedfd004318 0xf4fffffff8000738 0xfa7ffffffc00039c

def z118 : W := mkw 0x000018082808280a 0x00000c0414041405 0x7724f800791c783f 0x3b927c003c8e3c1f

def z119 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xb2bc01fc01fc07c1 0xd95e00fe00fe03e0

def z120 : W := mkw 0x027fe00005d35000 0x013ff00002e9a800 0x7b5b400006e39801 0x3dada0000371cc00

def z121 : W := mkw 0x4000020082008421 0x2000010041004210 0x0900000006038421 0x048000000301c210

def z122 : W := mkw 0x000008000008280a 0x0000040000041405 0x010000000000783e 0x0080000000003c1f

def z123 : W := mkw 0x41028002c002c030 0x2081400160016018 0x45038003e003e038 0x2281c001f001f01c

def z124 : W := mkw 0x616bc763d763d6b5 0xb0b5e3b1ebb1eb5a 0xfffbc7e3ffe3ffff 0xfffde3f1fff1ffff

def z125 : W := mkw 0x0000180828082800 0x00000c0414041400 0xf724f91c791c7801 0xfb927c8e3c8e3c00

def z126 : W := mkw 0xc1f407b6c7b487f1 0xe0fa03db63da43f8 0xbefc07ffe7fc07f9 0xdf7e03fff3fe03fc

def z127 : W := mkw 0x80000804000c294a 0x40000402000614a5 0x00000000011c6318 0x00000000008e318c

def z128 : W := mkw 0x0162850245024210 0x80b1428122812108 0xd4638703e1006318 0x6a31c381f080318c

def z129 : W := mkw 0x8000000400040140 0x40000002000200a0 0x2204001c001c00c0 0x9102000e000e0060

def z130 : W := mkw 0x0276a800059a6800 0x013b540002cd3400 0x0024b800011c6000 0x00125c00008e3000

def z131 : W := mkw 0x0000080000082800 0x0000040000041400 0x7324f800011c7801 0x39927c00008e3c00

def z132 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0x8400011c780007fe 0xc200008e3c0003ff

def z133 : W := mkw 0x0002800240000000 0x0001400120000000 0x44038003e0000000 0x2201c001f0000000

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0xf400400018000000 0xfa0020000c000000

def z135 : W := mkw 0x2009406110611084 0x1004a03088308842 0x229840e018e018c6 0x914c20700c700c63

def z136 : W := mkw 0x0009480000493800 0x0004a40000249c00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z137 : W := mkw 0x60000220826194a5 0x300001104130ca52 0x0b00000006e39ce7 0x058000000371ce73

def z138 : W := mkw 0x0074000005900000 0x003a000002c80000 0x00240000011c0000 0x00120000008e0000

def z139 : W := mkw 0x006bc54350000000 0x0035e2a1a8000000 0xf4fbc7e3f8000000 0xfa7de3f1fc000000

def z140 : W := mkw 0x0074000000000000 0x003a000000000000 0x307c000000000000 0x183e000000000000

def z141 : W := mkw 0x8276b80c2d9e694a 0x413b5c0616cf34a5 0xf724f91c791c7fff 0xfb927c8e3c8e3fff

def z142 : W := mkw 0x6009404190419024 0x3004a020c820c812 0x4503400398039826 0x2281a001cc01cc13

def z143 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x08638703e703e318 0x0431c381f381f18c

def z144 : W := mkw 0x667ffffbfffbfca5 0x333ffffdfffdfe52 0xfffffffffffffce7 0xfffffffffffffe73

def z145 : W := mkw 0x027ff8082ddb780a 0x013ffc0416edbc05 0x7f7ff8007ffff83f 0x3fbffc003ffffc1f

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0xd420810060000000 0x6a10408030000000

def z147 : W := mkw 0x007fe00005900000 0x003ff00002c80000 0x7a7ff80007fc0001 0x3d3ffc0003fe0000

def z148 : W := mkw 0x84f6b59e6d940340 0xc27b5acf36ca01a0 0x0024b91c611c0300 0x00125c8e308e0180

def z149 : W := mkw 0x00f407b007b00681 0x807a03d803d80340 0x08d806e006e00000 0x046c037003700000

def z150 : W := mkw 0x0200000005d35000 0x0100000002e9a800 0x0800000006e38000 0x040000000371c000

def z151 : W := mkw 0x456297dbff02c631 0xa2b14bedff816318 0xdde387ffff03e739 0xeef1c3ffff81f39c

def z152 : W := mkw 0x021d680005db7800 0x010eb40002edbc00 0x2b1c780007fff801 0x158e3c0003fffc00

def z153 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x0a24011c07fc07c1 0x0512008e03fe03e0

def z154 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ff90067ffff39 0x7fbffc8033ffff9c

def z155 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x2204781c181c18c6 0x91023c0e0c0e0c63

def z156 : W := mkw 0xe0fd5ffdbffdbfef 0xf07eaffedffedff7 0xffffffffffffffff 0xffffffffffffffff

def z157 : W := mkw 0x047ffddb78082800 0x023ffeedbc041400 0xf7fffffff91c7801 0xfbfffffffc8e3c00

def z158 : W := mkw 0x808007b4022407c1 0xc04003da011203e0 0xb2a407fc011c07c1 0xd95203fe008e03e0

def z159 : W := mkw 0x80741d9c280c294a 0x403a0ece140614a5 0xf7fcfffc791c7fff 0xfbfe7ffe3c8e3fff

def z160 : W := mkw 0x849d70fd38b401c0 0x424eb87e9c5a00e0 0x229c78fc18fc00c0 0x914e3c7e0c7e0060

def z161 : W := mkw 0x067fe5d355d35000 0x033ff2e9aae9a800 0x08db06e386e38000 0x046d8371c371c000

def z162 : W := mkw 0x0009404110000000 0x0004a02088000000 0xf4db46e398000000 0xfa6da371cc000000

def z163 : W := mkw 0x0000002000200080 0x0000001000100040 0x229800e000e000c0 0x914c007000700060

def z164 : W := mkw 0x040005d350000000 0x020002e9a8000000 0x008006e380000000 0x00400371c0000000

def z165 : W := mkw 0x410002008702c631 0xa080010043816318 0xdd2081006703e739 0x6e9040803381f39c

def z166 : W := mkw 0x8080022407b407c1 0xc040011203da03e0 0x0a00000007fc07c1 0x0500000003fe03e0

def z167 : W := mkw 0x0062950a68000000 0x00314a8534000000 0xf467ff1ff8000000 0xfa33ff8ffc000000

def z168 : W := mkw 0x40000220822084a1 0x2000011041104250 0xffdb06e386e384e1 0xffed8371c371c270

def z169 : W := mkw 0x046295db78000000 0x02314aedbc000000 0xd4e387fff8000000 0xea71c3fffc000000

def z170 : W := mkw 0xe0000a24826dbdef 0x700005124136def7 0x0b00000007ffffff 0x0580000003ffffff

def z171 : W := mkw 0x43628f02c7dbfe31 0xa1b1478163edff18 0xdf638703e7ffff39 0x6fb1c381f3ffff9c

def z172 : W := mkw 0x0062800005024000 0x0031400002812000 0x596380000703e001 0x2cb1c0000381f000

def z173 : W := mkw 0x0000080000082800 0x0000040000041400 0x03000000011c7801 0x01800000008e3c00

def z174 : W := mkw 0x437fef02c7dbfe31 0xa1bff78163edff18 0xff7fff03e7ffff39 0x7fbfff81f3ffff9c

def z175 : W := mkw 0x637fef63d7fbfeb5 0xb1bff7b1ebfdff5a 0xffffffe3ffffffff 0xfffffff1ffffffff

def z176 : W := mkw 0x027fe84115db7800 0x013ff4208aedbc00 0xfffffee39ffff801 0xffffff71cffffc00

def z177 : W := mkw 0x410002008702c631 0xa080010043816318 0xdd4306038703e739 0x6ea18301c381f39c

def z178 : W := mkw 0x8080002400b401c0 0x40400012005a00e0 0x0200000000fc00c0 0x01000000007e0060

def z179 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x0843060386038000 0x04218301c301c000

def z180 : W := mkw 0x046bf54b78000000 0x0235faa5bc000000 0xd463ff03f8000000 0x6a31ff81fc000000

def z181 : W := mkw 0x80000224022405c1 0x40000112011202e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z182 : W := mkw 0xe0fd47f597f597e5 0xf07ea3facbfacbf2 0xbaff07ff87ff87c1 0xdd7f83ffc3ffc3e0

def z183 : W := mkw 0x620bea61926bfca5 0x3105f530c935fe52 0xffdbfee39ee3fce7 0xffedff71cf71fe73

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300000000001ce7 0x0180000000000e73

def z185 : W := mkw 0x000018082808280a 0x00000c0414041405 0x0000780018001806 0x00003c000c000c03

def z186 : W := mkw 0x007d400005d11000 0x003ea00002e88800 0x7b7f400007ff9801 0x3dbfa00003ffcc00

def z187 : W := mkw 0x047fe5d350000000 0x023ff2e9a8000000 0x70fffee380000000 0x387fff71c0000000

def z188 : W := mkw 0x007d45d110000000 0x003ea2e888000000 0xf4ff47ff98000000 0xfa7fa3ffcc000000

def z189 : W := mkw 0x41768702c792c631 0xa0bb438163c96318 0xff7f8703e7ffe739 0x7fbfc381f3fff39c

def z190 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x0b5b000007fff801 0x05ad800003fffc00

def z191 : W := mkw 0x047fe5d350000000 0x023ff2e9a8000000 0x00db06e380000000 0x006d8371c0000000

def z192 : W := mkw 0x8094009400940140 0x404a004a004a00a0 0x0004001c001c0000 0x0002000e000e0000

def z193 : W := mkw 0x41628502c502c230 0xa0b1428162816118 0x45238103e103e338 0x2291c081f081f19c

def z194 : W := mkw 0x0062850245024000 0x0031428122812000 0xdd638703e703e001 0x6eb1c381f381f000

def z195 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x0024b91c611c6318 0x00125c8e308e318c

def z196 : W := mkw 0x847ffddf780c294a 0x423ffeefbc0614a5 0xf7fffffff91c7fff 0xfbfffffffc8e3fff

def z197 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x0bdb06e386e39ce7 0x05ed8371c371ce73

def z198 : W := mkw 0x840015df7804014a 0x42000aefbc0200a5 0x848007fff80007fe 0xc24003fffc0003ff

def z199 : W := mkw 0x84f6b7be6fb407c1 0xc27b5bdf37da03e0 0xbafcbffc67fc07c1 0xdd7e5ffe33fe03e0

def z200 : W := mkw 0x0276a800059a6800 0x013b540002cd3400 0x7324f800011c7801 0x39927c00008e3c00

def z201 : W := mkw 0x808007b407b407c1 0xc04003da03da03e0 0x8a8007fc07fc07c1 0xc54003fe03fe03e0

def z202 : W := mkw 0x0074059005900000 0x003a02c802c80000 0xbafc07fc07fc0001 0xdd7e03fe03fe0000

def z203 : W := mkw 0x41028702c202c631 0xa081438161016318 0xc5038703e003e738 0x6281c381f001f39c

def z204 : W := mkw 0x0062850240000000 0x0031428120000000 0x0043060380000000 0x00218301c0000000

def z205 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfffc87fc67fc67f9 0xfffe43fe33fe33fc

def z206 : W := mkw 0x607d47f1926194a5 0x303ea3f8c930ca52 0xffff47ff9ee39ce7 0xffffa3ffcf71ce73

def z207 : W := mkw 0x2009404110411004 0x1004a02088208802 0x0000400018001806 0x000020000c000c03

def z208 : W := mkw 0x027fea2007fb7c81 0x013ff51003fdbe40 0xfbfffee007fffcc1 0xfdffff7003fffe60

def z209 : W := mkw 0xe0094265926595e5 0x7004a132c932caf2 0xffff47ff9fff9fe7 0xffffa3ffcfffcff3

def z210 : W := mkw 0x80000804000c294a 0x40000402000614a5 0x7324f800011c7fff 0x39927c00008e3fff

def z211 : W := mkw 0x4000020082008421 0x2000010041004210 0x8400060380000420 0x42000301c0000210

def z212 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ff8001ffffce7 0xffbffc000ffffe73

def z213 : W := mkw 0x047ff5db7d900000 0x023ffaedbec80000 0xfefffffffffc0001 0xff7ffffffffe0000

def z214 : W := mkw 0x6009404190419024 0x3004a020c820c812 0x7f5b40039ee39827 0x3fada001cf71cc13

def z215 : W := mkw 0x0262880005db7800 0x0131440002edbc00 0x5b63800007fff801 0x2db1c00003fffc00

def z216 : W := mkw 0x0000100828000000 0x0000080414000000 0xf524f91c79006739 0xfa927c8e3c80339c

def z217 : W := mkw 0x80000804000c294a 0x40000402000614a5 0x03000000011c7fff 0x01800000008e3fff

def z218 : W := mkw 0x021d680000d93800 0x010eb400006c9c00 0x733cf80001fc7801 0x399e7c0000fe3c00

def z219 : W := mkw 0x82fd6fb407fd3fc1 0xc17eb7da03fe9fe0 0xbafc7ffc07fc1fc1 0xdd7e3ffe03fe0fe0

def z220 : W := mkw 0x847ff5df7804014a 0x423ffaefbc0200a5 0xf4fffffff80007fe 0xfa7ffffffc0003ff

def z221 : W := mkw 0x8074180c2d9c294a 0x403a0c0616ce14a5 0xff7cf91c7ffc7fff 0xffbe7c8e3ffe3fff

def z222 : W := mkw 0x8476bd9e680c294a 0x423b5ecf340614a5 0xf724f91c791c7fff 0xfb927c8e3c8e3fff

def z223 : W := mkw 0x8080022407b407c1 0xc040011203da03e0 0xba24011c07fc07c1 0xdd12008e03fe03e0

def z224 : W := mkw 0x067ff84b7ddb7800 0x033ffc25beedbc00 0x7f7ff803fffff801 0x3fbffc01fffffc00

def z225 : W := mkw 0x647ff5dbf8419024 0x323ffaedfc20c812 0xf5fffffff8039826 0xfafffffffc01cc13

def z226 : W := mkw 0x020be800004b7800 0x0105f4000025bc00 0x7327f800011ff801 0x3993fc00008ffc00

def z227 : W := mkw 0x0400159a68000000 0x02000acd34000000 0x0000011c60000000 0x0000008e30000000

def z228 : W := mkw 0x241d70f938611084 0x120eb87c9c308842 0x229c78fc18e018c6 0x914e3c7e0c700c63

def z229 : W := mkw 0x82ffe8b405ff79c0 0x417ff45a02ffbce0 0x7bfff8fc07fff8c1 0xbdfffc7e03fffc60

def z230 : W := mkw 0x808007b4022407c1 0xc04003da011203e0 0x808007fc000007c0 0xc04003fe000003e0

def z231 : W := mkw 0x0014009000000000 0x000a004800000000 0x209c00fc00000000 0x904e007e00000000

def z232 : W := mkw 0x0162850245024210 0x80b1428122812108 0xd520810061006739 0x6a9040803080339c

def z233 : W := mkw 0x6000004190008024 0x30000020c8004012 0x0400000398000026 0x02000001cc000013

def z234 : W := mkw 0xc162970eef06c77b 0xe0b14b87778363bd 0xdd63871fff03e7ff 0xeeb1c38fff81f3ff

def z235 : W := mkw 0x027ff8082ddb7800 0x013ffc0416edbc00 0xff7ff91c7ffff801 0xffbffc8e3ffffc00

def z236 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x2304781c191c7fff 0x91823c0e0c8e3fff

def z237 : W := mkw 0x0076800005924000 0x003b400002c92000 0x7b7f800007ffe001 0x3dbfc00003fff000

def z238 : W := mkw 0x80fd47f517b407c1 0xc07ea3fa8bda03e0 0xfeff47ff9ffc07c1 0xff7fa3ffcffe03e0

def z239 : W := mkw 0xe0095a6dba6dbdef 0x7004ad36dd36def7 0xffdf7eff9eff9ce7 0xffefbf7fcf7fce73

def z240 : W := mkw 0x04fff7fb7fb00681 0x827ffbfdbfd80340 0xfcfffffffee00000 0xfe7fffffff700000

def z241 : W := mkw 0x047ff5db7d024000 0x023ffaedbe812000 0xfdffffffff03e001 0xfeffffffff81f000

def z242 : W := mkw 0x0576b59a6d024210 0x82bb5acd36812108 0x0024b91c61006318 0x00125c8e3080318c

def z243 : W := mkw 0xc1000a04870eef7b 0xe0800502438777bd 0x0b000000071fffff 0x05800000038fffff

def z244 : W := mkw 0x84fff5ff78b401c0 0x427ffaffbc5a00e0 0xf6fffffff8fc00c0 0xfb7ffffffc7e0060

def z245 : W := mkw 0x02ffefb007fb7e81 0x817ff7d803fdbf40 0x7bfffee007fff801 0x3dffff7003fffc00

def z246 : W := mkw 0x0276a80005db7800 0x013b540002edbc00 0x0b24b80007fff801 0x05925c0003fffc00

def z247 : W := mkw 0x6000000080419024 0x300000004020c812 0x0100000000039826 0x008000000001cc13

def z248 : W := mkw 0x4376af02c79aee31 0xa1bb578163cd7718 0xdd67bf03e71fe739 0x6eb3df81f38ff39c

def z249 : W := mkw 0x0060070007000601 0x8030038003800300 0x9860070007000701 0x4c30038003800380

def z250 : W := mkw 0x80f40fb407bc2fc1 0xc07a07da03de17e0 0xfbfcfffc07fc7fc1 0xfdfe7ffe03fe3fe0

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000001006739 0x008000000080339c

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a58000006e00001 0x1d2c000003700000

def z253 : W := mkw 0x62000a2087fbfca5 0x3100051043fdfe52 0x0b00000007fffce7 0x0580000003fffe73

def z254 : W := mkw 0x067fedd355db7800 0x033ff6e9aaedbc00 0x7bfffee387fff801 0x3dffff71c3fffc00

def z255 : W := mkw 0xe0094a65926dbdef 0x7004a532c936def7 0xffdb46e39fffffff 0xffeda371cfffffff

def z256 : W := mkw 0xc100170eea04877b 0xe0800b87750243bd 0x8400071ff80007fe 0xc200038ffc0003ff

def z257 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x2adb46e39ee398c6 0x956da371cf71cc63

def z258 : W := mkw 0x60000261926194a5 0x30000130c930ca52 0x8f8006e39ee39ce7 0xc7c00371cf71ce73

def z259 : W := mkw 0x827ff80c2ddf794a 0x413ffc0616efbca5 0x7b7ff91c67fffb19 0x3dbffc8e33fffd8c

def z260 : W := mkw 0x867ffddf7ddf794a 0x433ffeefbeefbca5 0xffffffffffffffff 0xffffffffffffffff

def z261 : W := mkw 0x0200080005db7800 0x0100040002edbc00 0x7b24f80007fff801 0x3d927c0003fffc00

def z262 : W := mkw 0x416007008702c631 0xa0b0038043816318 0x996007000703e739 0x4cb003800381f39c

def z263 : W := mkw 0xe009584db84db96e 0x7004ac26dc26dcb7 0xf727f91ff91fffff 0xfb93fc8ffc8fffff

def z264 : W := mkw 0x007fe50240000000 0x003ff28120000000 0xf47fff03e0000000 0x7a3fff81f0000000

def z265 : W := mkw 0x82f6ad94059e6b40 0xc17b56ca02cf35a0 0x0024b91c011c6300 0x00125c8e008e3180

def z266 : W := mkw 0x4009424192008421 0x2004a120c9004210 0xfddb46e39e038421 0xfeeda371cf01c210

def z267 : W := mkw 0xa009586d386d39ce 0x5004ac369c369ce7 0x229c78fc18fc18c6 0x914e3c7e0c7e0c63

def z268 : W := mkw 0x0074159828000000 0x003a0acc14000000 0xf4fcfffc78000000 0xfa7e7ffe3c000000

def z269 : W := mkw 0x040010d938000000 0x0200086c9c000000 0x008000fc18000000 0x8040007e0c000000

def z270 : W := mkw 0x0000100828000000 0x0000080414000000 0xf424f91c78000000 0xfa127c8e3c000000

def z271 : W := mkw 0x0000100828000000 0x0000080414000000 0x4400f80078000000 0x22007c003c000000

def z272 : W := mkw 0x60095849b849b82e 0x3004ac24dc24dc17 0x4503f803f803f83e 0x2281fc01fc01fc1f

def z273 : W := mkw 0x627fea2087fbfca5 0x313ff51043fdfe52 0x7b7ff80007fffce7 0x3dbffc0003fffe73

def z274 : W := mkw 0x0076a00000000000 0x003b500000000000 0x0024b80000000000 0x00125c0000000000

def z275 : W := mkw 0x80000804000c294a 0x40000402000614a5 0xb324011c011c7fff 0xd992008e008e3fff

def z276 : W := mkw 0x0009400000000000 0x0004a00000000000 0x705b400000000000 0x382da00000000000

def z277 : W := mkw 0x0409704938000000 0x0204b8249c000000 0x0000780018000000 0x00003c000c000000

def z278 : W := mkw 0x0209680000493800 0x0104b40000249c00 0x0000780000001800 0x00003c0000000c00

def z279 : W := mkw 0x60000261922084a5 0x30000130c9104252 0xbed806e39ee004e7 0xdf6c0371cf700273

def z280 : W := mkw 0x027fe80000d93800 0x013ff400006c9c00 0x727ff80000fc1800 0x393ffc00007e0c00

def z281 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x08fc07fc07fc0300 0x047e03fe03fe0180

def z282 : W := mkw 0x0009504938000000 0x0004a8249c000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z283 : W := mkw 0x000018082808280a 0x00000c0414041405 0xf700f80078007cff 0xfb807c003c003e7f

def z284 : W := mkw 0x041d75db78000000 0x020ebaedbc000000 0xa49c7ffff8000000 0xd24e3ffffc000000

def z285 : W := mkw 0x410002008702c631 0xa080010043816318 0x0800000006038000 0x040000000301c000

def z286 : W := mkw 0x8476bd9e680c294a 0x423b5ecf340614a5 0x0024b91c611c6318 0x00125c8e308e318c

def z287 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xb224791c191c1fc7 0xd9123c8e0c8e0fe3

def z288 : W := mkw 0x8000000400040140 0x40000002000200a0 0x0024011c011c0300 0x0012008e008e0180

def z289 : W := mkw 0x0000080000082800 0x0000040000041400 0x22047800001c1800 0x11023c00000e0c00

def z290 : W := mkw 0x82800a2407ff7fc1 0xc140051203ffbfe0 0x0b00000007ffffc1 0x0580000003ffffe0

def z291 : W := mkw 0x4000000080008020 0x2000000040004010 0x4503000380038020 0x22818001c001c010

def z292 : W := mkw 0x60000220826194a5 0x300001104130ca52 0xbbd806e006e39ce7 0xddec03700371ce73

def z293 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfffbc7e3ffe3ffff 0xfffde3f1fff1ffff

def z294 : W := mkw 0x616bc763d763d6b5 0xb0b5e3b1ebb1eb5a 0xddfb87e3e7e3e739 0x6efdc3f1f3f1f39c

def z295 : W := mkw 0x41000702c702c631 0xa080038163816318 0x8d000703e703e739 0x46800381f381f39c

def z296 : W := mkw 0x41628f02c70aee31 0xa0b1478163857718 0xff67ff03e71fff39 0x7fb3ff81f38fff9c

def z297 : W := mkw 0x067ffddb784b7800 0x033ffeedbc25bc00 0xf5fffffff803f800 0xfafffffffc01fc00

def z298 : W := mkw 0x0074059000000000 0x003a02c800000000 0x00d806e000000000 0x006c037000000000

def z299 : W := mkw 0x80f405b405b403c0 0xc07a02da02da01e0 0x22bc01fc01fc03c0 0x915e00fe00fe01e0

def z300 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x0324b91c611c7fff 0x01925c8e308e3fff

def z301 : W := mkw 0x026be800054b7800 0x0135f40002a5bc00 0x5963f8000703f801 0x2cb1fc000381fc00

def z302 : W := mkw 0x0074070007900601 0x803a038003c80300 0xba7c070007fc0701 0x5d3e038003fe0380

def z303 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x2a5f780006ff9800 0x152fbc00037fcc00

def z304 : W := mkw 0x2009406110611084 0x1004a03088308842 0xf79840e018e01ce7 0xfbcc20700c700e73

def z305 : W := mkw 0x0060070007000601 0x8030038003800300 0x0840060006000000 0x0420030003000000

def z306 : W := mkw 0x60fd47f197f196a5 0xb07ea3f8cbf8cb52 0x08db06e386e38000 0x046d8371c371c000

def z307 : W := mkw 0x41028202c202c431 0x2081410161016218 0xdd438603e603e439 0x6ea1c301f301f21c

def z308 : W := mkw 0x41629f0aef0aee3b 0xa0b14f857785771d 0xdd63ff03ff03ff3f 0x6eb1ff81ff81ff9f

def z309 : W := mkw 0x82f6afb407be6fc1 0xc17b57da03df37e0 0xbafcbffc07fc67c1 0xdd7e5ffe03fe33e0

def z310 : W := mkw 0x0062800005024000 0x0031400002812000 0xdd6381006703e739 0x6eb1c0803381f39c

def z311 : W := mkw 0x047ff04b78000000 0x023ff825bc000000 0x747ff803f8000000 0x3a3ffc01fc000000

def z312 : W := mkw 0x007fe00000411000 0x003ff00000208800 0x7b7ff80006e39801 0x3dbffc000371cc00

def z313 : W := mkw 0x0009426112200481 0x0004a13089100240 0xfedb46e39ee004c1 0xff6da371cf700260

def z314 : W := mkw 0xc37fff0eefdfff7b 0xe1bfff8777efffbd 0xff7fff1fffffffff 0xffbfff8fffffffff

def z315 : W := mkw 0x41000702c2008631 0xa080038161004318 0xdd430703e6038739 0x6ea18381f301c39c

def z316 : W := mkw 0x0009404110000000 0x0004a02088000000 0x00db06e380000000 0x006d8371c0000000

def z317 : W := mkw 0xc1628f06c70eef7b 0xe0b14783638777bd 0xdf638703e71fffff 0x6fb1c381f38fffff

def z318 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x0004381c001c0000 0x00021c0e000e0000

def z319 : W := mkw 0xa009586d386d39ce 0x5004ac369c369ce7 0xf7bcf9fc79fc7fff 0xfbde7cfe3cfe3fff

def z320 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xff63c703ff03ffff 0xffb1e381ff81ffff

def z321 : W := mkw 0x040bf5db78000000 0x0205faedbc000000 0xc483fffff8000000 0xe241fffffc000000

def z322 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xbaff07ff87ff87c1 0xdd7f83ffc3ffc3e0

def z323 : W := mkw 0x4000020082008421 0x2000010041004210 0xdd638703e703e739 0x6eb1c381f381f39c

def z324 : W := mkw 0x437fe702c7d3d631 0xa1bff38163e9eb18 0xdd7b8703e7e3e739 0x6ebdc381f3f1f39c

def z325 : W := mkw 0x0062870247000601 0x8031438123800300 0xdc638703e7000701 0x6e31c381f3800380

def z326 : W := mkw 0xe080022487f597e5 0xf040011243facbf2 0x0b00000007ff9fe7 0x0580000003ffcff3

def z327 : W := mkw 0x060bf84b784b7800 0x0305fc25bc25bc00 0x4503f803f803f800 0x2281fc01fc01fc00

def z328 : W := mkw 0xe009526dba6595ef 0x7004a936dd32caf7 0xffdb47fffee39fff 0xffeda3ffff71cfff

def z329 : W := mkw 0x41768792c702c631 0xa0bb43c963816318 0xfdff87ffe703e739 0xfeffc3fff381f39c

def z330 : W := mkw 0x8060070407040741 0xc0300382038203a0 0xba64071c071c07c1 0xdd32038e038e03e0

def z331 : W := mkw 0x647fe7f3d26194a5 0x323ff3f9e930ca52 0x08db06e386e38000 0x046d8371c371c000

def z332 : W := mkw 0x616bc743d743d635 0xb0b5e3a1eba1eb1a 0xdd63c703ff03ff3f 0x6eb1e381ff81ff9f

def z333 : W := mkw 0x80e0072407b407c1 0xc070039203da03e0 0x9a60070007fc07c1 0x4d30038003fe03e0

def z334 : W := mkw 0x0000100828000000 0x0000080414000000 0xf724f91c78001ce7 0xfb927c8e3c000e73

def z335 : W := mkw 0x006bc00005435000 0x0035e00002a1a800 0x7b7bc00007e3f801 0x3dbde00003f1fc00

def z336 : W := mkw 0xe0001a6dba2cadef 0x70000d36dd1656f7 0xf7a4fffff91c7fff 0xfbd27ffffc8e3fff

def z337 : W := mkw 0x037fed0245db7a10 0x81bff68122edbd08 0x7b7ff90067fffb19 0x3dbffc8033fffd8c

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z339 : W := mkw 0x447ff7dbfa008421 0x223ffbedfd004210 0xfdfffffffe038421 0xfeffffffff01c210

def z340 : W := mkw 0x62094a6197fbfca5 0x3104a530cbfdfe52 0xffdb46e39ffffce7 0xffeda371cffffe73

def z341 : W := mkw 0x6009404190419024 0x3004a020c820c812 0x0003000380038000 0x00018001c001c000

def z342 : W := mkw 0x457fe7d3d702c631 0xa2bff3e9eb816318 0xddfb87e3e703e739 0x6efdc3f1f381f39c

def z343 : W := mkw 0x80f400b405b401c0 0x407a005a02da00e0 0x3afc00fc07fc00c1 0x9d7e007e03fe0060

def z344 : W := mkw 0x808007b4022407c1 0xc04003da011203e0 0xbad807fc06e007c1 0xdd6c03fe037003e0

def z345 : W := mkw 0x0060072007200681 0x8030039003900340 0xbaf807e007e007c1 0xdd7c03f003f003e0

def z346 : W := mkw 0xe27ffa6dbffffdef 0x713ffd36dffffef7 0xffffffffffffffff 0xffffffffffffffff

def z347 : W := mkw 0x00f407b007b00681 0x807a03d803d80340 0x3afc06e007fc0001 0x1d7e037003fe0000

def z348 : W := mkw 0x627fe26197f3d4a5 0x313ff130cbf9ea52 0x08db06e386e38000 0x046d8371c371c000

def z349 : W := mkw 0x0000050240000000 0x0000028120000000 0x84000703e0000000 0x42000381f0000000

def z350 : W := mkw 0x8000000400040140 0x40000002000200a0 0x8000011c000007c0 0xc000008e000003e0

def z351 : W := mkw 0xe1ffc7f7d7f7d7f5 0xf0ffe3fbebfbebfa 0xffffc7ffffffffff 0xffffe3ffffffffff

def z352 : W := mkw 0x80001a2c2a2c2dcb 0x40000d16151616e5 0xfffcfffc7ffc7fff 0xfffe7ffe3ffe3fff

def z353 : W := mkw 0x0274080005db7800 0x013a040002edbc00 0x3b7c000007fff801 0x1dbe000003fffc00

def z354 : W := mkw 0x41628502c002c030 0x20b1428160016018 0xd5638703e003e038 0x6ab1c381f001f01c

def z355 : W := mkw 0x809418bc28bc29ca 0x404a0c5e145e14e5 0x229c78fc18fc18c6 0x914e3c7e0c7e0c63

def z356 : W := mkw 0x040bf04b78000000 0x0205f825bc000000 0xf427f91ff8000000 0xfa13fc8ffc000000

def z357 : W := mkw 0x6009404190419024 0x3004a020c820c812 0xf703400398039ce7 0xfb81a001cc01ce73

def z358 : W := mkw 0x84fd77fd3fb407c1 0xc27ebbfe9fda03e0 0xbafc7ffc1ffc07c1 0xdd7e3ffe0ffe03e0

def z359 : W := mkw 0x827fe80405df7940 0x413ff40202efbca0 0xfb7ff91c07ffffc1 0xfdbffc8e03ffffe0

def z360 : W := mkw 0x0009422002611481 0x0004a11001308a40 0xfbdb46e006e39cc1 0xfdeda3700371ce60

def z361 : W := mkw 0x657ff7fbff63d6b5 0xb2bffbfdffb1eb5a 0xffffffffffe3ffff 0xfffffffffff1ffff

def z362 : W := mkw 0x0476a59240000000 0x023b52c920000000 0x0000000000000000 0x0000000000000000

def z363 : W := mkw 0x40628702c2008421 0x2031438161004210 0xdd638703e6038421 0x6eb1c381f301c210

def z364 : W := mkw 0x41f687b2c7b2c6b1 0xa0fb43d963d96358 0xddfb87e3e7e3e739 0x6efdc3f1f3f1f39c

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x5943000006038001 0x2ca180000301c000

def z366 : W := mkw 0x040955db78000000 0x0204aaedbc000000 0xf4db47fff8000000 0xfa6da3fffc000000

def z367 : W := mkw 0x027fef0007db7e01 0x813ff78003edbf00 0xfb7fff0007ffff01 0x7dbfff8003ffff80

def z368 : W := mkw 0x0200080000d93800 0x01000400006c9c00 0x0200000000fc1800 0x01000000007e0c00

def z369 : W := mkw 0x0009404110000000 0x0004a02088000000 0x4403400398000000 0x2201a001cc000000

def z370 : W := mkw 0xc0001a0caa0cad6b 0x60000d06550656b5 0xff67ff1fff1fffff 0xffb3ff8fff8fffff

def z371 : W := mkw 0x616bc763d763d6b5 0xb0b5e3b1ebb1eb5a 0x08db06e386e38000 0x046d8371c371c000

def z372 : W := mkw 0x047ff7db7f000601 0x823ffbedbf800300 0xfcffffffff000701 0xfe7fffffff800380

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x32240000011c0001 0x19120000008e0000

def z374 : W := mkw 0x848017ff7a2407c1 0xc2400bffbd1203e0 0x848007fff80007c0 0xc24003fffc0003e0

def z375 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf7fffffff8001ce7 0xfbfffffffc000e73

def z376 : W := mkw 0x040bf04b78000000 0x0205f825bc000000 0xf4dbfee3f8000000 0xfa6dff71fc000000

def z377 : W := mkw 0x221d686110f93884 0x110eb430887c9c42 0x229c78e018fc18c6 0x914e3c700c7e0c63

def z378 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xf424f91c791c6318 0xfa127c8e3c8e318c

def z379 : W := mkw 0x040015db78000000 0x02000aedbc000000 0xf4a4fffff8000000 0xfa527ffffc000000

def z380 : W := mkw 0x80f687b647b407c1 0xc07b43db23da03e0 0xfeff87ffe7fc07c1 0xff7fc3fff3fe03e0

def z381 : W := mkw 0x647ff7fbfa6194a5 0x323ffbfdfd30ca52 0xfcfffffffee38000 0xfe7fffffff71c000

def z382 : W := mkw 0xc57fffdfff0eef7b 0xe2bfffefff8777bd 0xffffffffff1fffff 0xffffffffff8fffff

def z383 : W := mkw 0x0002800000024000 0x0001400000012000 0x410380000003e000 0x2081c0000001f000

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0x84000000180004e6 0xc20000000c000273

def z385 : W := mkw 0x607d426197f194a5 0x303ea130cbf8ca52 0xffff46e39fff9ce7 0xffffa371cfffce73

def z386 : W := mkw 0x0476b59a68000000 0x023b5acd34000000 0xf424f91c78000000 0xfa127c8e3c000000

def z387 : W := mkw 0x027fe00005d35000 0x013ff00002e9a800 0x3a7f000007ff8001 0x1d3f800003ffc000

def z388 : W := mkw 0x020bf808284b780a 0x0105fc041425bc05 0x4503f8007803f83e 0x2281fc003c01fc1f

def z389 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0xb624011c791c07ff 0xdb12008e3c8e03ff

def z390 : W := mkw 0x61628722c763d6b5 0xb0b1439163b1eb5a 0xdf638703e7e3ffff 0x6fb1c381f3f1ffff

def z391 : W := mkw 0x84ffffff7fbc2fcb 0xc27fffffbfde17e5 0xfffffffffffc7fff 0xfffffffffffe3fff

def z392 : W := mkw 0xc1629f0eef0eef7b 0xe0b14f87778777bd 0xdd67bf1fe71fe739 0x6eb3df8ff38ff39c

def z393 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0x0000011c60000318 0x0000008e3000018c

def z394 : W := mkw 0x84fff7ff7a2407c1 0xc27ffbffbd1203e0 0xf4fffffff80007c0 0xfa7ffffffc0003e0

def z395 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x4ddb46e39ee39826 0x26eda371cf71cc13

def z396 : W := mkw 0x007fe59000000000 0x003ff2c800000000 0xf0fffffc00000000 0xf87ffffe00000000

def z397 : W := mkw 0x227fe86115fb7884 0x113ff4308afdbc42 0x7bfff8e01ffff8c7 0xbdfffc700ffffc63

def z398 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfffc47fc1ffc1fe7 0xfffe23fe0ffe0ff3

def z399 : W := mkw 0xc1e287b6c726c7f1 0xe0f143db639363f8 0xdde387ffe703e7f9 0xeef1c3fff381f3fc

def z400 : W := mkw 0x0060050000000000 0x0030028000000000 0x9060070000000000 0x4830038000000000

def z401 : W := mkw 0x80000804000c294a 0x40000402000614a5 0xf7004000191c7fff 0xfb8020000c8e3fff

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0x22004000180018c6 0x910020000c000c63

def z403 : W := mkw 0x0000000000411000 0x0000000000208800 0x0b00000006e39801 0x058000000371cc00

def z404 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x7324f81c191c78c7 0xb9927c0e0c8e3c63

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x4500800060006038 0x228040003000301c

def z406 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x2adc06fc06fc00c0 0x956e037e037e0060

def z407 : W := mkw 0x0402b00a68000000 0x0201580534000000 0x0000b80060000000 0x00005c0030000000

def z408 : W := mkw 0x847ff5df78040140 0x423ffaefbc0200a0 0xf6fffffff91c07c1 0xfb7ffffffc8e03e0

def z409 : W := mkw 0x406282008702c421 0x2031410043816210 0xdd6386038703e421 0x6eb1c301c381f210

def z410 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x2b9840e01ee39ce7 0x95cc20700f71ce73

def z411 : W := mkw 0x640017fbfa2084a5 0x32000bfdfd104252 0x848007fff80004e6 0xc24003fffc000273

def z412 : W := mkw 0x2009406110611084 0x1004a03088308842 0x009800e000e00000 0x004c007000700000

def z413 : W := mkw 0x800000040004014a 0x40000002000200a5 0x00000000000007fe 0x00000000000003ff

def z414 : W := mkw 0x437fe702c7d3d631 0xa1bff38163e9eb18 0x085b060386e38000 0x042d8301c371c000

def z415 : W := mkw 0x84ffe7f757b407c1 0xc27ff3fbabda03e0 0xbaff07ff87fc07c1 0xdd7f83ffc3fe03e0

def z416 : W := mkw 0x640bf26bfa6194a5 0x3205f935fd30ca52 0xffdbfee3fee39ce7 0xffedff71ff71ce73

def z417 : W := mkw 0x457ff5dbf802c030 0x22bffaedfc016018 0xf5fffffff803e038 0xfafffffffc01f01c

def z418 : W := mkw 0x41028002c002c030 0x2081400160016018 0xd5238103e103e739 0x6a91c081f081f39c

def z419 : W := mkw 0x41000702c2008631 0xa080038161004318 0x0000060380000000 0x00000301c0000000

def z420 : W := mkw 0x81629d0e6d0e6b5a 0xc0b14e87368735ad 0x0024b91c611c6318 0x00125c8e308e318c

def z421 : W := mkw 0x047ff59a68000000 0x023ffacd34000000 0x707ff91c60000000 0x383ffc8e30000000

def z422 : W := mkw 0x4060070087008621 0xa030038043804310 0xdd63070387038721 0x6eb18381c381c390

def z423 : W := mkw 0x0009400000411000 0x0004a00000208800 0xff5b40001ee39ce7 0xffada0000f71ce73

def z424 : W := mkw 0xc18007b6c22487f1 0xe0c003db611243f8 0x848007ffe00007f8 0xc24003fff00003fc

def z425 : W := mkw 0x647ff7fbfa2084a5 0x323ffbfdfd104252 0xf4fffffff80004e6 0xfa7ffffffc000273

def z426 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x4700f800791c7fff 0x23807c003c8e3fff

def z427 : W := mkw 0x0676bd9a6d9a6800 0x033b5ecd36cd3400 0x0024b91c611c6000 0x00125c8e308e3000

def z428 : W := mkw 0x84001ddf780c294a 0x42000eefbc0614a5 0xf7a4fffff91c7fff 0xfbd27ffffc8e3fff

def z429 : W := mkw 0x0000000005900000 0x0000000002c80000 0x0a00000007fc0001 0x0500000003fe0000

def z430 : W := mkw 0x4009420082419421 0x2004a1004120ca10 0xff5b460386e39c21 0x7fada301c371ce10

def z431 : W := mkw 0x457fe7d3d702c631 0xa2bff3e9eb816318 0x08db06e386038000 0x046d8371c301c000

def z432 : W := mkw 0x86ffffff7fff7fc1 0xc37fffffbfffbfe0 0xffffffffffffffc1 0xffffffffffffffe0

def z433 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x80a407fc011c07c0 0xc05203fe008e03e0

def z434 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x84db07fff8000000 0xc26d83fffc000000

def z435 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x2224f91c791c7bde 0x91127c8e3c8e3def

def z436 : W := mkw 0x0000022002200481 0x0000011001100240 0xffd846e01ee01ce7 0xffec23700f700e73

def z437 : W := mkw 0x4100020082008631 0xa080010041004318 0x0000000000000738 0x000000000000039c

def z438 : W := mkw 0x041d70d938000000 0x020eb86c9c000000 0xf4bcf9fc78000000 0xfa5e7cfe3c000000

def z439 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x4d438603e603e038 0x26a1c301f301f01c

def z440 : W := mkw 0x4162970aef02c631 0xa0b14b8577816318 0xfd67ff1fff03e739 0xfeb3ff8fff81f39c

def z441 : W := mkw 0x610bc043d043d034 0x3085e021e821e81a 0x4503c003f803f83e 0x2281e001fc01fc1f

def z442 : W := mkw 0x0276a800059a6800 0x013b540002cd3400 0x5967b800071fe001 0x2cb3dc00038ff000

def z443 : W := mkw 0x247ff5fb78611084 0x123ffafdbc308842 0xf6fffffff8e018c6 0xfb7ffffffc700c63

def z444 : W := mkw 0x8074059400040140 0x403a02ca000200a0 0xb2fc07fc011c07c1 0xd97e03fe008e03e0

def z445 : W := mkw 0x60094061906190a4 0x3004a030c830c852 0x679b40e398e398e6 0xb3cda071cc71cc73

def z446 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x7bdb46e386e39801 0x3deda371c371cc00

def z447 : W := mkw 0x436bef02c74bfe31 0xa1b5f78163a5ff18 0xdd63ff03e703ff39 0x6eb1ff81f381ff9c

def z448 : W := mkw 0x41f687b2c7b2c6b1 0xa0fb43d963d96358 0x08db06e386e38000 0x046d8371c371c000

def z449 : W := mkw 0x0060000005000000 0x0030000002800000 0x1860000007000001 0x0c30000003800000

def z450 : W := mkw 0x8009584d380c294a 0x4004ac269c0614a5 0xf7fffffff91c7fff 0xfbfffffffc8e3fff

def z451 : W := mkw 0x610002208763d6b5 0xb080011043b1eb5a 0x0b00000007e3ffff 0x0580000003f1ffff

def z452 : W := mkw 0x416282008702c631 0xa0b1410043816318 0x596380000703e739 0x2cb1c0000381f39c

def z453 : W := mkw 0x456bf74bff02c631 0xa2b5fba5ff816318 0xdd63ff03ff03e739 0x6eb1ff81ff81f39c

def z454 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0xf424f91c780007fe 0xfa127c8e3c0003ff

def z455 : W := mkw 0x047ff0d938000000 0x023ff86c9c000000 0x70fff8fc18000000 0xb87ffc7e0c000000

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x8400010060000738 0x420000803000039c

def z457 : W := mkw 0x80000804000c294a 0x40000402000614a5 0xd7208100611c7fff 0x6b904080308e3fff

def z458 : W := mkw 0x80f41fbc2fbc2fcb 0xc07a0fde17de17e5 0xbafc7ffc1ffc1fc7 0xdd7e3ffe0ffe0fe3

def z459 : W := mkw 0x047ffddb7808280a 0x023ffeedbc041405 0xf5fffffff800783e 0xfafffffffc003c1f

def z460 : W := mkw 0x80ffe7b407b407c1 0xc07ff3da03da03e0 0xfafffffc07fc07c1 0xfd7ffffe03fe03e0

def z461 : W := mkw 0xe4fff7fffff597e5 0xf27ffbfffffacbf2 0xffffffffffff9fe7 0xffffffffffffcff3

def z462 : W := mkw 0xc180022487b6c7f1 0xe0c0011243db63f8 0x0b00000007ffe7f9 0x0580000003fff3fc

def z463 : W := mkw 0x60000261922084a5 0x30000130c9104252 0x008006e380000000 0x00400371c0000000

def z464 : W := mkw 0x80f40fb407bc2fcb 0xc07a07da03de17e5 0xbbfc07fc07fc7fff 0xddfe03fe03fe3fff

def z465 : W := mkw 0x04ffe7f357b00681 0x827ff3f9abd80340 0x08db06e386e00000 0x046d8371c3700000

def z466 : W := mkw 0x60094a619269bca5 0x3004a530c934de52 0xfffffee39ffffce7 0xffffff71cffffe73

def z467 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x9863070387038701 0x4c318381c381c380

def z468 : W := mkw 0x0062800005024000 0x0031400002812000 0x0020800001006000 0x0010400000803000

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x0020810061006318 0x001040803080318c

def z470 : W := mkw 0x4000020082008421 0x2000010041004210 0xff4346039e039ce7 0xffa1a301cf01ce73

def z471 : W := mkw 0x0062850240000000 0x0031428120000000 0xd5638703e1006739 0x6ab1c381f080339c

def z472 : W := mkw 0x4102980ae80ae83a 0x20814c057405741d 0x4503f803f803f83e 0x2281fc01fc01fc1f

def z473 : W := mkw 0x021fe80000db7800 0x010ff400006dbc00 0x631ff80000fff800 0x318ffc00007ffc00

def z474 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xa69846e398e01ce6 0xd34c2371cc700e73

def z475 : W := mkw 0xc1001f0eea0caf7b 0xe0800f87750657bd 0xf724ff1ff91c7fff 0xfb927f8ffc8e3fff

def z476 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x8c430703e6038738 0x46218381f301c39c

def z477 : W := mkw 0xc3ffefb6c7fffff1 0xe1fff7db63fffff8 0xffffffffe7fffff9 0xfffffffff3fffffc

def z478 : W := mkw 0x41000702c2008631 0xa080038161004318 0xd5208703e1006739 0x6a904381f080339c

def z479 : W := mkw 0x809402b407b407c1 0xc04a015a03da03e0 0x2a9c00fc07fc07c1 0x954e007e03fe03e0

def z480 : W := mkw 0x82ffed9405df7b40 0xc17ff6ca02efbda0 0x7b7ff91c07fffb01 0x3dbffc8e03fffd80

def z481 : W := mkw 0x0000059000000000 0x000002c800000000 0x808007fc00000000 0xc04003fe00000000

def z482 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x8424b91c791c67fe 0xc2125c8e3c8e33ff

def z483 : W := mkw 0x0000080000082800 0x0000040000041400 0xf724f800191c7ce7 0xfb927c000c8e3e73

def z484 : W := mkw 0x81f6859645964350 0xc0fb42cb22cb21a8 0x0024811c611c6318 0x0012408e308e318c

def z485 : W := mkw 0x0009400000411000 0x0004a00000208800 0x2218400000e01800 0x110c200000700c00

def z486 : W := mkw 0x621d6a6192f9bca5 0x310eb530c97cde52 0xffdf7ee39eff9ce7 0xffefbf71cf7fce73

def z487 : W := mkw 0x60000261922084a5 0x30000130c9104252 0xf78046e398001ce7 0xfbc02371cc000e73

def z488 : W := mkw 0x007407b002200481 0x003a03d801100240 0xbafc07fc06e004c1 0xdd7e03fe03700260

def z489 : W := mkw 0x840bf84f780c294a 0x4205fc27bc0614a5 0xf727f91ff91c7fff 0xfb93fc8ffc8e3fff

def z490 : W := mkw 0x82ffea2407ff7fc1 0xc17ff51203ffbfe0 0x7b7ff80007ffffc1 0x3dbffc0003ffffe0

def z491 : W := mkw 0xc0f407b487b487e1 0xe07a03da43da43f0 0xffff07ff87ff87e1 0xffff83ffc3ffc3f0

def z492 : W := mkw 0x41000002c0008030 0x2080000160004018 0x04000003e0000038 0x02000001f000001c

def z493 : W := mkw 0x00f407b007b00681 0x807a03d803d80340 0xbad806e006e004c1 0xdd6c037003700260

def z494 : W := mkw 0x00f407b007b00681 0x807a03d803d80340 0xb8fc07fc06e00000 0xdc7e03fe03700000

def z495 : W := mkw 0x061d78d938d93800 0x030ebc6c9c6c9c00 0x229c78fc18fc1800 0x914e3c7e0c7e0c00

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x4500400018001826 0x228020000c000c13

def z497 : W := mkw 0x8074000405940140 0x403a000202ca00a0 0xba7c011c07fc07c1 0xdd3e008e03fe03e0

def z498 : W := mkw 0x047fe5d350000000 0x023ff2e9a8000000 0xd4fb87e3e0000000 0x6a7dc3f1f0000000

def z499 : W := mkw 0x0000022002200481 0x0000011001100240 0x808006e0000004c0 0xc040037000000260

def z500 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x8cdb06e39ee384e6 0xc66d8371cf71c273

def z501 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdc638703e6038000 0x6e31c381f301c000

def z502 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x4427f91ff8000000 0x2213fc8ffc000000

def z503 : W := mkw 0x41628002c502c030 0x20b1400162816018 0x5d638003e703e039 0x2eb1c001f381f01c

def z504 : W := mkw 0x0009404110000000 0x0004a02088000000 0xf7db46e398001ce7 0xfbeda371cc000e73

def z505 : W := mkw 0x047fe5d350000000 0x023ff2e9a8000000 0xf4db46e398000000 0xfa6da371cc000000

def z506 : W := mkw 0xe08007f5922487e5 0xf04003fac91243f2 0x848007ff980007e6 0xc24003ffcc0003f3

def z507 : W := mkw 0x0276a800059a6800 0x013b540002cd3400 0x3a7cb80007fc6001 0x1d3e5c0003fe3000

def z508 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xb224b91c611c67d9 0xd9125c8e308e33ec

def z509 : W := mkw 0x0062850240000000 0x0031428120000000 0x0020810060000000 0x0010408030000000

def z510 : W := mkw 0x040be04350000000 0x0205f021a8000000 0x0003000380000000 0x00018001c0000000

def z511 : W := mkw 0x82f40fb407ff7fc1 0xc17a07da03ffbfe0 0xbbfc07fc07ffffc1 0xddfe03fe03ffffe0

def z512 : W := mkw 0x0376ad02459a6a10 0x81bb568122cd3508 0x0024b900611c6318 0x00125c80308e318c

def z513 : W := mkw 0x60000261922084a5 0x30000130c9104252 0xddc306e39e0384e7 0xeee18371cf01c273

def z514 : W := mkw 0x041d70d938000000 0x020eb86c9c000000 0xf4df7eff98000000 0xfa6fbf7fcc000000

def z515 : W := mkw 0x827ff80c2ddf794a 0x413ffc0616efbca5 0x7b7ff81c1ffff8c7 0xbdbffc0e0ffffc63

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0xb2000000000004c1 0xd900000000000260

def z517 : W := mkw 0x430be802c04bf830 0x2185f4016025fc18 0x4503f803e003f838 0x2281fc01f001fc1c

def z518 : W := mkw 0x067ff8d93ddb7800 0x033ffc6c9eedbc00 0x7bfff8fc1ffff801 0xbdfffc7e0ffffc00

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0xb024011c00000000 0xd812008e00000000

def z520 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0xd520811c790067ff 0xea90408e3c8033ff

def z521 : W := mkw 0x41028002c002c030 0x2081400160016018 0x0003000380038000 0x00018001c001c000

def z522 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x44dbfee3f8000000 0x226dff71fc000000

def z523 : W := mkw 0x450bf04bf802c030 0x2285f825fc016018 0x4503f803f803e038 0x2281fc01fc01f01c

def z524 : W := mkw 0x8080000405940340 0xc040000202ca01a0 0x00000000011c0300 0x00000000008e0180

def z525 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xdddb06e386e38421 0x6eed8371c371c210

def z526 : W := mkw 0x809407b402b407c1 0xc04a03da015a03e0 0xa29c07fc00fc07c0 0xd14e03fe007e03e0

def z527 : W := mkw 0x0102800240024010 0x0081400120012008 0x0000800060006018 0x000040003000300c

def z528 : W := mkw 0x81629d0e6d0e6b5a 0xc0b14e87368735ad 0xf724f91c791c7fff 0xfb927c8e3c8e3fff

def z529 : W := mkw 0x027fe800059a6800 0x013ff40002cd3400 0x707ff800011c6000 0x383ffc00008e3000

def z530 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xc58346e398039ce6 0xe2c1a371cc01ce73

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0xd443060380000000 0x6a218301c0000000

def z532 : W := mkw 0x821d780c28dd394a 0x410ebc06146e9ca5 0x221c781c18fc18c6 0x910e3c0e0c7e0c63

def z533 : W := mkw 0x8000000400040140 0x40000002000200a0 0xf724411c191c1fe7 0xfb92208e0c8e0ff3

def z534 : W := mkw 0xc1628706c706c771 0xe0b14383638363b8 0xff67871fe71fe7f9 0xffb3c38ff38ff3fc

def z535 : W := mkw 0x80f41d9c2d9c2b4a 0xc07a0ece16ce15a5 0x0024b91c611c6318 0x00125c8e308e318c

def z536 : W := mkw 0x0000070002000601 0x8000038001000300 0x8000070000000700 0x4000038000000380

def z537 : W := mkw 0x808017bc2a2407cb 0xc0400bde151203e5 0x848007fc780007fe 0xc24003fe3c0003ff

def z538 : W := mkw 0x0000080000082800 0x0000040000041400 0x4100f80000007800 0x20807c0000003c00

def z539 : W := mkw 0xe0f407b487f597e5 0xf07a03da43facbf2 0xbbfc07fc07ff9fe7 0xddfe03fe03ffcff3

def z540 : W := mkw 0x809418bc28bc29ca 0x404a0c5e145e14e5 0xf7bcf9fc79fc7fff 0xfbde7cfe3cfe3fff

def z541 : W := mkw 0x067ffddb7d9a6800 0x033ffeedbecd3400 0xf4fffffff91c6000 0xfa7ffffffc8e3000

def z542 : W := mkw 0xc1f69fbeefbeeffb 0xe0fb4fdf77df77fd 0xffffffffffffffff 0xffffffffffffffff

def z543 : W := mkw 0x43000a0087dbfe31 0xa180050043edff18 0x0b00000007ffff39 0x0580000003ffff9c

def z544 : W := mkw 0x807ff80c280c294a 0x403ffc06140614a5 0xf77ff91c791c7fff 0xfbbffc8e3c8e3fff

def z545 : W := mkw 0x416bc702c743d631 0xa0b5e38163a1eb18 0xff7bc703e7e3ff39 0x7fbde381f3f1ff9c

def z546 : W := mkw 0xc1e28726c7b6c7f1 0xe0f1439363db63f8 0xdf638703e7ffe7f9 0x6fb1c381f3fff3fc

def z547 : W := mkw 0x047d75d938000000 0x023ebaec9c000000 0xb0fc7ffc18000000 0xd87e3ffe0c000000

def z548 : W := mkw 0x60094261922084a5 0x3004a130c9104252 0xf4db46e3980004e6 0xfa6da371cc000273

def z549 : W := mkw 0x620be841904bf824 0x3105f420c825fc12 0x4503f8039803f826 0x2281fc01cc01fc13

def z550 : W := mkw 0x60fd47f197f196a5 0xb07ea3f8cbf8cb52 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z551 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x495bf80006e3f800 0x24adfc000371fc00

def z552 : W := mkw 0x640957fbfa6194a5 0x3204abfdfd30ca52 0xffdb47fffee39ce7 0xffeda3ffff71ce73

def z553 : W := mkw 0x0000080000082800 0x0000040000041400 0xf724f900611c7f39 0x7b927c80308e3f9c

def z554 : W := mkw 0x0062870007024601 0x8031438003812300 0xd96387000703e701 0x6cb1c3800381f380

def z555 : W := mkw 0x80801fbc2a2c2fcb 0xc0400fde151617e5 0xf7a4fffc791c7fff 0xfbd27ffe3c8e3fff

def z556 : W := mkw 0x007fe00005024000 0x003ff00002812000 0x797ff8000703e001 0x3cbffc000381f000

def z557 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x223cf80001fc7800 0x111e7c0000fe3c00

def z558 : W := mkw 0x627fe84195dbf824 0x313ff420caedfc12 0x7f7ff8039ffff827 0x3fbffc01cffffc13

def z559 : W := mkw 0x047415db78000000 0x023a0aedbc000000 0xb4fc07fff8000000 0xda7e03fffc000000

def z560 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xf704781c181c1ce7 0xfb823c0e0c0e0e73

def z561 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xbadb06e386e384c1 0xdd6d8371c371c260

def z562 : W := mkw 0xe2ffeff597ffffe5 0xf17ff7facbfffff2 0xffffffff9fffffe7 0xffffffffcffffff3

def z563 : W := mkw 0x80f407b4022407c1 0xc07a03da011203e0 0xb0fc07fc000007c0 0xd87e03fe000003e0

def z564 : W := mkw 0x000be00000000000 0x0005f00000000000 0x4003f80000000000 0x2001fc0000000000

def z565 : W := mkw 0x80e007b4072407c1 0xc07003da039203e0 0x98e007fc070007c1 0xcc7003fe038003e0

def z566 : W := mkw 0x0060070007000601 0x8030038003800300 0xdd60870067006739 0x6eb043803380339c

def z567 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x092081006703e739 0x049040803381f39c

def z568 : W := mkw 0x4000020082008421 0x2000010041004210 0x0843060386038000 0x04218301c301c000

def z569 : W := mkw 0x610bc263d263d4b5 0x3085e131e931ea5a 0xffdbc6e3fee3fcff 0xffede371ff71fe7f

def z570 : W := mkw 0xa09d40f510f511c4 0x504ea07a887a88e2 0x229c40fc18fc18c6 0x914e207e0c7e0c63

def z571 : W := mkw 0x60095a69ba69bcaf 0x3004ad34dd34de57 0xffdbfee3fee3fcff 0xffedff71ff71fe7f

def z572 : W := mkw 0x647fe7f3d26194a5 0x323ff3f9e930ca52 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z573 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfcdb46e39ee38000 0xfe6da371cf71c000

def z574 : W := mkw 0x80f41fbc2fbc2fcb 0xc07a0fde17de17e5 0xbafcbffc67fc67d9 0xdd7e5ffe33fe33ec

def z575 : W := mkw 0x61094763d26196b5 0xb084a3b1e930cb5a 0xffdb47e3fee39fff 0xffeda3f1ff71cfff

def z576 : W := mkw 0x0060050005000200 0x8030028002800100 0x0020010001000300 0x0010008000800180

def z577 : W := mkw 0x61628763d722c6b5 0xb0b143b1eb91635a 0xdde387e3ff03e7ff 0xeef1c3f1ff81f3ff

def z578 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x094306038703e739 0x04a18301c381f39c

def z579 : W := mkw 0x606bc2619763d4a5 0x3035e130cbb1ea52 0xfffbc6e39fe3fce7 0xfffde371cff1fe73

def z580 : W := mkw 0xe47ffffffa6dbdef 0x723ffffffd36def7 0xffffffffffffffff 0xffffffffffffffff

def z581 : W := mkw 0x000018082808280a 0x00000c0414041405 0x0000b80060006018 0x00005c003000300c

def z582 : W := mkw 0x0000020002000401 0x0000010001000200 0x9840060006000401 0x4c20030003000200

def z583 : W := mkw 0x437fea0087dbfe31 0xa1bff50043edff18 0x7b7ff80007ffff39 0x3dbffc0003ffff9c

def z584 : W := mkw 0x007fe04110000000 0x003ff02088000000 0xf4fffee398000000 0xfa7fff71cc000000

def z585 : W := mkw 0x0074079007000601 0x803a03c803800300 0xb8fc07fc07000701 0xdc7e03fe03800380

def z586 : W := mkw 0x041d60d110000000 0x020eb06888000000 0x009800e000000000 0x004c007000000000

def z587 : W := mkw 0x8080022407b407c1 0xc040011203da03e0 0xbad806e007fc07c1 0xdd6c037003fe03e0

def z588 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0x0000001c180000c6 0x8000000e0c000063

def z589 : W := mkw 0x0100000005024210 0x8080000002812108 0x0000000001006318 0x000000000080318c

def z590 : W := mkw 0x0214280000982800 0x010a1400004c1400 0x00043800001c0000 0x00021c00000e0000

def z591 : W := mkw 0x0009400000411000 0x0004a00000208800 0x4103400000039800 0x2081a0000001cc00

def z592 : W := mkw 0x627fe26197f3d4a5 0x313ff130cbf9ea52 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z593 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xa604791c781c1ffe 0xd3023c8e3c0e0fff

def z594 : W := mkw 0x0009404110000000 0x0004a02088000000 0x209840e018000000 0x904c20700c000000

def z595 : W := mkw 0x0414309828000000 0x020a184c14000000 0x0004381c00000000 0x00021c0e00000000

def z596 : W := mkw 0x841d78dd380c294a 0x420ebc6e9c0614a5 0x229c78fc181c18c6 0x914e3c7e0c0e0c63

def z597 : W := mkw 0x61000763d22086b5 0xb08003b1e910435a 0x848007e3f80007fe 0xc24003f1fc0003ff

def z598 : W := mkw 0xc1001a0caf0eef7b 0xe0800d06578777bd 0xff24f91c7f1fffff 0xff927c8e3f8fffff

def z599 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x88d807fc06e007c0 0xc46c03fe037003e0

def z600 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x596386038703e001 0x2cb1c301c381f000

def z601 : W := mkw 0x80801a2c2fbc2fcb 0xc0400d1617de17e5 0xff24f91c7ffc7fff 0xff927c8e3ffe3fff

def z602 : W := mkw 0x41600702c7008631 0xa0b0038163804318 0x9c600703e7000739 0x4e300381f380039c

def z603 : W := mkw 0x417fe702c702c631 0xa0bff38163816318 0xfd7fff03e703e739 0x7ebfff81f381f39c

def z604 : W := mkw 0x02000800059a6800 0x0100040002cd3400 0x00000000011c6000 0x00000000008e3000

def z605 : W := mkw 0xc5fff7ffffb6c7f1 0xe2fffbffffdb63f8 0xffffffffffffe7f9 0xfffffffffffff3fc

def z606 : W := mkw 0x616bc763d763d6b5 0xb0b5e3b1ebb1eb5a 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z607 : W := mkw 0x0000100828000000 0x0000080414000000 0x2004781c18000000 0x90023c0e0c000000

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0x5120800001006001 0x2890400000803000

def z609 : W := mkw 0x606bc763d26194a5 0x3035e3b1e930ca52 0xfffbc7e3fee39ce7 0xfffde3f1ff71ce73

def z610 : W := mkw 0x2000006110200084 0x1000003088100042 0x008000e0180000c6 0x804000700c000063

def z611 : W := mkw 0x820bf80c284f794a 0x4105fc061427bca5 0xf727f91c791fffff 0xfb93fc8e3c8fffff

def z612 : W := mkw 0x457ff7dbff02c631 0xa2bffbedff816318 0xfcfffffffe038000 0xfe7fffffff01c000

def z613 : W := mkw 0x80800a2407bc2fcb 0xc040051203de17e5 0x0b00000007fc7fff 0x0580000003fe3fff

def z614 : W := mkw 0x0100050240000210 0x8080028120000108 0x0000010060000318 0x000000803000018c

def z615 : W := mkw 0x007ff00828000000 0x003ff80414000000 0xf47ff91c78000000 0xfa3ffc8e3c000000

def z616 : W := mkw 0x0162850245024210 0x80b1428122812108 0x0000000000000000 0x0000000000000000

def z617 : W := mkw 0x02ffe7b007f35681 0x817ff3d803f9ab40 0x08db06e006e38000 0x046d83700371c000

def z618 : W := mkw 0x0000100828000000 0x0000080414000000 0x0024b91c60000000 0x00125c8e30000000

def z619 : W := mkw 0x027fe00005d35000 0x013ff00002e9a800 0x597b800007e3e001 0x2cbdc00003f1f000

def z620 : W := mkw 0x8000100c2804014a 0x40000806140200a5 0xf700411c78001fff 0xfb80208e3c000fff

def z621 : W := mkw 0x067ffd9a6ddb7800 0x033ffecd36edbc00 0x7b7ff91c67fff801 0x3dbffc8e33fffc00

def z622 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x84208703e1006738 0x42104381f080339c

def z623 : W := mkw 0x0076859240000000 0x003b42c920000000 0xf4ff87ffe0000000 0xfa7fc3fff0000000

def z624 : W := mkw 0xc102980ee80ee97a 0x60814c07740774bd 0xf727f91ff91fffff 0xfb93fc8ffc8fffff

def z625 : W := mkw 0x84fff5df7d940340 0xc27ffaefbeca01a0 0xf4fffffff91c0300 0xfa7ffffffc8e0180

def z626 : W := mkw 0x0000000005024000 0x0000000002812000 0x090000000703e001 0x048000000381f000

def z627 : W := mkw 0x80f4079407940741 0xc07a03ca03ca03a0 0x9864071c071c0701 0x4c32038e038e0380

def z628 : W := mkw 0x80f41d9c2d9c2b4a 0xc07a0ece16ce15a5 0xf724f91c791c7fff 0xfb927c8e3c8e3fff

def z629 : W := mkw 0x84f417ff7fb407c1 0xc27a0bffbfda03e0 0xbefc07fffffc07c1 0xdf7e03fffffe03e0

def z630 : W := mkw 0x627fea6197fbfca5 0x313ff530cbfdfe52 0x7bfffee387fff801 0x3dffff71c3fffc00

def z631 : W := mkw 0x0162850245024210 0x80b1428122812108 0x596381006703e319 0x2cb1c0803381f18c

def z632 : W := mkw 0x80000804000c2940 0x40000402000614a0 0xf324f91c011c7fc1 0xf9927c8e008e3fe0

def z633 : W := mkw 0x0209480005db7800 0x0104a40002edbc00 0x7b5b400007fff801 0x3dada00003fffc00

def z634 : W := mkw 0x841d78dd380c294a 0x420ebc6e9c0614a5 0xf7bcf9fc791c7fff 0xfbde7cfe3c8e3fff

def z635 : W := mkw 0x477fffdbffdbfe31 0xa3bfffedffedff18 0xffffffffffffff39 0xffffffffffffff9c

def z636 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x8700011c791c7fff 0xc380008e3c8e3fff

def z637 : W := mkw 0x41628702c2008631 0xa0b1438161004318 0xd4638703e0000738 0x6a31c381f000039c

def z638 : W := mkw 0x8200180c2ddf794a 0x41000c0616efbca5 0xff24f91c7fffffff 0xff927c8e3fffffff

def z639 : W := mkw 0x4576b79aef02c631 0xa2bb5bcd77816318 0xdd67bf1fe703e739 0x6eb3df8ff381f39c

def z640 : W := mkw 0x0000022002200481 0x0000011001100240 0x0a00000006e004c1 0x0500000003700260

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0xf720c10079007fff 0xfb9060803c803fff

def z642 : W := mkw 0x00f407b007b00681 0x807a03d803d80340 0x98f807e007e00701 0x4c7c03f003f00380

def z643 : W := mkw 0x007fe00000000000 0x003ff00000000000 0x005b000000000000 0x002d800000000000

def z644 : W := mkw 0x2009406110611084 0x1004a03088308842 0x7bdb40e01ee398c7 0xbdeda0700f71cc63

def z645 : W := mkw 0x641d72f9ba6194a5 0x320eb97cdd30ca52 0xffdf7eff9ee39ce7 0xffefbf7fcf71ce73

def z646 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x4524f91c791c7b3e 0x22927c8e3c8e3d9f

def z647 : W := mkw 0x80fd47b407f517c1 0xc07ea3da03fa8be0 0xfbff47fc07ff9fc1 0xfdffa3fe03ffcfe0

def z648 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x20bcf9fc78000000 0x905e7cfe3c000000

def z649 : W := mkw 0x0080022007b00681 0x8040011003d80340 0x0800000006e00000 0x0400000003700000

def z650 : W := mkw 0x8062980c2d0e694a 0x40314c06168734a5 0xff67f91c7f1fffff 0xffb3fc8e3f8fffff

def z651 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x4127f800011ff800 0x2093fc00008ffc00

def z652 : W := mkw 0x027fe800004b7800 0x013ff4000025bc00 0x717ff8000003f800 0x38bffc000001fc00

def z653 : W := mkw 0x847ffddf780c294a 0x423ffeefbc0614a5 0xf6fffffff81c18c6 0xfb7ffffffc0e0c63

def z654 : W := mkw 0x0476b59a68000000 0x023b5acd34000000 0xb0fcbffc60000000 0xd87e5ffe30000000

def z655 : W := mkw 0x427fea0087dbfc21 0x213ff50043edfe10 0xff7ffe0387fffc21 0x7fbfff01c3fffe10

def z656 : W := mkw 0x0000004110000000 0x0000002088000000 0x848006e398000000 0xc2400371cc000000

def z657 : W := mkw 0x0062800000000000 0x0031400000000000 0x5063800000000000 0x2831c00000000000

def z658 : W := mkw 0x0476b59a68000000 0x023b5acd34000000 0xd467bf1fe0000000 0x6a33df8ff0000000

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x9020010001000701 0x4810008000800380

def z660 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x7324f91c611c7b19 0x39927c8e308e3d8c

def z661 : W := mkw 0x80f4059405940340 0xc07a02ca02ca01a0 0x3a7c011c07fc0301 0x1d3e008e03fe0180

def z662 : W := mkw 0x041ff0db78000000 0x020ff86dbc000000 0x649ff8fff8000000 0xb24ffc7ffc000000

def z663 : W := mkw 0x0162870247024611 0x80b1438123812308 0x9860870067006719 0x4c3043803380338c

def z664 : W := mkw 0xc1f68796c796c771 0xe0fb43cb63cb63b8 0xdd67871fe71fe739 0x6eb3c38ff38ff39c

def z665 : W := mkw 0x829d68b400fd39c0 0x414eb45a007e9ce0 0x229c78fc00fc18c0 0x914e3c7e007e0c60

def z666 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x4f0340039ee39ce7 0x2781a001cf71ce73

def z667 : W := mkw 0x82ffffbc2fff7fcb 0xc17fffde17ffbfe5 0xfffffffc7fffffff 0xfffffffe3fffffff

def z668 : W := mkw 0x80f417bc2fb407c1 0xc07a0bde17da03e0 0xfefcfffc7ffc07c1 0xff7e7ffe3ffe03e0

def z669 : W := mkw 0x80f4059405940340 0xc07a02ca02ca01a0 0xb224011c011c07c1 0xd912008e008e03e0

def z670 : W := mkw 0x0074000005900000 0x003a000002c80000 0x0858000006e00000 0x042c000003700000

def z671 : W := mkw 0x0062800005024000 0x0031400002812000 0x0843000006038000 0x042180000301c000

def z672 : W := mkw 0x001d600000000000 0x000eb00000000000 0x201c780000000000 0x100e3c0000000000

def z673 : W := mkw 0x80000804000c294a 0x40000402000614a5 0x02000000001c18c6 0x01000000000e0c63

def z674 : W := mkw 0x60095269ba6194a5 0x3004a934dd30ca52 0xfffffffffee39ce7 0xffffffffff71ce73

def z675 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x0ad806e007fc07c1 0x056c037003fe03e0

def z676 : W := mkw 0x8000000400040140 0x40000002000200a0 0x02000000011c07c1 0x01000000008e03e0

def z677 : W := mkw 0x0009404110411000 0x0004a02088208800 0xffdb46e39ee39801 0xffeda371cf71cc00

def z678 : W := mkw 0x067ffddb78d93800 0x033ffeedbc6c9c00 0xf6fffffff8fc1800 0xfb7ffffffc7e0c00

def z679 : W := mkw 0x8276b80c2d9e694a 0x413b5c0616cf34a5 0x0024b91c611c6318 0x00125c8e308e318c

def z680 : W := mkw 0x000010082800000a 0x0000080414000005 0x040000007800003e 0x020000003c00001f

def z681 : W := mkw 0x610942619763d6b5 0xb084a130cbb1eb5a 0xffdb46e39fe3ffff 0xffeda371cff1ffff

def z682 : W := mkw 0xe16bdf6fff6fffff 0xf0b5efb7ffb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z683 : W := mkw 0x80601f0c2f0c2f4b 0xc0300f86178617a5 0xff64ff1c7f1c7fff 0xffb27f8e3f8e3fff

def z684 : W := mkw 0x8009580c284d394a 0x4004ac0614269ca5 0xff7ff91c7fffffff 0xffbffc8e3fffffff

def z685 : W := mkw 0x6009404190419024 0x3004a020c820c812 0xf5db46e398039826 0xfaeda371cc01cc13

def z686 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x6704f81c781c78fe 0xb3827c0e3c0e3c7f

def z687 : W := mkw 0x027d680005d93800 0x013eb40002ec9c00 0x3a7c780007fc1801 0x1d3e3c0003fe0c00

def z688 : W := mkw 0x0000100828000000 0x0000080414000000 0x8400011c78000000 0xc200008e3c000000

def z689 : W := mkw 0xe08947f5926597e5 0xf044a3fac932cbf2 0xffdb47ff9ee39fe7 0xffeda3ffcf71cff3

def z690 : W := mkw 0x0074059000000000 0x003a02c800000000 0x0024011c00000000 0x0012008e00000000

def z691 : W := mkw 0x0009400000411000 0x0004a00000208800 0x085b000006e38000 0x042d80000371c000

def z692 : W := mkw 0x437fef02c7dbfe31 0xa1bff78163edff18 0x7b7ffe0387fff801 0x3dbfff01c3fffc00

def z693 : W := mkw 0x00f4059005900200 0x807a02c802c80100 0x0000000000000000 0x0000000000000000

def z694 : W := mkw 0x80f4022407b407c1 0xc07a011203da03e0 0x3a7c000007fc07c1 0x1d3e000003fe03e0

def z695 : W := mkw 0x82ffe7b407f757c1 0xc17ff3da03fbabe0 0xbaff07fc07ff87c1 0xdd7f83fe03ffc3e0

def z696 : W := mkw 0x607fe261926194a5 0x303ff130c930ca52 0xfffffee39ee39ce7 0xffffff71cf71ce73

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x7024f80000000000 0x38127c0000000000

def z698 : W := mkw 0x60094220826194a5 0x3004a1104130ca52 0x7b5b400006e39ce7 0x3dada0000371ce73

def z699 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xc500f91c78007ffe 0xe2807c8e3c003fff

def z700 : W := mkw 0x2009406110611084 0x1004a03088308842 0xf6db46e398e018c6 0xfb6da371cc700c63

def z701 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xd524b91c611c6739 0x6a925c8e308e339c

def z702 : W := mkw 0x0202a800000a6800 0x0101540000053400 0x0000b80000006000 0x00005c0000003000

def z703 : W := mkw 0x0000022002200481 0x0000011001100240 0x08d806e006e00000 0x046c037003700000

def z704 : W := mkw 0x80f417bc2fb407cb 0xc07a0bde17da03e5 0xbefc07fc7ffc07ff 0xdf7e03fe3ffe03ff

def z705 : W := mkw 0x027fe00005d35000 0x013ff00002e9a800 0x787ff80006e38000 0x3c3ffc000371c000

def z706 : W := mkw 0x60000220822084a5 0x3000011041104252 0x00000000000004e6 0x0000000000000273

def z707 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ff9007fffffff 0xffbffc803fffffff

def z708 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x085f380006ff8000 0x042f9c00037fc000

def z709 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xfdfffffffe038001 0xfeffffffff01c000

def z710 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdf638703e703ffff 0x6fb1c381f381ffff

def z711 : W := mkw 0x80000224022405c1 0x40000112011202e0 0xbadc06fc06fc04c1 0xdd6e037e037e0260

def z712 : W := mkw 0x027fedd115db7800 0x013ff6e88aedbc00 0xffffffff9ffff801 0xffffffffcffffc00

def z713 : W := mkw 0x4176a702c702c631 0xa0bb538163816318 0xdd67bf03e703e739 0x6eb3df81f381f39c

def z714 : W := mkw 0x809402b402b407c1 0xc04a015a015a03e0 0x229c00fc00fc07c0 0x914e007e007e03e0

def z715 : W := mkw 0x027fed9005db7800 0x013ff6c802edbc00 0x7b7ff91c07fff801 0x3dbffc8e03fffc00

def z716 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xfd67871fe703e739 0xfeb3c38ff381f39c

def z717 : W := mkw 0x200958493849380e 0x1004ac249c249c07 0x0000780018001806 0x00003c000c000c03

def z718 : W := mkw 0x41028702c702c631 0xa081438163816318 0xcd038703e703e739 0x6681c381f381f39c

def z719 : W := mkw 0x00001a282a282c8b 0x00000d1415141645 0xffd8fee07ee07cff 0xffec7f703f703e7f

def z720 : W := mkw 0x41768792c792c631 0xa0bb43c963c96318 0xffff87ffe7ffe739 0xffffc3fff3fff39c

def z721 : W := mkw 0x41768722c7b2c6b1 0xa0bb439163d96358 0xffff87e3e7ffe7f9 0xffffc3f1f3fff3fc

def z722 : W := mkw 0x80f407b647b407c1 0xc07a03db23da03e0 0xbefc07ffe7fc07c1 0xdf7e03fff3fe03e0

def z723 : W := mkw 0x007fe00005924000 0x003ff00002c92000 0x7b7ff80007ffe001 0x3dbffc0003fff000

def z724 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x497ff80007fff800 0x24bffc0003fffc00

def z725 : W := mkw 0x00f41fb82fb82e8b 0x807a0fdc17dc1745 0x4dd8fee07ee0783e 0x26ec7f703f703c1f

def z726 : W := mkw 0xc1f407b487b6c7f1 0xe0fa03da43db63f8 0xfffc87fc67ffe7f9 0xfffe43fe33fff3fc

def z727 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xfbff87ff87ffe7c1 0xfdffc3ffc3fff3e0

def z728 : W := mkw 0x451d72d9bf02c631 0xa28eb96cdf816318 0x299c78fc1f03e739 0x94ce3c7e0f81f39c

def z729 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0x2adf06ff86ff80c0 0x956f837fc37fc060

def z730 : W := mkw 0x047ff5db7d924000 0x023ffaedbec92000 0xffffffffffffe001 0xfffffffffffff000

def z731 : W := mkw 0x41628722c722c6b1 0xa0b1439163916358 0xfffbc7e3ffe3ffff 0xfffde3f1fff1ffff

def z732 : W := mkw 0x047ff5db7d900000 0x023ffaedbec80000 0xf4fffffff91c0000 0xfa7ffffffc8e0000

def z733 : W := mkw 0x041d70d938000000 0x020eb86c9c000000 0xa49c7eff98000000 0xd24e3f7fcc000000

def z734 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x22bc01fc01fc03c0 0x915e00fe00fe01e0

def z735 : W := mkw 0x828befb4026f7fc1 0xc145f7da0137bfe0 0xc183fffc0003ffc0 0xe0c1fffe0001ffe0

def z736 : W := mkw 0x41028202c702c631 0xa081410163816318 0xdd238103e703e739 0x6e91c081f381f39c

def z737 : W := mkw 0x007d480005d93800 0x003ea40002ec9c00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z738 : W := mkw 0x021fe80000db7800 0x010ff400006dbc00 0x7b5ff80006fff801 0x3daffc00037ffc00

def z739 : W := mkw 0x41628702c202c631 0xa0b1438161016318 0xd5638703e003e738 0x6ab1c381f001f39c

def z740 : W := mkw 0x41028502c002c230 0xa081428160016118 0x45038103e003e338 0x2281c081f001f19c

def z741 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xfd63c703ff03e739 0xfeb1e381ff81f39c

def z742 : W := mkw 0x417687b2c722c6b1 0xa0bb43d963916358 0xffff87ffe7e3e7f9 0xffffc3fff3f1f3fc

def z743 : W := mkw 0x027fed0005db7800 0x013ff68002edbc00 0xfb7fff0007fff801 0x7dbfff8003fffc00

def z744 : W := mkw 0x848bf26f7fb407c1 0xc245f937bfda03e0 0x4e03f803fffc07c1 0x2701fc01fffe03e0

def z745 : W := mkw 0xe1000a24876fffff 0xf080051243b7ffff 0x0b00000007ffffff 0x0580000003ffffff

def z746 : W := mkw 0x06001ddb7ddb7800 0x03000eedbeedbc00 0x8f8007fffffff801 0xc7c003fffffffc00

def z747 : W := mkw 0x8074059405940140 0x403a02ca02ca00a0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z748 : W := mkw 0x41000702c2008631 0xa080038161004318 0xdd638703e703e739 0x6eb1c381f381f39c

def z749 : W := mkw 0x047ff5db78411000 0x023ffaedbc208800 0xfffffffffee39ce7 0xffffffffff71ce73

def z750 : W := mkw 0x027fed0245db7800 0x013ff68122edbc00 0x7b7ffe0387fff801 0x3dbfff01c3fffc00

def z751 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf4fffffff9000701 0xfa7ffffffc800380

def z752 : W := mkw 0x020be800004b7800 0x0105f4000025bc00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z753 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf4fffffff80004e6 0xfa7ffffffc000273

def z754 : W := mkw 0x067ff5db7d924000 0x033ffaedbec92000 0xf4fffffff8000000 0xfa7ffffffc000000

def z755 : W := mkw 0x41e28722c7b2c6b1 0xa0f1439163d96358 0xdd638703e7e3e739 0x6eb1c381f3f1f39c

def z756 : W := mkw 0xe08017fdba2487ef 0xf0400bfedd1243f7 0x848007fff80007fe 0xc24003fffc0003ff

def z757 : W := mkw 0xc1f687b6c7b487f1 0xe0fb43db63da43f8 0xfeff87ffe7fc07f9 0xff7fc3fff3fe03fc

def z758 : W := mkw 0x007ff04938000000 0x003ff8249c000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z759 : W := mkw 0x027fe89005db7800 0x013ff44802edbc00 0x7bfff8fc07fff801 0xbdfffc7e03fffc00

def z760 : W := mkw 0x431d6f02c2d9be31 0xa18eb781616cdf18 0xa61c7f03e0fc1f38 0x530e3f81f07e0f9c

def z761 : W := mkw 0x0402b5db78000000 0x02015aedbc000000 0x8480bffff8000000 0xc2405ffffc000000

def z762 : W := mkw 0x660bf84bf84bf824 0x3305fc25fc25fc12 0x4503f803f803f826 0x2281fc01fc01fc13

def z763 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x4724f91c791c7fff 0x23927c8e3c8e3fff

def z764 : W := mkw 0x80f400b405b401c0 0x407a005a02da00e0 0xbafc01fc07fc07c1 0xdd7e00fe03fe03e0

def z765 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xc5238703e103e738 0x6291c381f081f39c

def z766 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xfb7ff91c07fff801 0xfdbffc8e03fffc00

def z767 : W := mkw 0xc19680b6c0b6c1f0 0x60cb405b605b60f8 0x679f80ffe0ffe0f8 0xb3cfc07ff07ff07c

def z768 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xc4a7fffff8000000 0xe253fffffc000000

def z769 : W := mkw 0x040955db78000000 0x0204aaedbc000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z770 : W := mkw 0x81f687b647b647d1 0xc0fb43db23db23e8 0xfeff87ffe7fc67d9 0xff7fc3fff3fe33ec

def z771 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf7fffffff9007fff 0xfbfffffffc803fff

def z772 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xf7fcfffc791c7fff 0xfbfe7ffe3c8e3fff

def z773 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x2abc01fc07fc07c1 0x955e00fe03fe03e0

def z774 : W := mkw 0x80f685b640b401c0 0x407b42db205a00e0 0xf6ff87ffe0fc00c0 0xfb7fc3fff07e0060

def z775 : W := mkw 0x006bd54b78000000 0x0035eaa5bc000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z776 : W := mkw 0x0074059000900000 0x003a02c800480000 0xb2fc07fc00fc0000 0xd97e03fe007e0000

def z777 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x009c00fc00fc0000 0x004e007e007e0000

def z778 : W := mkw 0x067fe8d115db7800 0x033ff4688aedbc00 0x7bfff8e007fff801 0x3dfffc7003fffc00

def z779 : W := mkw 0x216bc56355635294 0x90b5e2b1aab1a94a 0x22b8c1e079e07bde 0x915c60f03cf03def

def z780 : W := mkw 0x040bf5db78000000 0x0205faedbc000000 0xf4a7fffff8000000 0xfa53fffffc000000

def z781 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xbbff07ff87ffe7f9 0xddff83ffc3fff3fc

def z782 : W := mkw 0x6276aa6197baeca5 0x313b5530cbdd7652 0x84a4bee3991c64e6 0xc2525f71cc8e3273

def z783 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf6fffffff80018c6 0xfb7ffffffc000c63

def z784 : W := mkw 0xc0000224822485e1 0x60000112411242f0 0xffff87ffe7ffe7f9 0xffffc3fff3fff3fc

def z785 : W := mkw 0x80000024002401c0 0x40000012001200e0 0x229c00fc00fc00c0 0x914e007e007e0060

def z786 : W := mkw 0x41f687b2c7b2c6b1 0xa0fb43d963d96358 0xffff87e3e7ffe739 0x7fffc3f1f3fff39c

def z787 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xb0ff7fff98000000 0xd87fbfffcc000000

def z788 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xa2bc07fc01fc07c0 0xd15e03fe00fe03e0

def z789 : W := mkw 0x027fed9245db7800 0x013ff6c922edbc00 0xffffffffe7fff801 0xfffffffff3fffc00

def z790 : W := mkw 0x80f687b407b647c1 0xc07b43da03db23e0 0xbaff07fc07ff87c1 0xdd7f83fe03ffc3e0

def z791 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbbfc07fc07fc1fe7 0xddfe03fe03fe0ff3

def z792 : W := mkw 0x80f687b647b407c1 0xc07b43db23da03e0 0xffff87ffe7fc67f9 0xffffc3fff3fe33fc

def z793 : W := mkw 0x041435db78000000 0x020a1aedbc000000 0x84843ffff8000000 0xc2421ffffc000000

def z794 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x98638703e703e719 0x4c31c381f381f38c

def z795 : W := mkw 0x807407b4022405c1 0x403a03da011202e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z796 : W := mkw 0x809407b402b407c1 0xc04a03da015a03e0 0xb2bc07fc01fc07c1 0xd95e03fe00fe03e0

def z797 : W := mkw 0x80094845100c294a 0x4004a422880614a5 0xf7db46e3991c7fff 0xfbeda371cc8e3fff

def z798 : W := mkw 0xe0095a6dba6dbdef 0x7004ad36dd36def7 0x08ffbfffe7ffe318 0x047fdffff3fff18c

def z799 : W := mkw 0xe0800a2487fdbfef 0xf040051243fedff7 0x0b00000007ffffff 0x0580000003ffffff

def z800 : W := mkw 0x41628202c702c631 0xa0b1410163816318 0x5d638003e703e739 0x2eb1c001f381f39c

def z801 : W := mkw 0x80600724072407c1 0xc0300392039203e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z802 : W := mkw 0x41000702c702c631 0xa080038163816318 0xdd430703e703e739 0x6ea18381f381f39c

def z803 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xbbfc87fc67ffe7f9 0xddfe43fe33fff3fc

def z804 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf4df7eff98000000 0xfa6fbf7fcc000000

def z805 : W := mkw 0x61094261926196b5 0xb084a130c930cb5a 0xffdb46e39ee39fff 0xffeda371cf71cfff

def z806 : W := mkw 0x41628502c502c230 0xa0b1428162816118 0xd5238103e103e739 0x6a91c081f081f39c

def z807 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdd638703ff03e7ff 0xeeb1c381ff81f3ff

def z808 : W := mkw 0x80f405b400b401c0 0x407a02da005a00e0 0x22dc06fc00fc00c0 0x916e037e007e0060

def z809 : W := mkw 0x41768702c702c631 0xa0bb438163816318 0xfd7f8703e703e739 0x7ebfc381f381f39c

def z810 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x84ffbffff8000000 0xc27fdffffc000000

def z811 : W := mkw 0x847fedd7500c294a 0x423ff6eba80614a5 0x03db06e3811c7fff 0x01ed8371c08e3fff

def z812 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xffffc7ffffffffff 0xffffe3ffffffffff

def z813 : W := mkw 0x037fed0245db7a10 0x81bff68122edbd08 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z814 : W := mkw 0x809400b405b401c0 0x404a005a02da00e0 0x2a9c00fc07fc00c1 0x954e007e03fe0060

def z815 : W := mkw 0x0276a80005db7800 0x013b540002edbc00 0x7b24f80007fff801 0x3d927c0003fffc00

def z816 : W := mkw 0x02ffed9005db7a00 0x817ff6c802edbd00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z817 : W := mkw 0x067ff5db78d11000 0x033ffaedbc688800 0xf4fffffff8e00000 0xfa7ffffffc700000

def z818 : W := mkw 0x0200080005db7800 0x0100040002edbc00 0x4b00f80007fff801 0x25807c0003fffc00

def z819 : W := mkw 0x057ff5db7d024210 0x82bffaedbe812108 0xfdffffffff03e319 0xfeffffffff81f18c

def z820 : W := mkw 0x0076959a68000000 0x003b4acd34000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z821 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x229c00fc01fc07c1 0x914e007e00fe03e0

def z822 : W := mkw 0x80f405b405b403c0 0xc07a02da02da01e0 0x00bc01fc01fc0300 0x005e00fe00fe0180

def z823 : W := mkw 0x80f405b405b403c0 0xc07a02da02da01e0 0x229c00fc00fc00c0 0x914e007e007e0060

def z824 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x88fc07fc07fc07c0 0xc47e03fe03fe03e0

def z825 : W := mkw 0x0609784938493800 0x0304bc249c249c00 0x0000780018001800 0x00003c000c000c00

def z826 : W := mkw 0x476bff4bff4bfe31 0xa3b5ffa5ffa5ff18 0xdd63ff03ff03ff39 0x6eb1ff81ff81ff9c

def z827 : W := mkw 0xe0000a24822cadef 0x70000512411656f7 0x03000000011c7fff 0x01800000008e3fff

def z828 : W := mkw 0x020be80005db7800 0x0105f40002edbc00 0x7b5bf80007fff801 0x3dadfc0003fffc00

def z829 : W := mkw 0x0214280005db7800 0x010a140002edbc00 0x0b04380007fff801 0x05821c0003fffc00

def z830 : W := mkw 0x41628502c502c230 0xa0b1428162816118 0x00238103e103e318 0x0011c081f081f18c

def z831 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfeff07ff87fc07c1 0xff7f83ffc3fe03e0

def z832 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfefc47fc1ffc07c1 0xff7e23fe0ffe03e0

def z833 : W := mkw 0x640bf84bf849b82e 0x3205fc25fc24dc17 0x4503f803f803f83e 0x2281fc01fc01fc1f

def z834 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xfb7ff90007ffff01 0x7dbffc8003ffff80

def z835 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xbadb46e39ee39cc7 0xdd6da371cf71ce63

def z836 : W := mkw 0x041ff5db78000000 0x020ffaedbc000000 0xe49ffffff8000000 0xf24ffffffc000000

def z837 : W := mkw 0x41628722c722c6b1 0xa0b1439163916358 0xddfb87e3e7e3e739 0x6efdc3f1f3f1f39c

def z838 : W := mkw 0x027fe84115db7800 0x013ff4208aedbc00 0x7bfffee387fff801 0x3dffff71c3fffc00

def z839 : W := mkw 0x227fe84115db7804 0x113ff4208aedbc02 0x7b7ff8001ffff807 0x3dbffc000ffffc03

def z840 : W := mkw 0x861d78dd38dd394a 0x430ebc6e9c6e9ca5 0x229c78fc18fc18c6 0x914e3c7e0c7e0c63

def z841 : W := mkw 0xc1f407b6c7b487f1 0xe0fa03db63da43f8 0xfffc87ffe7fc67f9 0xfffe43fff3fe33fc

def z842 : W := mkw 0xc1f407b487b6c7f1 0xe0fa03da43db63f8 0xbafc07fc07ff87c1 0xdd7e03fe03ffc3e0

def z843 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xffff47ff9ee39ce7 0xffffa3ffcf71ce73

def z844 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xa4bcfffff8000000 0xd25e7ffffc000000

def z845 : W := mkw 0xe100176ffa2487ff 0xf0800bb7fd1243ff 0x848007fff80007fe 0xc24003fffc0003ff

def z846 : W := mkw 0x41028202c202c631 0xa081410161016318 0x45038003e003e738 0x2281c001f001f39c

def z847 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x59638703e703e319 0x2cb1c381f381f18c

def z848 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x3afc07fc07fc0301 0x1d7e03fe03fe0180

def z849 : W := mkw 0x60095a49ba49bc2f 0x3004ad24dd24de17 0xdd63ff03ff03ff3f 0x6eb1ff81ff81ff9f

def z850 : W := mkw 0xe0fd45d595d59364 0xf07ea2eacaeac9b2 0x4527411f991f9b26 0x2293a08fcc8fcd93

def z851 : W := mkw 0x046295db78000000 0x02314aedbc000000 0xf4e7fffff8000000 0xfa73fffffc000000

def z852 : W := mkw 0xc1800a2487beeffb 0xe0c0051243df77fd 0x0b00000007ffffff 0x0580000003ffffff

def z853 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf7fffffff8001801 0xfbfffffffc000c00

def z854 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfefc87fc67fc07c1 0xff7e43fe33fe03e0

def z855 : W := mkw 0x00768800059a6800 0x003b440002cd3400 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z856 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x64dffefff8000000 0xb26fff7ffc000000

def z857 : W := mkw 0x0200080005db7800 0x0100040002edbc00 0x0b24b80007fff801 0x05925c0003fffc00

def z858 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x4b27f80007fff801 0x2593fc0003fffc00

def z859 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7b7ff8001ffff8c7 0xbdbffc000ffffc63

def z860 : W := mkw 0xc1629f0eef0eef7b 0xe0b14f87778777bd 0x2a477e1f9e1f98c6 0x9523bf0fcf0fcc63

def z861 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xfd67ff03e703e739 0x7eb3ff81f381f39c

def z862 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0x2324f91c791c7fff 0x91927c8e3c8e3fff

def z863 : W := mkw 0xc19402b487b6c7f1 0xe0ca015a43db63f8 0x2b9c00fc07ffe7f9 0x95ce007e03fff3fc

def z864 : W := mkw 0x0074009005900000 0x003a004802c80000 0x3afc00fc07fc0001 0x9d7e007e03fe0000

def z865 : W := mkw 0xc0f407b487b487e1 0xe07a03da43da43f0 0xbbfc07fc07ff87e1 0xddfe03fe03ffc3f0

def z866 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdc638703e703e318 0x6e31c381f381f18c

def z867 : W := mkw 0x047d75d938000000 0x023ebaec9c000000 0xf4ff7fff98000000 0xfa7fbfffcc000000

def z868 : W := mkw 0x809402b402b405c1 0x404a015a015a02e0 0x2a9c00fc06fc04c1 0x954e007e037e0260

def z869 : W := mkw 0x021d680000d93800 0x010eb400006c9c00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z870 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xf79c40fc18fc1ce7 0xfbce207e0c7e0e73

def z871 : W := mkw 0xc1628726c726c7f1 0xe0b14393639363f8 0xffff87ffe7ffe7f9 0xffffc3fff3fff3fc

def z872 : W := mkw 0x046bf5db78000000 0x0235faedbc000000 0xd4e3fffff8000000 0xea71fffffc000000

def z873 : W := mkw 0xc0f407b487b487e1 0xe07a03da43da43f0 0xffff47ff9fff9fe7 0xffffa3ffcfffcff3

def z874 : W := mkw 0x047ff5db78024000 0x023ffaedbc012000 0xf5fffffff803e000 0xfafffffffc01f000

def z875 : W := mkw 0x047ff5db7d900000 0x023ffaedbec80000 0xfcfffffffee00000 0xfe7fffffff700000

def z876 : W := mkw 0xc09402b482b485e1 0x604a015a415a42f0 0xffdf06ff86ff84e1 0xffef837fc37fc270

def z877 : W := mkw 0x247ff5db78411004 0x123ffaedbc208802 0xf4fffffff8001806 0xfa7ffffffc000c03

def z878 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x3a7fb80007ffe001 0x1d3fdc0003fff000

def z879 : W := mkw 0x80f407b407b647c1 0xc07a03da03db23e0 0xbbfc07fc07ffe7c1 0xddfe03fe03fff3e0

def z880 : W := mkw 0x0262880005db7800 0x0131440002edbc00 0x7b67f80007fff801 0x3db3fc0003fffc00

def z881 : W := mkw 0x809405b400b403c0 0xc04a02da005a01e0 0x229c01fc00fc03c0 0x914e00fe007e01e0

def z882 : W := mkw 0x41628722c722c6b1 0xa0b1439163916358 0xdf638703e7e3e7f9 0x6fb1c381f3f1f3fc

def z883 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xfefffffffee00001 0xff7fffffff700000

def z884 : W := mkw 0x809402b402b405c1 0x404a015a015a02e0 0xa29c06fc00fc04c0 0xd14e037e007e0260

def z885 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x70ffffffe0000000 0x387ffffff0000000

def z886 : W := mkw 0x827ff00c2dd7514a 0x413ff80616eba8a5 0x8c5b011c7ee387fe 0xc62d808e3f71c3ff

def z887 : W := mkw 0x007fe00005d11000 0x003ff00002e88800 0x7b7ff80007ff9801 0x3dbffc0003ffcc00

def z888 : W := mkw 0x6476b7baea6194a5 0x323b5bdd7530ca52 0x0b24b91c66e39ce7 0x05925c8e3371ce73

def z889 : W := mkw 0x61628722c722c6b5 0xb0b143916391635a 0xdd638703e703e7ff 0x6eb1c381f381f3ff

def z890 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xff678703e71fe739 0x7fb3c381f38ff39c

def z891 : W := mkw 0x0000080000493800 0x0000040000249c00 0x7b24f80007fff801 0x3d927c0003fffc00

def z892 : W := mkw 0x027d680005db7800 0x013eb40002edbc00 0x3b7c780007fff801 0x1dbe3c0003fffc00

def z893 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf6fffffff91c0001 0xfb7ffffffc8e0000

def z894 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfffcc7fc7ffc7fff 0xfffe63fe3ffe3fff

def z895 : W := mkw 0x80f405b400b401c0 0x407a02da005a00e0 0x22bc01fc00fc00c0 0x915e00fe007e0060

def z896 : W := mkw 0x80f400b400b401c0 0x407a005a005a00e0 0x32fc00fc00fc00c0 0x997e007e007e0060

def z897 : W := mkw 0x809405b400b401c0 0x404a02da005a00e0 0xa29c07fc00fc00c0 0xd14e03fe007e0060

def z898 : W := mkw 0x047ff0d938000000 0x023ff86c9c000000 0xf4fffeff98000000 0xfa7fff7fcc000000

def z899 : W := mkw 0x047fe5d350000000 0x023ff2e9a8000000 0xf0ffffff80000000 0xf87fffffc0000000

def z900 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf5fffffff8001826 0xfafffffffc000c13

def z901 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbefc07fc67fc07f9 0xdf7e03fe33fe03fc

def z902 : W := mkw 0x80f687b647b407c1 0xc07b43db23da03e0 0xbaff07ff87fc07c1 0xdd7f83ffc3fe03e0

def z903 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfafcfffc07fc07c1 0xfd7e7ffe03fe03e0

def z904 : W := mkw 0x2009406110611084 0x1004a03088308842 0xffdb46e39ee398c7 0xffeda371cf71cc63

def z905 : W := mkw 0xc1f687b487b6c7f1 0xe0fb43da43db63f8 0xfbff87fc07ffe7f9 0xfdffc3fe03fff3fc

def z906 : W := mkw 0x060bf84b784b780a 0x0305fc25bc25bc05 0x4503f803f803f83e 0x2281fc01fc01fc1f

def z907 : W := mkw 0x041d75db78000000 0x020ebaedbc000000 0xf4bcfffff8000000 0xfa5e7ffffc000000

def z908 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7b7ff90067fffb19 0x3dbffc8033fffd8c

def z909 : W := mkw 0x8676bd9e6d9e694a 0x433b5ecf36cf34a5 0x0024b91c611c6318 0x00125c8e308e318c

def z910 : W := mkw 0x41628002c502c030 0x20b1400162816018 0xdd638103e703e739 0x6eb1c081f381f39c

def z911 : W := mkw 0xe0000a24826dbdef 0x700005124136def7 0x0b00000006ff9ce7 0x05800000037fce73

def z912 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xa4df7ffff8000000 0xd26fbffffc000000

def z913 : W := mkw 0x047ff5db7d024000 0x023ffaedbe812000 0xfcfffffffe038000 0xfe7fffffff01c000

def z914 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x6fdb46e39ee398e6 0xb7eda371cf71cc73

def z915 : W := mkw 0x0200080005db7800 0x0100040002edbc00 0x2b04780007fff801 0x15823c0003fffc00

def z916 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfbfc47fc07fc1fc1 0xfdfe23fe03fe0fe0

def z917 : W := mkw 0x021d680005db7800 0x010eb40002edbc00 0x7b3cf80007fff801 0x3d9e7c0003fffc00

def z918 : W := mkw 0x809407b407b407c1 0xc04a03da03da03e0 0xaa9c07fc07fc07c1 0xd54e03fe03fe03e0

def z919 : W := mkw 0x80f402b407b407c1 0xc07a015a03da03e0 0x3afc00fc07fc07c1 0x9d7e007e03fe03e0

def z920 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf5fffffff9006001 0xfafffffffc803000

def z921 : W := mkw 0x80f687b647b407c1 0xc07b43db23da03e0 0xbafc87fc67fc07c1 0xdd7e43fe33fe03e0

def z922 : W := mkw 0x809402b407b407c1 0xc04a015a03da03e0 0xbadc06fc07fc07c1 0xdd6e037e03fe03e0

def z923 : W := mkw 0x4576a792c702c631 0xa2bb53c963816318 0xdd638703e703e739 0x6eb1c381f381f39c

def z924 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ff80007fffc21 0x7fbffc0003fffe10

def z925 : W := mkw 0x057ff5db78024010 0x02bffaedbc012008 0xf4fffffff8006018 0xfa7ffffffc00300c

def z926 : W := mkw 0x470bf84bf84bf830 0x2385fc25fc25fc18 0x4503f803f803f838 0x2281fc01fc01fc1c

def z927 : W := mkw 0x067fe84355db7800 0x033ff421aaedbc00 0x7b7ff80387fff801 0x3dbffc01c3fffc00

def z928 : W := mkw 0x040975db78000000 0x0204baedbc000000 0x84807ffff8000000 0xc2403ffffc000000

def z929 : W := mkw 0x057ff5db7d024210 0x82bffaedbe812108 0xf5fffffff9006739 0xfafffffffc80339c

def z930 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xc4dbfffff8000000 0xe26dfffffc000000

def z931 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfffbc7e3fee39ce7 0xfffde3f1ff71ce73

def z932 : W := mkw 0x80f405b405b403c0 0xc07a02da02da01e0 0x3afc01fc07fc03c1 0x9d7e00fe03fe01e0

def z933 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x98fc07fc07fc0701 0x4c7e03fe03fe0380

def z934 : W := mkw 0x0162850245024210 0x80b1428122812108 0xdd638703e703e319 0x6eb1c381f381f18c

def z935 : W := mkw 0x060bf849384b7800 0x0305fc249c25bc00 0x4103f8001803f800 0x2081fc000c01fc00

def z936 : W := mkw 0x80f402b407b405c1 0x407a015a03da02e0 0xbafc06fc07fc04c1 0xdd7e037e03fe0260

def z937 : W := mkw 0x040bf5db78000000 0x0205faedbc000000 0xf4dbfffff8000000 0xfa6dfffffc000000

def z938 : W := mkw 0x0276a80005db7800 0x013b540002edbc00 0x5b67b80007fff801 0x2db3dc0003fffc00

def z939 : W := mkw 0x057ff5db7d024210 0x82bffaedbe812108 0xf4fffffff8000000 0xfa7ffffffc000000

def z940 : W := mkw 0xc19407b6c2b487f1 0xe0ca03db615a43f8 0xa69c07ffe0fc07f8 0xd34e03fff07e03fc

def z941 : W := mkw 0x616bdf4bff4bfe3f 0xb0b5efa5ffa5ff1f 0xdd63ff03ff03ff3f 0x6eb1ff81ff81ff9f

def z942 : W := mkw 0x81f685b645b643d0 0xc0fb42db22db21e8 0x22bc81fc61fc63d8 0x915e40fe30fe31ec

def z943 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xffff07ff87ff87e1 0xffff83ffc3ffc3f0

def z944 : W := mkw 0x0062850245024000 0x0031428122812000 0xdd638703e703e739 0x6eb1c381f381f39c

def z945 : W := mkw 0x0476b5db78000000 0x023b5aedbc000000 0xd4e7bffff8000000 0xea73dffffc000000

def z946 : W := mkw 0x80f405b405b403c0 0xc07a02da02da01e0 0xb2fc07fc01fc03c0 0xd97e03fe00fe01e0

def z947 : W := mkw 0x0276a800059a6800 0x013b540002cd3400 0x7b7fb80007ffe001 0x3dbfdc0003fff000

def z948 : W := mkw 0x40000220822084a1 0x2000011041104250 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z949 : W := mkw 0x021d680005db7800 0x010eb40002edbc00 0x7b5f780007fff801 0x3dafbc0003fffc00

def z950 : W := mkw 0xc1f407b6c7b487f1 0xe0fa03db63da43f8 0xbafc07ff87fc07c1 0xdd7e03ffc3fe03e0

def z951 : W := mkw 0x047ff5db7d000000 0x023ffaedbe800000 0xfcffffffff000001 0xfe7fffffff800000

def z952 : W := mkw 0x406282008702c421 0x2031410043816210 0xdd638703e703e739 0x6eb1c381f381f39c

def z953 : W := mkw 0x41028002c002c030 0x2081400160016018 0xc5038103e003e738 0x6281c081f001f39c

def z954 : W := mkw 0x057ff5db78000210 0x82bffaedbc000108 0xf4fffffff8000318 0xfa7ffffffc00018c

def z955 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfbfc87fc07fc67c1 0xfdfe43fe03fe33e0

def z956 : W := mkw 0x82f6a7b407b647c1 0xc17b53da03db23e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z957 : W := mkw 0x026be80005db7800 0x0135f40002edbc00 0x5b63f80007fff801 0x2db1fc0003fffc00

def z958 : W := mkw 0x81f687b647b647d1 0xc0fb43db23db23e8 0xfffc87fc67fc67f9 0xfffe43fe33fe33fc

def z959 : W := mkw 0xe0f407b487b487e5 0xf07a03da43da43f2 0xbafc07fc07fc07e7 0xdd7e03fe03fe03f3

def z960 : W := mkw 0x0476b59a68000000 0x023b5acd34000000 0xf4ffbfffe0000000 0xfa7fdffff0000000

def z961 : W := mkw 0x007d55d938000000 0x003eaaec9c000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z962 : W := mkw 0x04fff5db7d900200 0x827ffaedbec80100 0xf4fffffff8000000 0xfa7ffffffc000000

def z963 : W := mkw 0x041d75db78000000 0x020ebaedbc000000 0xf4df7ffff8000000 0xfa6fbffffc000000

def z964 : W := mkw 0x41768702c792c631 0xa0bb438163c96318 0xdd7b8703e7e3e739 0x6ebdc381f3f1f39c

def z965 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf5fffffff8000421 0xfafffffffc000210

def z966 : W := mkw 0xa21d786d38fd39ce 0x510ebc369c7e9ce7 0x229c78fc18fc18c6 0x914e3c7e0c7e0c63

def z967 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xffff46e39fff9ce7 0xffffa371cfffce73

def z968 : W := mkw 0x84f6a7b647b407c1 0xc27b53db23da03e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z969 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xffdb47e3fee39fff 0xffeda3f1ff71cfff

def z970 : W := mkw 0x047415db78000000 0x023a0aedbc000000 0xf4fcfffff8000000 0xfa7e7ffffc000000

def z971 : W := mkw 0x047d75db78000000 0x023ebaedbc000000 0xb4fc7ffff8000000 0xda7e3ffffc000000

def z972 : W := mkw 0xc1f407b6c7b487f1 0xe0fa03db63da43f8 0xffff07ffe7ff87f9 0xffff83fff3ffc3fc

def z973 : W := mkw 0x0209480005db7800 0x0104a40002edbc00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z974 : W := mkw 0x041d75db78000000 0x020ebaedbc000000 0x209c7eff98000000 0x904e3f7fcc000000

def z975 : W := mkw 0x0476b5db78000000 0x023b5aedbc000000 0xf4a4fffff8000000 0xfa527ffffc000000

def z976 : W := mkw 0x81f407b407b647d1 0xc0fa03da03db23e8 0xbafc07fc07fc67d9 0xdd7e03fe03fe33ec

def z977 : W := mkw 0xa41d78fd386d39ce 0x520ebc7e9c369ce7 0x229c78fc18fc18c6 0x914e3c7e0c7e0c63

def z978 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x229c40fc18fc18c6 0x914e207e0c7e0c63

def z979 : W := mkw 0x41628722c722c6b1 0xa0b1439163916358 0xdde387e3e703e7f9 0xeef1c3f1f381f3fc

def z980 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xcddb46e39ee39ce6 0xe6eda371cf71ce73

def z981 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbafc07fc06fc00c0 0xdd7e03fe037e0060

def z982 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xb8fc07fc07fc0300 0xdc7e03fe03fe0180

def z983 : W := mkw 0x809402b402b405c1 0x404a015a015a02e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z984 : W := mkw 0xa09d58fd38fd39ce 0x504eac7e9c7e9ce7 0x229c78fc18fc18c6 0x914e3c7e0c7e0c63

def z985 : W := mkw 0x41028702c202c631 0xa081438161016318 0xd5238703e103e739 0x6a91c381f081f39c

def z986 : W := mkw 0x0276a80005db7800 0x013b540002edbc00 0x3b7cb80007fff801 0x1dbe5c0003fffc00

def z987 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xd4ffbfffe0000000 0x6a7fdffff0000000

def z988 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7f7ff80067fff839 0x3fbffc0033fffc1c

def z989 : W := mkw 0x007407b007b00481 0x003a03d803d80240 0xbafc07fc07fc04c1 0xdd7e03fe03fe0260

def z990 : W := mkw 0x80f6a7b407b407c1 0xc07b53da03da03e0 0xbafcbffc07fc07c1 0xdd7e5ffe03fe03e0

def z991 : W := mkw 0x8080022407b407c1 0xc040011203da03e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z992 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x4b5bf80007fff801 0x25adfc0003fffc00

def z993 : W := mkw 0x80f407b402b407c1 0xc07a03da015a03e0 0xb2fc07fc00fc07c0 0xd97e03fe007e03e0

def z994 : W := mkw 0x067ff5db78435000 0x033ffaedbc21a800 0xf4fffffff8038000 0xfa7ffffffc01c000

def z995 : W := mkw 0x041ff0db78000000 0x020ff86dbc000000 0xf4dffefff8000000 0xfa6fff7ffc000000

def z996 : W := mkw 0x037fed0245db7a10 0x81bff68122edbd08 0xff7fff03e7fffb19 0x7fbfff81f3fffd8c

def z997 : W := mkw 0x0276a80005db7800 0x013b540002edbc00 0x0824b80007ffe000 0x04125c0003fff000

def z998 : W := mkw 0xc0001a0caa0cad6b 0x60000d06550656b5 0xff477e1f9e1f9ce7 0xffa3bf0fcf0fce73

def z999 : W := mkw 0xe009404590459164 0x7004a022c822c8b2 0xf727411f991f9fe7 0xfb93a08fcc8fcff3

def z1000 : W := mkw 0x027fed0005db7a00 0x813ff68002edbd00 0x7b7ff90007fffb01 0x3dbffc8003fffd80

def z1001 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbbfc07fc07fc67f9 0xddfe03fe03fe33fc

def z1002 : W := mkw 0x021d680000d93800 0x010eb400006c9c00 0x2a5f780006ff9800 0x152fbc00037fcc00

def z1003 : W := mkw 0xe2800a2487ffffe5 0xf140051243fffff2 0x0b00000007ffffe7 0x0580000003fffff3

def z1004 : W := mkw 0x809402b407b407c1 0xc04a015a03da03e0 0xbabc01fc07fc07c1 0xdd5e00fe03fe03e0

def z1005 : W := mkw 0x027fed0245db7800 0x013ff68122edbc00 0xff7fff03e7ffff39 0x7fbfff81f3ffff9c

def z1006 : W := mkw 0x0074079007900601 0x803a03c803c80300 0xbafc07fc07fc0701 0xdd7e03fe03fe0380

def z1007 : W := mkw 0x620bf849b84bf82e 0x3105fc24dc25fc17 0x4503f803f803f83e 0x2281fc01fc01fc1f

def z1008 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x4d238103e703e739 0x2691c081f381f39c

def z1009 : W := mkw 0x80f400b405b401c0 0x407a005a02da00e0 0x2adc00fc06fc00c0 0x956e007e037e0060

def z1010 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7a7ff80006ff9800 0x3d3ffc00037fcc00

def z1011 : W := mkw 0x80f687b407b407c1 0xc07b43da03da03e0 0xfaff87fc07fc07c1 0xfd7fc3fe03fe03e0

def z1012 : W := mkw 0x4376a702c792c631 0xa1bb538163c96318 0xdd638703e703e739 0x6eb1c381f381f39c

def z1013 : W := mkw 0x0476b5db78000000 0x023b5aedbc000000 0xb4fcbffff8000000 0xda7e5ffffc000000

def z1014 : W := mkw 0x60001228aa6194a5 0x300009145530ca52 0xff24f91c7ee39ce7 0xff927c8e3f71ce73

def z1015 : W := mkw 0x60095849b849b82e 0x3004ac24dc24dc17 0x4503780398039826 0x2281bc01cc01cc13

def z1016 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x3adc00fc06fc00c1 0x9d6e007e037e0060

def z1017 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xaedb46e39ee39ce6 0xd76da371cf71ce73

def z1018 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xcd438703e603e738 0x66a1c381f301f39c

def z1019 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x2a7ff80007fff800 0x153ffc0003fffc00

def z1020 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfffc07fc07fc07e1 0xfffe03fe03fe03f0

def z1021 : W := mkw 0x41628792c702c631 0xa0b143c963816318 0xdde387ffe703e739 0xeef1c3fff381f39c

def z1022 : W := mkw 0x80f680b405b641c0 0x407b405a02db20e0 0x7bff80fc07ffe0c1 0xbdffc07e03fff060

def z1023 : W := mkw 0x81f687b647b647d1 0xc0fb43db23db23e8 0xfbff87fc67ffe7d9 0xfdffc3fe33fff3ec

def z1024 : W := mkw 0x41f68792c792c631 0xa0fb43c963c96318 0xdd638703e703e739 0x6eb1c381f381f39c

def z1025 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x0b7fb80007fff801 0x05bfdc0003fffc00

def z1026 : W := mkw 0x021d680000d93800 0x010eb400006c9c00 0x2b1c780006ff9801 0x158e3c00037fcc00

def z1027 : W := mkw 0x2009406110611084 0x1004a03088308842 0xf7b8c1e079e07fff 0xfbdc60f03cf03fff

def z1028 : W := mkw 0x060bf84b78493800 0x0305fc25bc249c00 0x4403f803f8001800 0x2201fc01fc000c00

def z1029 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf4fffffff8000738 0xfa7ffffffc00039c

def z1030 : W := mkw 0x808007b4022407c1 0xc04003da011203e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z1031 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xbaff87ffe7ffe7d9 0xdd7fc3fff3fff3ec

def z1032 : W := mkw 0x047ff5db7d024000 0x023ffaedbe812000 0xfdffffffff03e739 0xfeffffffff81f39c

def z1033 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xb2dc06fc00fc00c0 0xd96e037e007e0060

def z1034 : W := mkw 0x41e287b2c722c6b1 0xa0f143d963916358 0xdde387e3e703e739 0x6ef1c3f1f381f39c

def z1035 : W := mkw 0x41628702c792c631 0xa0b1438163c96318 0xdf638703e7ffe739 0x6fb1c381f3fff39c

def z1036 : W := mkw 0x809407b402b407c1 0xc04a03da015a03e0 0x229c06fc00fc00c0 0x914e037e007e0060

def z1037 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfffb47e39fe39fe7 0xfffda3f1cff1cff3

def z1038 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x2b3cf80007fff801 0x159e7c0003fffc00

def z1039 : W := mkw 0x021d680005db7800 0x010eb40002edbc00 0x2a1c780006ff9800 0x150e3c00037fcc00

def z1040 : W := mkw 0x067fedd355db7800 0x033ff6e9aaedbc00 0xfffffee39ffff801 0xffffff71cffffc00

def z1041 : W := mkw 0x41028202c702c631 0xa081410163816318 0xdd438603e703e739 0x6ea1c301f381f39c

def z1042 : W := mkw 0x047ff5db78900000 0x023ffaedbc480000 0xf6fffffff8fc0000 0xfb7ffffffc7e0000

def z1043 : W := mkw 0x8009500c2845114a 0x4004a806142288a5 0xff5b411c7ee39fff 0xffada08e3f71cfff

def z1044 : W := mkw 0x041d70d938000000 0x020eb86c9c000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z1045 : W := mkw 0x80f687b647b647c1 0xc07b43db23db23e0 0xffff87ffe7ffe7c1 0xffffc3fff3fff3e0

def z1046 : W := mkw 0x00f407b007b00681 0x807a03d803d80340 0xbafc07fc07fc0001 0xdd7e03fe03fe0000

def z1047 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xa624f91c791c7ffe 0xd3127c8e3c8e3fff

def z1048 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xff63c703e703ff39 0x7fb1e381f381ff9c

def z1049 : W := mkw 0x007fe80000493800 0x003ff40000249c00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z1050 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xff67f91c7f1fffff 0xffb3fc8e3f8fffff

def z1051 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x00df3eff80000000 0x006f9f7fc0000000

def z1052 : W := mkw 0x81f687b647b647d1 0xc0fb43db23db23e8 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z1053 : W := mkw 0xa009584d384d394e 0x5004ac269c269ca7 0x2204781c181c18c6 0x91023c0e0c0e0c63

def z1054 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbadc06fc06fc04c1 0xdd6e037e037e0260

def z1055 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x6b5ff80006fff800 0x35affc00037ffc00

def z1056 : W := mkw 0x037fed0245db7a10 0x81bff68122edbd08 0xff7ff90067ffff39 0x7fbffc8033ffff9c

def z1057 : W := mkw 0xc0f687b487b6c7e1 0xe07b43da43db63f0 0xffff87ff87ffe7e1 0xffffc3ffc3fff3f0

def z1058 : W := mkw 0x80f407b407b407cb 0xc07a03da03da03e5 0xbafc07fc07fc07ff 0xdd7e03fe03fe03ff

def z1059 : W := mkw 0x410002008702c631 0xa080010043816318 0xdd638703e703e739 0x6eb1c381f381f39c

def z1060 : W := mkw 0x027fed4355db7800 0x013ff6a1aaedbc00 0xffffffe3fffff801 0xfffffff1fffffc00

def z1061 : W := mkw 0x027fed0245db7800 0x013ff68122edbc00 0x7b7ff90067fff801 0x3dbffc8033fffc00

def z1062 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xbefc87ffe7fc67f9 0xdf7e43fff3fe33fc

def z1063 : W := mkw 0x047ff5db78411000 0x023ffaedbc208800 0xf5fffffff8039800 0xfafffffffc01cc00

def z1064 : W := mkw 0x4000000080008020 0x2000000040004010 0xd5238103e103e739 0x6a91c081f081f39c

def z1065 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x2b5f780007fff801 0x15afbc0003fffc00

def z1066 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x2bdb46e39ee39ce7 0x95eda371cf71ce73

def z1067 : W := mkw 0x80f405b405b401c0 0x407a02da02da00e0 0xbafc07fc07fc00c1 0xdd7e03fe03fe0060

def z1068 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xfbff07fc07ff87c1 0xfdff83fe03ffc3e0

def z1069 : W := mkw 0x81f69d9e6d9e6b5a 0xc0fb4ecf36cf35ad 0x0024b91c611c6318 0x00125c8e308e318c

def z1070 : W := mkw 0x41028202c202c431 0x2081410161016218 0xdd638703e703e739 0x6eb1c381f381f39c

def z1071 : W := mkw 0x41028002c502c230 0xa081400162816118 0x45038003e103e338 0x2281c001f081f19c

def z1072 : W := mkw 0x0274080005db7800 0x013a040002edbc00 0x7b7cf80007fff801 0x3dbe7c0003fffc00

def z1073 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xb29c00fc00fc04c1 0xd94e007e007e0260

def z1074 : W := mkw 0x80f405b400b401c0 0x407a02da005a00e0 0xb2fc07fc01fc07c1 0xd97e03fe00fe03e0

def z1075 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xf767ff1ff91c7fff 0xfbb3ff8ffc8e3fff

def z1076 : W := mkw 0x81f407b647b407d1 0xc0fa03db23da03e8 0xbafc07fc67fc07d9 0xdd7e03fe33fe03ec

def z1077 : W := mkw 0x047ff5db7d435000 0x023ffaedbea1a800 0xffffffffffe3f801 0xfffffffffff1fc00

def z1078 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x8ad807fc07fc07c1 0xc56c03fe03fe03e0

def z1079 : W := mkw 0x047ff5db7d024000 0x023ffaedbe812000 0xf4fffffff9006000 0xfa7ffffffc803000

def z1080 : W := mkw 0xc0f407b487b487e1 0xe07a03da43da43f0 0xffff87ffe7ffe7f9 0xffffc3fff3fff3fc

def z1081 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xb0ffbfffe0000000 0xd87fdffff0000000

def z1082 : W := mkw 0x808007b407b407c1 0xc04003da03da03e0 0xbad807fc07fc07c1 0xdd6c03fe03fe03e0

def z1083 : W := mkw 0x41f687b2c7b2c6b1 0xa0fb43d963d96358 0xfffb87e3e7e3e7f9 0xfffdc3f1f3f1f3fc

def z1084 : W := mkw 0x047ff5db78411000 0x023ffaedbc208800 0xfcfffffffee38000 0xfe7fffffff71c000

def z1085 : W := mkw 0x040015db78000000 0x02000aedbc000000 0xc480fffff8000000 0xe2407ffffc000000

def z1086 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x8d430703e703e739 0x46a18381f381f39c

def z1087 : W := mkw 0xc1f407b487b487f1 0xe0fa03da43da43f8 0xbafc07fc07fc07f9 0xdd7e03fe03fe03fc

def z1088 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xa29c01fc00fc07c0 0xd14e00fe007e03e0

def z1089 : W := mkw 0x021fe80005db7800 0x010ff40002edbc00 0x6b1ff80007fff801 0x358ffc0003fffc00

def z1090 : W := mkw 0x41028002c002c030 0x2081400160016018 0x45038003e103e739 0x2281c001f081f39c

def z1091 : W := mkw 0x027fe84115db7800 0x013ff4208aedbc00 0x7bfff8e01ffff801 0xbdfffc700ffffc00

def z1092 : W := mkw 0xe48017fffa2487e5 0xf2400bfffd1243f2 0x848007fff80007e6 0xc24003fffc0003f3

def z1093 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x787ff80007ffe000 0x3c3ffc0003fff000

def z1094 : W := mkw 0x80f405b405b403c0 0xc07a02da02da01e0 0xb2bc01fc01fc07c1 0xd95e00fe00fe03e0

def z1095 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xaadc07fc06fc07c0 0xd56e03fe037e03e0

def z1096 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xff7cf91c7ffc7fff 0xffbe7c8e3ffe3fff

def z1097 : W := mkw 0x027fe00005d35000 0x013ff00002e9a800 0x7a7ff80007ff8001 0x3d3ffc0003ffc000

def z1098 : W := mkw 0x610bd84bf84bf83e 0x3085ec25fc25fc1f 0x4503f803f803f83e 0x2281fc01fc01fc1f

def z1099 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x7bdb46e39ee398c7 0xbdeda371cf71cc63

def z1100 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x597fb80007ffe001 0x2cbfdc0003fff000

def z1101 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x44fffffff8000000 0x227ffffffc000000

def z1102 : W := mkw 0x809407b402b407c1 0xc04a03da015a03e0 0xbadc07fc06fc07c1 0xdd6e03fe037e03e0

def z1103 : W := mkw 0x0000104938000000 0x000008249c000000 0xf4a4fffff8000000 0xfa527ffffc000000

def z1104 : W := mkw 0xc58017fffa2487f1 0xe2c00bfffd1243f8 0x848007fff80007f8 0xc24003fffc0003fc

def z1105 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ff8001ffff801 0xffbffc000ffffc00

def z1106 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xb2bc01fc00fc00c0 0xd95e00fe007e0060

def z1107 : W := mkw 0x047ff5db7800000a 0x023ffaedbc000005 0xf4fffffff800003e 0xfa7ffffffc00001f

def z1108 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x09638703e703e739 0x04b1c381f381f39c

def z1109 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf4fffffff9006318 0xfa7ffffffc80318c

def z1110 : W := mkw 0xe40017fffa2485ef 0x72000bfffd1242f7 0x848007fff80007fe 0xc24003fffc0003ff

def z1111 : W := mkw 0x067fed9245db7800 0x033ff6c922edbc00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z1112 : W := mkw 0xe000122caa2485ef 0x70000916551242f7 0x8400011c780007fe 0xc200008e3c0003ff

def z1113 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x70fffeff98000000 0xb87fff7fcc000000

def z1114 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7f7ff8001ffff827 0x3fbffc000ffffc13

def z1115 : W := mkw 0x41028002c002c030 0x2081400160016018 0x45238103e103e338 0x2291c081f081f19c

def z1116 : W := mkw 0x41628502c502c230 0xa0b1428162816118 0xd5638703e103e338 0x6ab1c381f081f19c

def z1117 : W := mkw 0x041d70d938000000 0x020eb86c9c000000 0x20df7eff98000000 0x906fbf7fcc000000

def z1118 : W := mkw 0x040015db78000000 0x02000aedbc000000 0x84a4bffff8000000 0xc2525ffffc000000

def z1119 : W := mkw 0x027fe80000d93800 0x013ff400006c9c00 0x7b7ff80006ff9801 0x3dbffc00037fcc00

def z1120 : W := mkw 0x047ff5db7dd11000 0x023ffaedbee88800 0xffffffffffff9801 0xffffffffffffcc00

def z1121 : W := mkw 0x0014009000900000 0x000a004800480000 0x229c00fc00fc0000 0x914e007e007e0000

def z1122 : W := mkw 0x80f407b402b405c1 0x407a03da015a02e0 0xbafc07fc06fc04c1 0xdd7e03fe037e0260

def z1123 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbafc47fc1ffc1fc7 0xdd7e23fe0ffe0fe3

def z1124 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xddff87ffe7ffe739 0x6effc3fff3fff39c

def z1125 : W := mkw 0x027fed9005db7800 0x013ff6c802edbc00 0x7bfffee007fff801 0x3dffff7003fffc00

def z1126 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0xf7bc81fc61fc67f9 0xfbde40fe30fe33fc

def z1127 : W := mkw 0x007fe59240000000 0x003ff2c920000000 0xf4ffffffe0000000 0xfa7ffffff0000000

def z1128 : W := mkw 0x007fe5d110000000 0x003ff2e888000000 0xf4ffffff98000000 0xfa7fffffcc000000

def z1129 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x2afc07fc07fc03c0 0x957e03fe03fe01e0

def z1130 : W := mkw 0x047ff5db7d000200 0x823ffaedbe800100 0xf4fffffff9000300 0xfa7ffffffc800180

def z1131 : W := mkw 0xc0f407b487b487e1 0xe07a03da43da43f0 0xbefc07ff87fc07e1 0xdf7e03ffc3fe03f0

def z1132 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x8c638703e703e738 0x4631c381f381f39c

def z1133 : W := mkw 0x0009480000493800 0x0004a40000249c00 0x7b5f780006ff9801 0x3dafbc00037fcc00

def z1134 : W := mkw 0x8074022407b405c1 0x403a011203da02e0 0xbafc07fc07fc07c1 0xdd7e03fe03fe03e0

def z1135 : W := mkw 0x80f4059405940340 0xc07a02ca02ca01a0 0xbafc07fc07fc0301 0xdd7e03fe03fe0180

def z1136 : W := mkw 0x60000a619228aca5 0x30000530c9145652 0xf7a4fee3991c7ce7 0xfbd27f71cc8e3e73

def z1137 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x4fdb46e39ee39ce7 0x27eda371cf71ce73

def z1138 : W := mkw 0xc18017beea2487fb 0xe0c00bdf751243fd 0x848007fff80007fe 0xc24003fffc0003ff

def z1139 : W := mkw 0x0209680005db7800 0x0104b40002edbc00 0x0b00780007fff801 0x05803c0003fffc00

def z1140 : W := mkw 0x41628502c002c030 0x20b1428160016018 0xd5638703e103e739 0x6ab1c381f081f39c

def z1141 : W := mkw 0x4060070087008621 0xa030038043804310 0xdd638703e703e739 0x6eb1c381f381f39c

def z1142 : W := mkw 0x067ff5db7dd35000 0x033ffaedbee9a800 0xfffffffffee39801 0xffffffffff71cc00

def z1143 : W := mkw 0xc1f407b6c7b6c7f1 0xe0fa03db63db63f8 0xbffc07ffe7ffe7f9 0xdffe03fff3fff3fc

def z1144 : W := mkw 0xc3800a2487fffff1 0xe1c0051243fffff8 0x0b00000007fffff9 0x0580000003fffffc

def z1145 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xffdb46e39fe3ffff 0xffeda371cff1ffff

def z1146 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0x8fdb06e39ee39ce7 0xc7ed8371cf71ce73

def z1147 : W := mkw 0xe2000a2487fffdef 0x7100051243fffef7 0x0b00000007ffffff 0x0580000003ffffff

def z1148 : W := mkw 0x0009404110411000 0x0004a02088208800 0xffdb46e39ee39ce7 0xffeda371cf71ce73

def z1149 : W := mkw 0x41f687b2c7b2c6b1 0xa0fb43d963d96358 0xfdff87ffe7e3e739 0xfeffc3fff3f1f39c

def z1150 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xfdfb87e3e703e739 0xfefdc3f1f381f39c

def z1151 : W := mkw 0x40628702c2008421 0x2031438161004210 0xdd638703e703e739 0x6eb1c381f381f39c

def z1152 : W := mkw 0x006bc800054b7800 0x0035e40002a5bc00 0x7b7ff80007fff801 0x3dbffc0003fffc00

def z1153 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xfeff87ffe7ff87c1 0xff7fc3fff3ffc3e0

def z1154 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x3a7f780007ff9801 0x1d3fbc0003ffcc00

def z1155 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ff90067fff801 0x7fbffc8033fffc00

def z1156 : W := mkw 0x200958493849380e 0x1004ac249c249c07 0x4500f8007800783e 0x22807c003c003c1f

def z1157 : W := mkw 0x027fe80245db7800 0x013ff40122edbc00 0x7f7ff803e7fff801 0x3fbffc01f3fffc00

def z1158 : W := mkw 0x037fe80005db7a10 0x81bff40002edbd08 0x7b7ff80007fffb19 0x3dbffc0003fffd8c

def z1159 : W := mkw 0x027fe84115db7800 0x013ff4208aedbc00 0x7f7ff8039ffff801 0x3fbffc01cffffc00

def z1160 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x08dc06fc06fc0000 0x046e037e037e0000

def z1161 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xffdbc6e3fee3fcff 0xffede371ff71fe7f

def z1162 : W := mkw 0x80000024002401c0 0x40000012001200e0 0xb2bc01fc01fc07c1 0xd95e00fe00fe03e0

def z1163 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x4d438603e703e739 0x26a1c301f381f39c

def z1164 : W := mkw 0x0009504938000000 0x0004a8249c000000 0xf4df7eff98000000 0xfa6fbf7fcc000000

def z1165 : W := mkw 0x067fedd355db7800 0x033ff6e9aaedbc00 0xfbffffff87fff801 0xfdffffffc3fffc00

def z1166 : W := mkw 0x8000180c280c294a 0x40000c06140614a5 0xc524f91c791c7ffe 0xe2927c8e3c8e3fff

def z1167 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xfbfffee007fff801 0xfdffff7003fffc00

def z1168 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7b7ff80007ffff39 0x3dbffc0003ffff9c

def z1169 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xfb7ff80007fffcc1 0xfdbffc0003fffe60

def z1170 : W := mkw 0x040bf04b78000000 0x0205f825bc000000 0xf4fffffff8000000 0xfa7ffffffc000000

def z1171 : W := mkw 0x41768702c792c631 0xa0bb438163c96318 0xdd678703e71fe739 0x6eb3c381f38ff39c

def z1172 : W := mkw 0xc0f687b6c7b487e1 0xe07b43db63da43f0 0xffff87ffe7ff87e1 0xffffc3fff3ffc3f0

def z1173 : W := mkw 0x067ff5db7dd35000 0x033ffaedbee9a800 0xfeffffffffff8001 0xff7fffffffffc000

def z1174 : W := mkw 0x027fe84115db7800 0x013ff4208aedbc00 0xfffffee39ffffce7 0xffffff71cffffe73

def z1175 : W := mkw 0x066bfd4b7d4b7800 0x0335fea5bea5bc00 0xdd63ff03ff03f801 0x6eb1ff81ff81fc00

def z1176 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7b7ff80007fffce7 0x3dbffc0003fffe73

def z1177 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xdd63c703ff03ff3f 0x6eb1e381ff81ff9f

def z1178 : W := mkw 0x80f687b407b647c1 0xc07b43da03db23e0 0xbafc87fc07fc67c1 0xdd7e43fe03fe33e0

def z1179 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xff7b8703e7e3e739 0x7fbdc381f3f1f39c

def z1180 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfedb46e39ee398c6 0xff6da371cf71cc63

def z1181 : W := mkw 0x027d680005d93800 0x013eb40002ec9c00 0x7b7f780007ff9801 0x3dbfbc0003ffcc00

def z1182 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf5fffffff8006038 0xfafffffffc00301c

def z1183 : W := mkw 0x067fedd355db7800 0x033ff6e9aaedbc00 0xffffffe3e7fff801 0x7ffffff1f3fffc00

def z1184 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfffffee39ee39ce7 0xffffff71cf71ce73

def z1185 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0x4d638703e703e338 0x26b1c381f381f19c

def z1186 : W := mkw 0x41768792c702c631 0xa0bb43c963816318 0xdd67871fe703e739 0x6eb3c38ff381f39c

def z1187 : W := mkw 0x41628702c702c631 0xa0b1438163816318 0xff638703e703e7f9 0xffb1c381f381f3fc

def z1188 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0xbeff07ffe7ff87f9 0xdf7f83fff3ffc3fc

def z1189 : W := mkw 0x809400b405b403c0 0xc04a005a02da01e0 0x229c00fc01fc03c0 0x914e007e00fe01e0

def z1190 : W := mkw 0xc0f407b487b487e1 0xe07a03da43da43f0 0xbaff07ff87ff87c1 0xdd7f83ffc3ffc3e0

def z1191 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0x7b5f780006ff9801 0x3dafbc00037fcc00

def z1192 : W := mkw 0x067ff5db7dd35000 0x033ffaedbee9a800 0xfdffffffffe3e001 0xfefffffffff1f000

def z1193 : W := mkw 0xe000126dba2485ef 0x70000936dd1242f7 0x848006ff980004e6 0xc240037fcc000273

def z1194 : W := mkw 0x80f687b407b647c1 0xc07b43da03db23e0 0xffff87fc67ffe7f9 0xffffc3fe33fff3fc

def z1195 : W := mkw 0x80f400b405b401c0 0x407a005a02da00e0 0x22bc00fc01fc00c0 0x915e007e00fe0060

def z1196 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x2adc06fc07fc07c1 0x956e037e03fe03e0

def z1197 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x0afc07fc07fc07c1 0x057e03fe03fe03e0

def z1198 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbafc87fc67fc67d9 0xdd7e43fe33fe33ec

def z1199 : W := mkw 0x809400b400b401c0 0x404a005a005a00e0 0x32bc00fc01fc00c1 0x995e007e00fe0060

def z1200 : W := mkw 0x0076859245924000 0x003b42c922c92000 0xffff87ffe7ffe001 0xffffc3fff3fff000

def z1201 : W := mkw 0x020be80005db7800 0x0105f40002edbc00 0x7b27f80007fff801 0x3d93fc0003fffc00

def z1202 : W := mkw 0x040015db78000000 0x02000aedbc000000 0xa4847ffff8000000 0xd2423ffffc000000

def z1203 : W := mkw 0x809402b402b405c1 0x404a015a015a02e0 0x2adc06fc06fc00c0 0x956e037e037e0060

def z1204 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0x3afc06fc07fc00c1 0x9d7e037e03fe0060

def z1205 : W := mkw 0x41628502c502c230 0xa0b1428162816118 0x5d638103e703e339 0x2eb1c081f381f19c

def z1206 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0x20fffffff8000000 0x907ffffffc000000

def z1207 : W := mkw 0x047ff5db78411000 0x023ffaedbc208800 0xf6fffffff8e01800 0xfb7ffffffc700c00

def z1208 : W := mkw 0x41028702c202c631 0xa081438161016318 0xdd438703e603e739 0x6ea1c381f301f39c

def z1209 : W := mkw 0x0476b5db78000000 0x023b5aedbc000000 0x00a4bfffe0000000 0x00525ffff0000000

def z1210 : W := mkw 0x027fe80005db7800 0x013ff40002edbc00 0xff7ffe0387fff801 0x7fbfff01c3fffc00

def z1211 : W := mkw 0x80f407b407b407c1 0xc07a03da03da03e0 0xbefc07fc1ffc07e7 0xdf7e03fe0ffe03f3

def z1212 : W := mkw 0x41768792c702c631 0xa0bb43c963816318 0xddfb87e3e703e739 0x6efdc3f1f381f39c

def z1213 : W := mkw 0x027fe80005db780a 0x013ff40002edbc05 0x7b7ff80007fff83f 0x3dbffc0003fffc1f

def z1214 : W := mkw 0x60094261926194a5 0x3004a130c930ca52 0xfffbc6e39fe3fce7 0xfffde371cff1fe73

def z1215 : W := mkw 0x047ff5db78000000 0x023ffaedbc000000 0xf6fffffff80004c1 0xfb7ffffffc000260

def z1216 : W := mkw 0x0202a80005db7800 0x0101540002edbc00 0x0b00b80007fff801 0x05805c0003fffc00

def z1217 : W := mkw 0xc1f407b487b6c7f1 0xe0fa03da43db63f8 0xffff07ff87ffe7f9 0xffff83ffc3fff3fc

def z1218 : W := mkw 0x809402b407b407c1 0xc04a015a03da03e0 0x2a9c00fc06fc00c0 0x954e007e037e0060

def z1219 : W := mkw 0x037fe80245db7810 0x01bff40122edbc08 0x7b7ff80067fff819 0x3dbffc0033fffc0c

def z1220 : W := mkw 0xc1f687b6c7b6c7f1 0xe0fb43db63db63f8 0x08ff87ffe7ffe318 0x047fc3fff3fff18c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z9,z10])],[(0,[z1,z2,z3,z4,z5,z8,z11])],[(0,[z12,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z13]),(0,[z14,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z16,z5,z8])],[(0,[z0,z2,z3,z4,z17,z5,z8]),(0,[z2,z3,z18,z4,z17,z5,z8]),(0,[z19,z1,z2,z20,z4,z5,z8]),(0,[z21,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z8,z22]),(0,[z1,z23,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z5,z8]),(0,[z1,z25,z2,z3,z26,z5,z8]),(0,[z27,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z28,z3,z4,z5,z8])],[(0,[z29,z1,z2,z3,z4,z5,z8]),(0,[z30,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z31,z5,z8]),(0,[z32,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z33]),(0,[z1,z2,z3,z4,z34,z5,z8]),(1,[z1,z35,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z36]),(0,[z1,z2,z3,z4,z5,z8,z37]),(0,[z1,z2,z3,z4,z38,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z39])],[(0,[z1,z2,z3,z4,z5,z40,z8]),(1,[z1,z2,z41,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z43,z1,z44,z3,z4,z5,z8])],[(0,[z1,z45,z25,z3,z4,z5,z8]),(0,[z1,z2,z3,z46,z4,z5,z8]),(0,[z47,z1,z2,z3,z4,z5,z8]),(0,[z48,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z45,z3,z49,z4,z5,z8]),(0,[z1,z2,z50,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z5,z8]),(0,[z1,z2,z3,z52,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z8,z54]),(0,[z1,z2,z55,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z9,z8]),(0,[z56,z1,z2,z3,z4,z5,z8])],[(0,[z0,z57,z2,z3,z4,z5,z8]),(0,[z58,z1,z59,z3,z4,z5,z8]),(0,[z60,z1,z2,z49,z4,z5,z8]),(0,[z60,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z36])],[(0,[z58,z1,z2,z3,z4,z5,z8]),(0,[z61,z1,z2,z3,z4,z5,z8]),(0,[z62,z63,z1,z2,z3,z4,z5]),(0,[z64,z1,z65,z2,z3,z4,z5]),(0,[z1,z2,z3,z66,z4,z5,z6]),(0,[z1,z2,z3,z67,z4,z8,z68])],[(0,[z1,z2,z3,z4,z5,z69,z8]),(0,[z70,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z71]),(0,[z1,z72,z2,z3,z4,z5,z8])],[(0,[z73,z1,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z75]),(0,[z1,z76,z2,z3,z4,z5,z8]),(0,[z77,z1,z2,z78,z4,z5,z8])],[(0,[z1,z79,z2,z3,z4,z5,z8]),(0,[z80,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z81,z3,z4,z5,z8]),(0,[z1,z2,z82,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z83]),(0,[z84,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z9,z8,z85])],[(0,[z1,z2,z3,z4,z5,z86,z8]),(0,[z87,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z88]),(1,[z1,z89,z90,z4,z5,z8]),(0,[z1,z2,z90,z3,z4,z5,z91]),(0,[z1,z2,z3,z92,z4,z5,z8]),(1,[z93,z2,z3,z4,z5,z8])]],
   [[(0,[z94,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z95,z4,z5,z8]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z44,z2,z3,z4,z5,z8]),(0,[z97,z1,z2,z3,z4,z98,z8])],[],[(0,[z99,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z100,z8]),(0,[z1,z101,z2,z3,z4,z5,z8]),(0,[z102,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z74,z3,z4,z5,z103]),(0,[z104,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z105]),(0,[z1,z106,z2,z3,z4,z5,z8]),(1,[z1,z107,z3,z4,z5,z8]),(1,[z53,z1,z2,z4,z5,z103])],[(0,[z1,z2,z3,z4,z5,z108,z8]),(0,[z12,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z5,z8,z109]),(0,[z110,z1,z2,z3,z4,z5,z8])],[(0,[z0,z64,z2,z3,z4,z5,z8]),(0,[z1,z111,z2,z3,z4,z5,z8]),(0,[z1,z2,z112,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z113]),(0,[z114,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z115,z4,z5,z8])],[(0,[z1,z89,z2,z49,z4,z5,z8]),(0,[z1,z89,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z8]),(0,[z1,z2,z3,z4,z5,z8,z116]),(0,[z1,z2,z3,z4,z98,z5,z6])],[(0,[z1,z2,z3,z117,z4,z5,z8]),(0,[z118,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z119]),(0,[z120,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z121,z3,z4,z5,z8]),(0,[z122,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z4,z124,z5,z8])],[(1,[z1,z2,z3,z4,z5,z8]),(0,[z125,z1,z2,z3,z4,z5,z8]),(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z50,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z127,z5,z8]),(0,[z128,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z129,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z6])],[(0,[z130,z1,z2,z3,z4,z5,z8]),(0,[z131,z1,z2,z3,z4,z132,z8]),(0,[z133,z1,z2,z3,z4,z5,z8]),(0,[z134,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z135,z3,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z136,z1,z2,z3,z4,z5,z8])],[(0,[z1,z3,z137,z4,z26,z5,z8]),(0,[z53,z1,z2,z135,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z103]),(0,[z1,z2,z3,z4,z5,z10,z85]),(0,[z1,z2,z3,z4,z5,z8,z10])],[(0,[z138,z1,z2,z3,z4,z5,z8]),(0,[z63,z1,z2,z3,z4,z5,z103]),(0,[z139,z1,z2,z3,z4,z5,z8])],[(0,[z140,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z141]),(0,[z1,z2,z3,z142,z4,z5,z6]),(0,[z1,z2,z143,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z144,z5,z8]),(0,[z58,z2,z3,z4,z132,z5,z8]),(0,[z1,z145,z2,z3,z4,z5,z8])],[(0,[z146,z1,z2,z3,z4,z5,z8]),(0,[z147,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z148]),(0,[z149,z1,z2,z3,z4,z8,z10])]],
   [[(0,[z150,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z151,z4,z5,z8]),(1,[z1,z2,z50,z4,z5,z103]),(0,[z60,z152,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z153,z8]),(0,[z53,z154,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z4,z155,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z156])],[(0,[z1,z2,z157,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z158,z8]),(0,[z1,z2,z3,z4,z5,z159,z8]),(0,[z1,z2,z3,z4,z5,z8,z160]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z8,z68])],[(0,[z1,z2,z161,z3,z4,z5,z8]),(0,[z131,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z49,z4,z5,z8]),(0,[z162,z1,z89,z3,z4,z5,z8]),(0,[z19,z1,z2,z135,z4,z5,z8]),(0,[z163,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z97,z149,z1,z2,z3,z4,z8])],[(0,[z1,z164,z2,z3,z4,z5,z8]),(0,[z130,z1,z2,z3,z18,z5,z8]),(0,[z1,z2,z165,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z166,z103]),(0,[z167,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z6,z8,z103]),(0,[z1,z2,z168,z3,z4,z5,z8])],[(0,[z1,z169,z2,z3,z4,z5,z8]),(1,[z1,z3,z4,z5,z8,z170])],[(0,[z1,z2,z3,z171,z4,z5,z8]),(0,[z172,z1,z2,z3,z4,z5,z103])],[(0,[z173,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z174,z4,z5,z8,z103]),(0,[z1,z2,z3,z4,z175,z5,z8]),(0,[z64,z1,z2,z3,z4,z5,z103]),(0,[z1,z176,z2,z3,z4,z5,z8]),(0,[z1,z2,z177,z3,z4,z5,z8])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z174,z4,z5,z8]),(0,[z1,z2,z3,z137,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z178,z6])]],
   [[(0,[z1,z25,z2,z3,z137,z5,z8]),(0,[z1,z2,z179,z3,z4,z5,z103]),(0,[z1,z180,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z181,z5,z68]),(0,[z1,z2,z3,z4,z5,z8,z182])],[(0,[z1,z2,z3,z4,z183,z5,z8]),(0,[z184,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z135,z3,z5,z8,z68]),(0,[z185,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z67,z4,z5,z6]),(0,[z186,z1,z2,z3,z4,z5,z8])],[(0,[z1,z187,z2,z3,z4,z5,z8]),(0,[z43,z1,z2,z3,z67,z5,z8]),(0,[z188,z1,z2,z3,z4,z5,z8])],[(0,[z62,z1,z2,z189,z4,z5,z8]),(1,[z60,z1,z49,z4,z5,z8]),(0,[z190,z1,z2,z3,z4,z5,z8]),(1,[z19,z1,z2,z4,z5,z103]),(0,[z77,z1,z2,z3,z4,z98,z5])],[(0,[z1,z191,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z192,z8]),(0,[z1,z2,z3,z4,z5,z6,z54]),(1,[z102,z2,z3,z4,z5,z8]),(1,[z1,z2,z193,z4,z5,z8])],[(0,[z194,z1,z2,z3,z4,z5,z8]),(0,[z62,z64,z2,z3,z4,z5,z8]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z195,z5,z8,z68])],[(0,[z1,z3,z49,z4,z5,z8,z196]),(0,[z1,z2,z3,z197,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z198]),(0,[z1,z191,z2,z3,z4,z8,z196]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z63,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z199]),(0,[z200,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z201,z8]),(1,[z202,z1,z2,z3,z4,z5]),(1,[z1,z2,z203,z4,z5,z8]),(0,[z204,z1,z2,z3,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z205])],[(0,[z1,z2,z3,z4,z206,z5,z8]),(0,[z1,z2,z207,z3,z4,z5,z8]),(0,[z1,z208,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z209])],[(0,[z45,z2,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z210,z5,z8]),(0,[z12,z2,z3,z174,z4,z5,z8]),(0,[z1,z2,z211,z3,z4,z5,z8]),(0,[z1,z2,z90,z4,z5,z8,z103]),(0,[z162,z176,z2,z3,z4,z5,z8]),(0,[z162,z1,z2,z3,z26,z5,z8]),(0,[z43,z212,z2,z3,z4,z5,z8])],[(1,[z1,z213,z3,z4,z5,z8]),(0,[z1,z2,z3,z214,z4,z5,z8]),(0,[z215,z1,z2,z3,z4,z5,z8])],[(0,[z131,z1,z2,z3,z4,z8,z13]),(0,[z216,z1,z2,z3,z4,z5,z8]),(1,[z1,z191,z3,z4,z217,z8]),(0,[z218,z1,z2,z3,z4,z5,z8])],[(0,[z1,z45,z2,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z5,z8,z105]),(0,[z1,z2,z3,z4,z5,z8,z219]),(0,[z1,z2,z3,z4,z5,z8,z220]),(0,[z1,z2,z3,z4,z132,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z8]),(0,[z1,z2,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z222]),(0,[z1,z2,z3,z4,z5,z223,z8]),(0,[z1,z2,z224,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z225,z5,z8]),(0,[z226,z1,z2,z3,z4,z5,z8])],[(0,[z1,z227,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z18,z4,z5,z6]),(0,[z63,z48,z2,z3,z4,z5,z8]),(0,[z1,z2,z107,z3,z4,z5,z8])],[(0,[z1,z2,z228,z3,z4,z5,z8]),(0,[z1,z65,z2,z3,z4,z5,z103]),(0,[z1,z2,z179,z4,z155,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z229])]],
   [[(0,[z130,z2,z3,z4,z5,z8,z13]),(1,[z64,z2,z3,z4,z5,z230]),(0,[z231,z1,z2,z3,z4,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z233,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z234]),(0,[z1,z235,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z103]),(0,[z149,z1,z2,z3,z4,z98,z5]),(1,[z1,z2,z3,z4,z98,z10])],[(0,[z1,z191,z2,z3,z4,z217,z8]),(0,[z1,z2,z20,z3,z4,z5,z8]),(0,[z1,z2,z135,z20,z3,z5,z8]),(1,[z19,z1,z2,z135,z5,z8])],[(0,[z1,z2,z59,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z230,z6]),(0,[z1,z2,z3,z4,z236,z5,z8]),(0,[z237,z1,z2,z3,z4,z5,z103])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z0,z130,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z238]),(0,[z1,z2,z3,z4,z5,z8,z239]),(0,[z1,z2,z240,z3,z4,z5,z8])],[(0,[z1,z2,z241,z3,z4,z5,z8]),(0,[z57,z2,z3,z4,z5,z8,z13]),(0,[z152,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z242,z3,z4,z5,z8]),(1,[z1,z101,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z243]),(0,[z1,z2,z3,z4,z5,z8,z244]),(0,[z1,z245,z2,z3,z4,z5,z8])],[(0,[z73,z1,z2,z3,z4,z5,z103]),(0,[z1,z74,z3,z4,z217,z5,z8]),(0,[z2,z3,z4,z5,z230,z8,z105]),(0,[z162,z246,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z247,z4,z5,z8]),(1,[z1,z2,z20,z124,z5,z8])],[(0,[z1,z2,z3,z248,z4,z5,z8]),(0,[z1,z2,z3,z4,z217,z5,z103]),(0,[z249,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z78,z4,z5,z8])]],
   [[(0,[z2,z74,z3,z4,z132,z5,z8]),(0,[z202,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z250]),(0,[z60,z111,z2,z3,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z6])],[(0,[z251,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z67,z124,z5,z8])],[(0,[z202,z1,z2,z74,z3,z4,z5]),(0,[z252,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z253,z5,z8]),(0,[z191,z2,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z255]),(0,[z1,z2,z3,z4,z5,z8,z256])],[(0,[z1,z2,z3,z257,z4,z5,z8])],[(0,[z1,z2,z3,z258,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z5,z103]),(0,[z1,z2,z3,z4,z5,z8,z259])],[(0,[z1,z2,z3,z4,z5,z8,z260]),(0,[z261,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z262,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z263])],[(0,[z264,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z265]),(0,[z1,z2,z266,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z196,z103]),(0,[z1,z2,z3,z4,z5,z8,z267]),(0,[z268,z1,z2,z3,z4,z5,z8])],[(0,[z1,z269,z2,z3,z4,z5,z8]),(0,[z1,z2,z90,z3,z4,z5,z8]),(0,[z270,z1,z191,z3,z4,z5,z8]),(0,[z271,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z272,z5,z8])]],
   [[(0,[z1,z65,z74,z3,z4,z5,z8]),(0,[z162,z1,z25,z3,z4,z5,z8]),(0,[z1,z25,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z273,z5,z8]),(0,[z1,z2,z3,z4,z124,z5,z8]),(0,[z1,z2,z3,z4,z195,z5,z6])],[(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z57,z1,z2,z50,z4,z5,z8]),(0,[z162,z1,z3,z49,z4,z5,z8]),(0,[z1,z191,z3,z49,z4,z5,z8]),(0,[z185,z1,z2,z3,z4,z5,z103]),(0,[z77,z1,z2,z3,z4,z5,z103]),(0,[z77,z1,z2,z3,z4,z5,z85]),(0,[z97,z1,z2,z3,z142,z4,z5])],[(0,[z274,z1,z2,z3,z4,z5,z8]),(0,[z1,z3,z49,z137,z4,z5,z8]),(0,[z1,z2,z3,z4,z275,z5,z8])],[(0,[z276,z1,z2,z3,z4,z5,z8]),(0,[z1,z277,z2,z3,z4,z5,z8])],[(0,[z64,z2,z74,z3,z4,z5,z8]),(0,[z278,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z279,z4,z5,z8]),(0,[z280,z1,z2,z3,z4,z5,z8]),(0,[z21,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z281]),(0,[z282,z1,z2,z3,z4,z5,z8]),(0,[z283,z1,z2,z3,z4,z5,z8])],[(0,[z1,z284,z2,z3,z4,z5,z8]),(0,[z62,z2,z3,z4,z5,z8,z105]),(0,[z1,z2,z285,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z286]),(0,[z1,z2,z4,z155,z5,z8,z103]),(0,[z1,z2,z3,z4,z287,z5,z8])],[(0,[z2,z50,z3,z174,z4,z5,z8]),(0,[z53,z1,z2,z4,z5,z8,z103]),(0,[z1,z2,z3,z4,z288,z5,z8])],[]],
   [[(0,[z289,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z290]),(0,[z1,z2,z291,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z155,z5,z8])],[(0,[z1,z2,z50,z3,z4,z5,z8]),(0,[z2,z3,z4,z17,z5,z8,z13]),(0,[z62,z1,z2,z3,z4,z5,z105]),(0,[z1,z2,z3,z292,z4,z5,z8]),(1,[z1,z2,z3,z293,z5,z8]),(0,[z1,z2,z3,z4,z294,z5,z8])],[(0,[z1,z2,z295,z3,z4,z5,z8]),(0,[z60,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z49,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z103]),(0,[z1,z2,z3,z3,z4,z5,z6])],[(0,[z1,z2,z3,z296,z4,z5,z8]),(0,[z1,z2,z297,z3,z4,z5,z8]),(0,[z270,z1,z2,z3,z4,z5,z103]),(0,[z298,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z299,z8]),(0,[z19,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z66,z4,z5,z8]),(1,[z1,z44,z3,z4,z5,z8]),(0,[z43,z1,z2,z143,z4,z5,z8])],[(0,[z1,z2,z3,z4,z300,z5,z8]),(0,[z1,z2,z3,z4,z5,z54,z103]),(0,[z301,z1,z2,z3,z4,z5,z8]),(0,[z77,z97,z1,z2,z3,z4,z5])],[(0,[z1,z45,z2,z3,z4,z5,z103]),(0,[z302,z1,z2,z3,z4,z5,z8]),(0,[z19,z1,z2,z4,z5,z8,z103]),(0,[z303,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z304,z3,z4,z5,z8]),(0,[z305,z1,z2,z3,z4,z5,z8]),(0,[z282,z1,z3,z4,z5,z8,z68]),(0,[z1,z2,z3,z4,z306,z5,z8]),(0,[z1,z2,z307,z3,z4,z5,z8]),(0,[z1,z2,z3,z308,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z309]),(0,[z1,z2,z3,z4,z5,z6,z13]),(0,[z310,z1,z2,z3,z4,z5,z8]),(0,[z162,z1,z2,z3,z137,z5,z8]),(0,[z1,z2,z3,z142,z4,z5,z9])],[(0,[z0,z45,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z174,z4,z5,z8]),(0,[z1,z311,z2,z3,z4,z5,z8]),(0,[z312,z1,z2,z3,z4,z5,z8]),(0,[z313,z1,z2,z3,z4,z5,z8]),(0,[z249,z1,z2,z123,z4,z5,z8]),(0,[z149,z1,z2,z3,z4,z5,z103]),(0,[z149,z1,z2,z3,z4,z5,z85]),(0,[z1,z2,z3,z4,z98,z5,z10])]],
   [[(1,[z270,z1,z3,z4,z8,z196]),(0,[z1,z65,z3,z4,z5,z166,z8]),(1,[z1,z2,z4,z5,z6,z103])],[(1,[z0,z45,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z314]),(0,[z1,z2,z315,z3,z4,z5,z8]),(0,[z12,z2,z3,z4,z132,z5,z8]),(0,[z64,z1,z2,z3,z4,z5,z230]),(0,[z316,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z317]),(0,[z1,z2,z3,z4,z5,z6,z33]),(0,[z1,z2,z3,z4,z318,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z319]),(1,[z303,z2,z3,z4,z5,z8]),(0,[z43,z1,z2,z320,z4,z5,z8]),(0,[z97,z1,z2,z3,z4,z5,z10])],[(1,[z1,z321,z3,z4,z5,z8]),(0,[z1,z2,z179,z3,z4,z5,z322]),(1,[z249,z1,z2,z4,z5,z103]),(1,[z1,z2,z323,z4,z5,z8])],[(0,[z1,z2,z3,z324,z4,z5,z8]),(0,[z270,z1,z3,z4,z5,z8,z196]),(0,[z325,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z155,z5,z8,z54]),(0,[z1,z2,z3,z4,z5,z8,z326])],[(0,[z1,z2,z327,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z328]),(0,[z1,z2,z3,z329,z4,z5,z8]),(0,[z53,z1,z107,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z330,z8])],[(0,[z1,z2,z3,z4,z331,z5,z8]),(0,[z1,z3,z4,z217,z5,z8,z196]),(0,[z1,z2,z3,z4,z332,z5,z8])],[(0,[z1,z2,z327,z74,z3,z4,z5]),(0,[z2,z3,z174,z4,z5,z8,z13]),(0,[z1,z89,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z333,z8]),(0,[z1,z2,z90,z123,z4,z5,z8]),(0,[z334,z1,z2,z3,z4,z5,z8]),(0,[z335,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z98,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z336]),(1,[z337,z2,z3,z4,z5,z8]),(0,[z19,z93,z2,z3,z4,z5,z8]),(0,[z338,z1,z2,z3,z4,z5,z103])],[(0,[z62,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z339,z4,z5,z8])],[(0,[z1,z2,z3,z4,z340,z5,z8]),(0,[z57,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z129,z5,z8]),(0,[z1,z2,z3,z341,z4,z5,z8])],[(0,[z1,z2,z3,z342,z4,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z8])],[(0,[z73,z2,z74,z3,z4,z5,z8]),(0,[z270,z1,z74,z3,z4,z5,z8]),(0,[z1,z2,z50,z3,z4,z5,z343]),(0,[z1,z2,z3,z4,z5,z344,z8]),(0,[z1,z2,z203,z3,z4,z5,z8]),(0,[z345,z1,z2,z3,z4,z5,z8]),(0,[z19,z1,z2,z4,z5,z8,z54]),(0,[z1,z2,z3,z4,z5,z119,z8])],[(0,[z73,z1,z45,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z346]),(0,[z12,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z189,z4,z5,z8]),(0,[z63,z1,z2,z3,z4,z5,z166]),(0,[z1,z2,z3,z4,z16,z5,z103])],[(0,[z347,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z8]),(0,[z1,z2,z3,z142,z4,z5,z8])],[(0,[z1,z74,z3,z4,z5,z8,z33]),(0,[z1,z2,z74,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z105]),(1,[z1,z2,z179,z4,z155,z8])]],
   [[(0,[z349,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z350,z5,z8]),(0,[z60,z1,z3,z49,z4,z5,z8]),(0,[z1,z2,z3,z4,z124,z5,z103]),(0,[z1,z2,z3,z4,z5,z8,z351]),(1,[z282,z1,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z8,z267,z68]),(0,[z1,z2,z3,z4,z5,z352,z8])],[(1,[z172,z2,z174,z4,z5,z8]),(0,[z1,z2,z50,z123,z4,z5,z8]),(0,[z353,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z354,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z355,z8]),(0,[z1,z356,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z357,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z358]),(0,[z1,z89,z90,z3,z4,z5,z8]),(0,[z19,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z179,z3,z4,z8,z54]),(0,[z1,z2,z3,z4,z5,z8,z359])],[(0,[z360,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z361,z5,z8]),(0,[z1,z362,z2,z3,z4,z5,z8]),(0,[z1,z2,z35,z3,z4,z5,z8]),(0,[z1,z2,z123,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z9,z103]),(1,[z97,z149,z1,z2,z3,z4])],[(0,[z1,z2,z363,z3,z4,z5,z8]),(0,[z1,z2,z3,z320,z4,z5,z8]),(0,[z1,z2,z3,z364,z4,z5,z8])],[(0,[z365,z1,z2,z3,z4,z5,z8]),(0,[z58,z1,z2,z3,z4,z5,z103]),(0,[z1,z366,z2,z3,z4,z5,z8]),(0,[z1,z367,z2,z3,z4,z5,z8]),(0,[z249,z1,z2,z4,z5,z8,z103])],[(0,[z368,z1,z2,z3,z4,z5,z8]),(0,[z369,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z370]),(0,[z1,z2,z3,z4,z371,z5,z8]),(1,[z1,z2,z3,z257,z5,z8]),(0,[z1,z2,z372,z3,z4,z5,z8])],[(0,[z373,z1,z2,z3,z4,z5,z8]),(0,[z162,z1,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z374]),(0,[z1,z2,z3,z4,z5,z6,z10]),(1,[z1,z375,z3,z4,z5,z8]),(0,[z1,z376,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z377,z3,z4,z5,z8]),(0,[z64,z1,z2,z3,z4,z5,z105]),(0,[z1,z2,z3,z4,z378,z5,z8]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z103])],[(1,[z1,z379,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z380]),(0,[z77,z1,z2,z3,z142,z5,z8])],[(0,[z58,z1,z2,z3,z17,z5,z8]),(0,[z130,z2,z3,z18,z4,z5,z8]),(0,[z1,z2,z179,z4,z124,z5,z8]),(0,[z1,z2,z3,z67,z4,z5,z8]),(0,[z1,z2,z3,z4,z381,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z382])],[(0,[z383,z1,z2,z3,z4,z5,z8]),(0,[z384,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z385,z5,z8]),(0,[z1,z3,z4,z26,z5,z8,z196]),(0,[z1,z386,z2,z3,z4,z5,z8]),(0,[z387,z1,z2,z3,z4,z5,z8])],[(0,[z388,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z389,z5,z8]),(0,[z1,z2,z3,z4,z390,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z391]),(0,[z1,z2,z3,z4,z5,z8,z392])],[(0,[z1,z2,z3,z4,z393,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z394]),(0,[z162,z1,z2,z3,z4,z5,z8]),(0,[z1,z191,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z395,z4,z5,z8])],[(0,[z1,z2,z3,z174,z4,z5,z103]),(0,[z396,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z166,z6]),(0,[z1,z2,z397,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z398])]],
   [[(0,[z62,z1,z2,z203,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z399]),(0,[z400,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z401,z5,z8]),(0,[z270,z1,z3,z137,z4,z5,z8]),(0,[z402,z1,z2,z3,z4,z5,z8])],[(0,[z1,z25,z74,z3,z4,z5,z8]),(0,[z403,z1,z2,z3,z4,z5,z8]),(0,[z0,z2,z3,z174,z4,z5,z8]),(0,[z172,z1,z284,z3,z4,z5,z8]),(0,[z172,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z404,z5,z8]),(0,[z1,z2,z3,z4,z4,z5,z8]),(0,[z405,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z406,z8])],[(0,[z270,z1,z45,z3,z4,z5,z8]),(0,[z131,z2,z3,z18,z4,z5,z8]),(0,[z64,z1,z2,z3,z4,z5,z6])],[(0,[z1,z407,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z137,z4,z5,z6]),(0,[z63,z1,z2,z329,z4,z5,z8]),(0,[z53,z1,z2,z123,z4,z5,z8]),(0,[z136,z2,z3,z4,z5,z8,z68]),(0,[z1,z2,z3,z4,z5,z8,z408])],[(0,[z1,z2,z409,z3,z4,z5,z8]),(0,[z1,z2,z3,z410,z4,z5,z8]),(0,[z1,z2,z3,z4,z411,z5,z8]),(0,[z1,z2,z412,z3,z4,z5,z8]),(0,[z1,z2,z179,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z413,z5,z8]),(0,[z1,z2,z3,z414,z4,z5,z8]),(1,[z57,z2,z50,z4,z5,z8]),(0,[z130,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z8,z415]),(0,[z1,z2,z3,z4,z416,z5,z8]),(0,[z1,z2,z135,z3,z4,z5,z103]),(0,[z1,z2,z3,z417,z4,z5,z8]),(0,[z1,z2,z418,z3,z4,z5,z8])],[(0,[z172,z1,z2,z174,z4,z5,z8]),(0,[z1,z2,z3,z4,z132,z5,z8])],[(0,[z1,z2,z419,z3,z4,z5,z8]),(0,[z1,z2,z50,z4,z5,z8,z103]),(0,[z1,z2,z3,z18,z4,z5,z8]),(0,[z1,z2,z90,z3,z4,z5,z83]),(0,[z1,z2,z3,z4,z5,z8,z420]),(0,[z2,z3,z4,z5,z8,z71,z68])]],
   [[(0,[z1,z421,z2,z3,z4,z5,z8]),(0,[z1,z65,z2,z3,z4,z5,z166]),(0,[z1,z2,z3,z4,z5,z281,z8]),(0,[z1,z2,z422,z3,z4,z5,z8])],[(0,[z423,z1,z2,z3,z4,z5,z8]),(0,[z231,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z424]),(1,[z1,z2,z4,z5,z8,z267])],[(0,[z172,z57,z2,z3,z4,z5,z8]),(0,[z130,z1,z2,z3,z17,z5,z8]),(0,[z1,z2,z3,z4,z425,z5,z8]),(0,[z1,z2,z3,z4,z426,z5,z8]),(0,[z63,z1,z3,z4,z5,z8,z33]),(0,[z19,z1,z2,z123,z4,z5,z8])],[(0,[z1,z2,z427,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z428]),(0,[z131,z58,z2,z3,z4,z5,z8]),(1,[z261,z2,z3,z4,z5,z8])],[(0,[z429,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z430,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z230,z8]),(0,[z1,z2,z3,z431,z4,z5,z8]),(0,[z53,z1,z2,z179,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z195,z8])],[(0,[z131,z1,z2,z3,z4,z5,z103])],[(0,[z1,z2,z3,z4,z5,z8,z432]),(0,[z1,z2,z3,z4,z5,z433,z8]),(0,[z1,z2,z168,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z8,z103]),(0,[z1,z2,z3,z4,z5,z8,z85])],[(0,[z58,z57,z2,z3,z4,z5,z8]),(0,[z53,z1,z101,z3,z4,z5,z8]),(0,[z104,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z434,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z435,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z68]),(0,[z436,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z437,z3,z4,z5,z8]),(0,[z1,z438,z2,z3,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z439,z3,z4,z5,z8])],[(1,[z162,z1,z3,z26,z5,z8]),(0,[z1,z2,z3,z440,z4,z5,z8]),(0,[z1,z2,z3,z4,z441,z5,z8]),(0,[z1,z2,z3,z4,z5,z15,z8]),(0,[z442,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z4,z5,z6,z8]),(0,[z1,z2,z3,z4,z5,z8,z170]),(0,[z1,z2,z3,z67,z195,z5,z8]),(0,[z1,z2,z3,z4,z98,z8,z10])],[(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z179,z4,z5,z8]),(0,[z1,z2,z443,z3,z4,z5,z8])],[(0,[z57,z2,z50,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z444,z8]),(1,[z1,z65,z3,z4,z5,z166]),(0,[z1,z2,z3,z445,z4,z5,z8])],[(1,[z1,z284,z3,z4,z5,z8]),(0,[z1,z2,z3,z446,z4,z5,z8]),(0,[z1,z2,z3,z447,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z448,z4,z5,z8]),(1,[z1,z2,z3,z4,z272,z5])],[(0,[z449,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z450,z8])],[(0,[z1,z90,z3,z49,z4,z5,z8]),(0,[z1,z2,z3,z4,z451,z5,z8]),(1,[z1,z2,z3,z4,z5,z406])]],
   [[(0,[z1,z2,z452,z3,z4,z5,z8]),(0,[z1,z2,z3,z453,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z103,z351])],[(0,[z73,z0,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z454,z5,z8]),(0,[z1,z455,z2,z3,z4,z5,z8]),(0,[z456,z1,z2,z3,z4,z5,z8]),(0,[z12,z1,z81,z3,z4,z5,z8]),(1,[z62,z2,z3,z4,z5,z105]),(0,[z1,z2,z3,z4,z5,z105,z103]),(0,[z1,z2,z3,z4,z457,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z458]),(0,[z1,z2,z3,z4,z5,z6,z244]),(0,[z1,z2,z3,z4,z195,z5,z8]),(0,[z1,z2,z459,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z460]),(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z1,z45,z3,z4,z217,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z461]),(0,[z1,z2,z3,z4,z5,z462,z103]),(0,[z1,z2,z375,z3,z4,z5,z8]),(0,[z1,z2,z323,z3,z4,z5,z8])],[(0,[z1,z2,z3,z463,z4,z5,z8]),(0,[z1,z2,z3,z4,z217,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z464]),(0,[z1,z2,z465,z3,z4,z5,z8]),(1,[z154,z2,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z8,z170,z68])],[(0,[z1,z2,z3,z4,z466,z5,z8]),(0,[z261,z191,z2,z3,z4,z5,z8]),(0,[z1,z2,z207,z3,z4,z5,z103]),(1,[z1,z2,z3,z142,z5,z9]),(0,[z1,z2,z467,z3,z4,z5,z8])],[(0,[z468,z1,z2,z3,z4,z5,z8]),(0,[z469,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z470,z3,z4,z5,z8])],[(0,[z471,z1,z2,z3,z4,z5,z8]),(1,[z48,z2,z3,z4,z5,z8]),(0,[z1,z2,z472,z3,z4,z5,z8]),(0,[z473,z1,z2,z3,z4,z5,z8])],[(0,[z1,z74,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z474,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z475]),(0,[z1,z2,z476,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z477]),(0,[z1,z2,z3,z4,z17,z5,z6]),(0,[z1,z2,z478,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z479]),(0,[z1,z2,z3,z4,z26,z5,z103]),(1,[z53,z1,z2,z4,z8,z54]),(0,[z43,z1,z2,z3,z5,z8,z68]),(0,[z1,z2,z3,z4,z5,z8,z480])],[(0,[z481,z1,z2,z3,z4,z5,z8]),(0,[z2,z3,z174,z18,z4,z5,z8]),(0,[z1,z2,z3,z4,z482,z5,z8]),(0,[z483,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z213,z3,z4,z5,z8]),(0,[z19,z1,z35,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z484,z103])],[(0,[z485,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z486,z5,z8]),(0,[z1,z2,z3,z487,z4,z5,z8]),(0,[z488,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z489]),(0,[z1,z2,z3,z4,z5,z8,z490]),(1,[z1,z2,z3,z4,z5,z491])],[(0,[z1,z2,z3,z3,z4,z5,z8]),(0,[z1,z2,z492,z3,z4,z5,z8]),(0,[z63,z1,z2,z3,z4,z5,z33]),(0,[z53,z1,z2,z3,z293,z5,z8]),(0,[z493,z1,z2,z3,z4,z5,z8])],[(0,[z96,z1,z2,z3,z4,z5,z8]),(0,[z43,z102,z2,z3,z4,z5,z8])],[(0,[z12,z1,z379,z3,z4,z5,z8]),(0,[z494,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z41,z3,z4,z5,z8]),(0,[z1,z2,z20,z3,z4,z5,z103]),(0,[z77,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z495,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z126])],[(0,[z1,z25,z191,z3,z4,z5,z8]),(0,[z496,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z0,z2,z3,z4,z132,z5,z8]),(0,[z172,z1,z2,z3,z4,z5,z11]),(0,[z2,z3,z18,z4,z132,z5,z8]),(0,[z1,z2,z3,z4,z5,z497,z8]),(1,[z1,z2,z189,z4,z5,z8]),(0,[z53,z1,z2,z4,z5,z8,z54]),(0,[z1,z498,z2,z3,z4,z5,z8])],[(0,[z499,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z500,z4,z5,z8]),(0,[z1,z2,z501,z3,z4,z5,z8]),(0,[z1,z502,z2,z3,z4,z5,z8])],[(0,[z1,z2,z503,z3,z4,z5,z8]),(0,[z504,z1,z2,z3,z4,z5,z8]),(0,[z249,z1,z2,z3,z4,z5,z103]),(0,[z1,z505,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z506]),(0,[z507,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z508,z5,z8])],[(0,[z2,z74,z3,z4,z17,z5,z8]),(0,[z130,z2,z74,z3,z4,z5,z8]),(0,[z509,z1,z2,z3,z4,z5,z8]),(0,[z1,z510,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z205])],[(0,[z1,z2,z3,z4,z5,z8,z511]),(0,[z1,z512,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z513,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z299]),(1,[z1,z514,z3,z4,z5,z8]),(0,[z53,z303,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z515]),(0,[z516,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z517,z4,z5,z8]),(0,[z1,z2,z518,z3,z4,z5,z8]),(0,[z270,z162,z1,z3,z4,z5,z8]),(1,[z1,z2,z123,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z8])],[(0,[z519,z1,z2,z3,z4,z5,z8]),(0,[z63,z1,z2,z41,z4,z5,z8]),(0,[z1,z3,z4,z5,z166,z8,z33])],[(0,[z1,z2,z3,z4,z520,z5,z8]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z521,z3,z4,z5,z8]),(0,[z1,z522,z2,z3,z4,z5,z8])]],
   [[(1,[z1,z81,z3,z4,z5,z8]),(0,[z1,z2,z3,z523,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z524,z8]),(0,[z270,z1,z2,z3,z4,z8,z196]),(0,[z1,z2,z3,z4,z5,z8,z196]),(0,[z1,z2,z3,z525,z4,z5,z8])],[(0,[z1,z45,z2,z3,z4,z5,z6]),(0,[z172,z1,z2,z50,z4,z5,z8]),(0,[z172,z1,z2,z3,z4,z5,z526]),(0,[z527,z1,z2,z3,z4,z5,z8]),(0,[z19,z1,z2,z135,z3,z5,z8])],[(0,[z2,z3,z4,z132,z5,z8,z13]),(0,[z1,z2,z90,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z8,z528]),(0,[z1,z2,z3,z4,z5,z6,z9])],[(0,[z131,z2,z74,z3,z4,z5,z8]),(0,[z1,z25,z2,z3,z4,z5,z103]),(0,[z529,z1,z2,z3,z4,z5,z8]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z142,z4,z98,z5])],[(0,[z0,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z530,z4,z5,z8]),(0,[z531,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z20,z4,z155,z5,z8]),(0,[z1,z2,z3,z4,z272,z5,z68])],[(0,[z1,z2,z3,z4,z5,z8,z532]),(0,[z1,z2,z3,z448,z4,z5,z103]),(0,[z1,z2,z3,z4,z533,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z534]),(0,[z1,z2,z3,z4,z5,z8,z535])],[(0,[z536,z1,z2,z3,z4,z5,z8]),(0,[z1,z277,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z103,z103]),(0,[z1,z2,z3,z4,z5,z103,z85]),(0,[z1,z2,z3,z4,z5,z537,z8])],[(1,[z1,z2,z3,z4,z5,z322]),(0,[z278,z1,z2,z3,z4,z5,z103])]],
   [[(0,[z1,z2,z74,z3,z4,z5,z8]),(0,[z130,z12,z2,z3,z4,z5,z8]),(0,[z538,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z539]),(0,[z1,z2,z3,z4,z5,z103,z68]),(0,[z1,z2,z3,z4,z5,z6,z540]),(0,[z1,z2,z3,z67,z4,z195,z8])],[(0,[z1,z2,z541,z3,z4,z5,z8]),(0,[z19,z337,z2,z3,z4,z5,z8]),(0,[z1,z337,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z542]),(0,[z1,z2,z193,z3,z4,z5,z8])],[(0,[z1,z2,z3,z543,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z42])],[(0,[z1,z2,z3,z4,z5,z544,z8]),(0,[z1,z2,z3,z545,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z178,z8]),(0,[z1,z2,z3,z4,z5,z8,z546]),(0,[z1,z547,z2,z3,z4,z5,z8])],[(0,[z1,z74,z3,z49,z4,z5,z8]),(0,[z1,z2,z3,z548,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z50,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z549,z5,z8]),(0,[z1,z25,z3,z4,z5,z8,z196]),(0,[z338,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z550,z5,z8])],[(0,[z60,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z49,z4,z5,z103]),(1,[z1,z2,z3,z67,z195,z8]),(0,[z551,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z552,z5,z8]),(0,[z553,z1,z2,z3,z4,z5,z8]),(0,[z554,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z555,z8]),(0,[z556,z1,z2,z3,z4,z5,z8]),(0,[z1,z89,z191,z3,z4,z5,z8]),(0,[z1,z65,z2,z3,z4,z5,z33])],[(0,[z58,z1,z23,z3,z4,z5,z8]),(0,[z557,z1,z2,z3,z4,z5,z8]),(1,[z77,z1,z2,z3,z5,z85]),(0,[z1,z2,z3,z4,z558,z5,z8])]],
   [[(0,[z131,z12,z2,z3,z4,z5,z8]),(0,[z1,z559,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z560,z5,z8]),(1,[z1,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z561,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z562]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z1,z321,z2,z3,z4,z5,z8]),(0,[z63,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z563,z8]),(0,[z57,z2,z3,z18,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z8])],[(0,[z564,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z565,z8]),(0,[z1,z2,z20,z3,z4,z5,z491]),(0,[z1,z2,z135,z3,z67,z5,z8]),(0,[z566,z1,z2,z3,z4,z5,z8])],[(0,[z12,z2,z3,z4,z17,z5,z8]),(0,[z1,z2,z567,z3,z4,z5,z8]),(0,[z1,z2,z568,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z569,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z281]),(0,[z1,z2,z3,z4,z5,z8,z570]),(0,[z1,z2,z3,z4,z571,z5,z8])],[(0,[z0,z1,z74,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z526]),(0,[z1,z2,z3,z4,z572,z5,z8]),(0,[z1,z2,z3,z573,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z574])],[(0,[z1,z2,z3,z4,z575,z5,z8]),(0,[z62,z1,z213,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z380]),(0,[z576,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z577,z5,z8]),(0,[z1,z2,z578,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z579,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z580]),(0,[z1,z2,z3,z4,z5,z166,z8]),(0,[z1,z2,z3,z4,z5,z103,z477]),(0,[z581,z1,z2,z3,z4,z5,z8])],[(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z582,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z78,z4,z5,z8])],[(0,[z172,z1,z2,z3,z4,z5,z8]),(0,[z1,z89,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z583,z4,z5,z8]),(0,[z1,z3,z137,z4,z217,z5,z8]),(0,[z1,z2,z3,z4,z98,z5,z103]),(1,[z212,z2,z3,z4,z5,z8]),(0,[z1,z2,z323,z4,z5,z8,z68])],[(0,[z172,z1,z241,z3,z4,z5,z8]),(0,[z584,z1,z2,z3,z4,z5,z8]),(0,[z64,z1,z2,z3,z4,z5,z8]),(0,[z585,z1,z2,z3,z4,z5,z8]),(0,[z1,z586,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z587,z8]),(0,[z63,z1,z65,z3,z4,z5,z8]),(0,[z1,z2,z179,z3,z4,z5,z119]),(0,[z1,z2,z3,z4,z181,z5,z8])],[(0,[z1,z2,z3,z4,z588,z5,z8]),(0,[z58,z2,z3,z4,z17,z5,z8]),(0,[z62,z1,z2,z3,z4,z5,z103]),(1,[z111,z2,z3,z4,z5,z8]),(0,[z589,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z137,z4,z5,z8]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z398])],[(0,[z590,z1,z2,z3,z4,z5,z8]),(0,[z57,z1,z2,z3,z4,z5,z103]),(0,[z591,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z20,z3,z4,z5,z299]),(0,[z1,z2,z179,z3,z4,z5,z8]),(0,[z97,z1,z2,z3,z4,z5,z103]),(0,[z149,z1,z2,z364,z4,z5,z8])],[(1,[z1,z23,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z592,z5,z8]),(1,[z1,z2,z90,z4,z5,z103]),(0,[z1,z2,z20,z3,z124,z5,z8]),(0,[z53,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z86,z6])],[(0,[z1,z2,z3,z4,z593,z5,z8]),(0,[z1,z2,z3,z4,z5,z479,z8]),(0,[z594,z1,z2,z3,z4,z5,z8]),(0,[z1,z595,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z596]),(1,[z2,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z597,z5,z8]),(0,[z1,z2,z135,z4,z124,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z598]),(0,[z301,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z599,z8]),(0,[z1,z2,z600,z3,z4,z5,z8]),(0,[z1,z2,z3,z142,z4,z5,z103]),(0,[z1,z2,z3,z142,z4,z5,z85])],[(0,[z1,z2,z3,z4,z5,z601,z8])],[(0,[z1,z2,z3,z174,z4,z5,z6]),(0,[z1,z2,z602,z3,z4,z5,z8]),(0,[z1,z89,z3,z4,z5,z8,z196])],[],[(0,[z1,z2,z3,z603,z4,z5,z8]),(0,[z604,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z605]),(0,[z19,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z606,z5,z8])],[(0,[z607,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z3,z4,z5,z103])],[(0,[z608,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z609,z5,z8]),(0,[z1,z2,z135,z4,z155,z5,z8])]],
   [[(0,[z1,z2,z610,z3,z4,z5,z8]),(0,[z58,z1,z2,z3,z18,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z611]),(0,[z1,z25,z3,z137,z4,z5,z8]),(0,[z1,z212,z2,z3,z4,z5,z8])],[(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z60,z1,z2,z3,z4,z5,z479]),(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z1,z2,z3,z612,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z613,z8])],[(0,[z614,z1,z2,z3,z4,z5,z8]),(1,[z130,z2,z3,z18,z5,z8]),(0,[z615,z1,z2,z3,z4,z5,z8]),(0,[z93,z1,z2,z3,z4,z5,z8]),(0,[z616,z1,z2,z3,z4,z5,z8])],[(0,[z1,z89,z74,z3,z4,z5,z8]),(0,[z0,z1,z45,z3,z4,z5,z8]),(0,[z1,z617,z2,z3,z4,z5,z8]),(0,[z162,z1,z3,z4,z217,z5,z8]),(0,[z618,z1,z2,z3,z4,z5,z8]),(0,[z1,z191,z3,z4,z217,z5,z8]),(0,[z53,z1,z2,z3,z4,z155,z8]),(0,[z149,z1,z2,z418,z4,z5,z8])],[(0,[z1,z65,z2,z3,z4,z5,z8]),(0,[z619,z1,z2,z3,z4,z5,z8])],[(0,[z2,z74,z3,z4,z5,z8,z105]),(1,[z1,z59,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z620,z5,z8]),(1,[z176,z2,z3,z4,z5,z8]),(0,[z1,z2,z621,z3,z4,z5,z8]),(0,[z1,z2,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z67,z4,z5,z103])],[(0,[z2,z74,z3,z174,z4,z5,z8]),(0,[z1,z2,z622,z3,z4,z5,z8]),(0,[z623,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z624]),(1,[z1,z2,z3,z4,z181,z5]),(0,[z77,z1,z2,z3,z4,z5,z9])],[(1,[z1,z241,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z625])]],
   [[(0,[z626,z1,z2,z3,z4,z5,z8]),(0,[z131,z0,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z627,z8]),(0,[z1,z2,z3,z4,z5,z8,z54]),(0,[z237,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z628])],[(0,[z1,z2,z3,z4,z5,z8,z629]),(0,[z131,z1,z2,z3,z4,z5,z6]),(0,[z246,z1,z2,z3,z4,z5,z8]),(0,[z162,z1,z2,z3,z4,z5,z103]),(0,[z1,z191,z2,z3,z4,z5,z103]),(0,[z53,z1,z2,z3,z4,z5,z406]),(0,[z1,z2,z3,z4,z5,z103,z542]),(0,[z163,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z630,z5,z8])],[(0,[z631,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z632,z5,z8]),(0,[z633,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z103]),(0,[z1,z2,z3,z4,z5,z8,z462]),(0,[z1,z2,z3,z4,z5,z6,z85])],[(0,[z73,z1,z2,z3,z4,z5,z8]),(0,[z57,z1,z2,z174,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z634]),(1,[z1,z2,z329,z4,z5,z8])],[(0,[z1,z2,z3,z635,z4,z5,z8]),(0,[z1,z2,z3,z4,z217,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z68])],[(0,[z1,z2,z3,z4,z636,z5,z8]),(0,[z1,z2,z637,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z638]),(0,[z64,z2,z3,z4,z5,z230,z8]),(0,[z1,z2,z3,z639,z4,z5,z8])],[(0,[z640,z1,z2,z3,z4,z5,z8]),(0,[z641,z1,z2,z3,z4,z5,z8]),(0,[z642,z1,z2,z3,z4,z5,z8])],[(0,[z643,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z644,z3,z4,z5,z8]),(0,[z60,z1,z2,z90,z4,z5,z8]),(0,[z1,z2,z3,z4,z645,z5,z8]),(0,[z1,z180,z2,z3,z4,z5,z6]),(0,[z43,z1,z375,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z646,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z647]),(0,[z1,z648,z2,z3,z4,z5,z8])],[(0,[z1,z45,z89,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z5,z8]),(0,[z1,z2,z3,z4,z132,z5,z103]),(1,[z1,z2,z3,z4,z5,z91]),(1,[z246,z2,z3,z4,z5,z8]),(0,[z649,z1,z2,z3,z4,z5,z8]),(0,[z63,z76,z2,z3,z4,z5,z8]),(1,[z63,z1,z3,z4,z5,z33])],[(0,[z1,z2,z3,z4,z5,z650,z8]),(1,[z58,z2,z3,z17,z5,z8]),(0,[z1,z2,z3,z18,z4,z5,z103]),(0,[z651,z1,z2,z3,z4,z5,z8])],[(0,[z652,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z653]),(0,[z1,z2,z3,z4,z5,z424,z103]),(0,[z1,z2,z3,z4,z5,z192,z6]),(0,[z1,z2,z3,z4,z5,z8,z229]),(1,[z1,z2,z143,z4,z5,z8]),(0,[z1,z654,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z655,z4,z5,z8]),(0,[z1,z154,z2,z3,z4,z5,z8]),(0,[z149,z1,z2,z3,z4,z5,z9])],[(0,[z656,z1,z2,z3,z4,z5,z8])],[(0,[z62,z1,z321,z3,z4,z5,z8]),(1,[z1,z2,z4,z124,z5,z103]),(0,[z77,z1,z2,z3,z4,z5,z8])],[(0,[z657,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z230,z103]),(1,[z152,z2,z3,z4,z5,z8]),(0,[z1,z89,z3,z137,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z491]),(0,[z1,z2,z20,z4,z124,z5,z8]),(0,[z1,z2,z4,z124,z5,z8,z103]),(0,[z1,z658,z2,z3,z4,z5,z8]),(0,[z659,z1,z2,z3,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z398])]],
   [[(1,[z73,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z660,z5,z8]),(0,[z1,z2,z3,z4,z5,z661,z8]),(0,[z1,z662,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z343]),(1,[z131,z2,z3,z4,z8,z13]),(0,[z1,z379,z2,z3,z4,z5,z8]),(1,[z43,z1,z2,z3,z8,z68])],[(1,[z1,z2,z320,z4,z5,z8]),(1,[z1,z2,z364,z4,z5,z8])],[(0,[z57,z2,z74,z3,z4,z5,z8]),(0,[z1,z45,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z126]),(0,[z62,z1,z65,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z91]),(0,[z663,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z664])],[(0,[z1,z2,z3,z4,z5,z526,z8]),(0,[z1,z2,z3,z4,z5,z8,z665]),(0,[z1,z89,z2,z90,z4,z5,z8]),(0,[z1,z2,z3,z4,z26,z5,z6]),(0,[z1,z2,z3,z666,z4,z5,z8]),(0,[z43,z1,z2,z3,z4,z5,z103])],[(0,[z60,z1,z2,z3,z4,z5,z380])],[(0,[z1,z2,z3,z4,z5,z8,z667]),(0,[z1,z2,z3,z4,z5,z8,z668]),(1,[z1,z2,z4,z155,z5,z103]),(0,[z1,z2,z3,z4,z5,z669,z8])],[(0,[z670,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z124,z5,z8,z68])]],
   [[(0,[z671,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z5,z8]),(1,[z1,z2,z49,z4,z5,z103]),(0,[z270,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z205])],[(0,[z672,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z343,z8]),(0,[z1,z2,z3,z4,z673,z5,z8]),(0,[z1,z2,z3,z4,z674,z5,z8]),(0,[z1,z2,z3,z4,z5,z675,z8]),(0,[z1,z2,z3,z4,z676,z5,z8]),(0,[z1,z2,z20,z3,z4,z5,z6])],[(0,[z677,z1,z2,z3,z4,z5,z8]),(0,[z172,z2,z3,z174,z4,z5,z8]),(0,[z1,z2,z678,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z679]),(0,[z680,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z49,z4,z5,z8,z103]),(0,[z1,z2,z3,z4,z681,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z682]),(0,[z1,z2,z179,z3,z4,z155,z8]),(0,[z1,z2,z3,z4,z5,z683,z8])],[(0,[z1,z2,z3,z4,z5,z684,z8]),(0,[z1,z2,z3,z685,z4,z5,z8]),(0,[z1,z2,z3,z4,z686,z5,z8]),(0,[z687,z1,z2,z3,z4,z5,z8]),(0,[z77,z1,z2,z3,z5,z8,z85])],[(0,[z688,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z689]),(0,[z690,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z293,z5,z8]),(0,[z1,z2,z3,z4,z195,z5,z103]),(0,[z149,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z174,z4,z5,z103]),(0,[z691,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z13,z103]),(0,[z19,z1,z514,z3,z4,z5,z8]),(0,[z1,z2,z3,z692,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z103,z605]),(0,[z1,z2,z3,z4,z5,z8,z484]),(0,[z693,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z142,z5,z9,z8])],[(0,[z1,z2,z3,z4,z5,z694,z8]),(0,[z1,z2,z3,z4,z5,z8,z695]),(0,[z19,z1,z2,z3,z124,z5,z8]),(0,[z1,z2,z4,z124,z5,z8,z54]),(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z623,z1,z2,z3,z4,z5,z103])],[(0,[z58,z2,z3,z174,z4,z5,z8]),(0,[z62,z1,z2,z3,z4,z5,z230]),(0,[z270,z1,z2,z3,z4,z217,z8]),(1,[z136,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z696,z5,z8]),(0,[z57,z12,z2,z3,z4,z5,z8]),(1,[z1,z2,z418,z4,z5,z8])],[(0,[z697,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z698,z4,z5,z8]),(0,[z1,z2,z3,z4,z699,z5,z8]),(0,[z1,z2,z700,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z701,z5,z8]),(0,[z1,z2,z3,z4,z5,z540,z8]),(0,[z77,z1,z2,z193,z4,z5,z8])],[(0,[z12,z1,z2,z3,z4,z132,z8])],[(0,[z702,z1,z2,z3,z4,z5,z8]),(0,[z53,z1,z2,z3,z257,z5,z8])],[(1,[z1,z2,z327,z3,z4,z5]),(0,[z1,z45,z65,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z53,z1,z2,z20,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z322]),(0,[z703,z1,z2,z3,z4,z5,z8]),(0,[z97,z149,z1,z2,z3,z4,z5])],[(0,[z338,z1,z2,z3,z4,z5,z8]),(0,[z58,z130,z2,z3,z4,z5,z8]),(0,[z131,z2,z3,z4,z5,z8,z13]),(1,[z2,z3,z4,z5,z8,z71])],[(0,[z1,z45,z3,z4,z5,z8,z33]),(0,[z1,z2,z3,z4,z5,z8,z704]),(0,[z60,z1,z89,z3,z4,z5,z8]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z705,z1,z2,z3,z4,z5,z8]),(1,[z76,z2,z3,z4,z5,z8]),(0,[z1,z514,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z3,z4,z5,z103])],[(0,[z1,z2,z3,z706,z4,z5,z8]),(0,[z1,z25,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z124,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z81,z3,z4,z132,z5,z8]),(0,[z707,z2,z3,z4,z5,z8]),(0,[z708,z2,z3,z4,z5,z8]),(0,[z19,z1,z35,z4,z5,z103]),(0,[z19,z1,z2,z135,z5,z36])],[(0,[z1,z709,z3,z4,z5,z8]),(0,[z131,z2,z3,z4,z684,z8]),(0,[z1,z2,z710,z4,z5,z8]),(0,[z1,z2,z3,z4,z711,z5]),(0,[z712,z2,z3,z4,z5,z8])],[(0,[z1,z2,z713,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z714]),(0,[z715,z2,z3,z4,z5,z8]),(0,[z1,z2,z578,z4,z5,z103]),(0,[z254,z3,z4,z217,z5,z8]),(0,[z1,z2,z3,z293,z5,z205]),(0,[z1,z2,z179,z4,z155,z6])],[(0,[z131,z2,z3,z4,z13,z103]),(0,[z1,z2,z716,z4,z5,z8]),(0,[z1,z2,z717,z3,z4,z5]),(0,[z282,z1,z3,z4,z272,z5])],[(0,[z1,z2,z718,z4,z5,z8]),(0,[z536,z1,z2,z4,z5,z103]),(0,[z1,z2,z248,z4,z5,z103]),(0,[z21,z96,z1,z2,z3,z4]),(0,[z212,z2,z3,z4,z5,z398]),(0,[z719,z1,z2,z3,z4,z5])],[(0,[z2,z3,z4,z272,z5,z71]),(0,[z1,z2,z4,z181,z5,z267])],[(0,[z1,z2,z74,z720,z4,z5]),(0,[z1,z2,z721,z4,z5,z8]),(0,[z1,z2,z67,z124,z5,z103])],[(0,[z1,z2,z3,z4,z5,z722]),(0,[z723,z2,z3,z4,z5,z103]),(0,[z43,z1,z2,z320,z8,z68]),(0,[z724,z2,z3,z4,z5,z8]),(0,[z725,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z726]),(0,[z1,z2,z165,z4,z5,z103]),(0,[z63,z1,z3,z4,z5,z33])],[(0,[z1,z2,z3,z4,z5,z727]),(0,[z60,z152,z49,z4,z5,z8]),(0,[z60,z1,z49,z4,z5,z6]),(0,[z1,z90,z728,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z729]),(0,[z1,z730,z3,z4,z5,z103]),(0,[z212,z2,z3,z4,z5,z103]),(0,[z2,z3,z4,z5,z103,z71]),(0,[z1,z2,z731,z4,z5,z8])],[(0,[z1,z732,z3,z4,z5,z8]),(0,[z1,z733,z3,z4,z5,z8]),(1,[z1,z728,z4,z5,z8]),(0,[z1,z375,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z734])],[(0,[z62,z2,z3,z4,z5,z735]),(0,[z111,z2,z3,z4,z5,z103]),(0,[z1,z2,z736,z4,z5,z8]),(0,[z325,z1,z2,z4,z5,z103]),(0,[z303,z2,z3,z4,z5,z205]),(0,[z1,z2,z3,z257,z5,z406]),(0,[z737,z2,z3,z4,z5,z8])],[(0,[z64,z2,z3,z4,z5,z735]),(0,[z1,z2,z440,z4,z5,z103]),(0,[z738,z2,z3,z4,z5,z8]),(0,[z53,z154,z2,z4,z5,z103])],[(0,[z1,z2,z739,z4,z5,z8]),(0,[z1,z23,z3,z4,z5,z103]),(0,[z1,z2,z740,z4,z5,z8]),(0,[z130,z2,z3,z487,z5,z8]),(0,[z1,z2,z741,z4,z5,z8]),(0,[z1,z2,z742,z4,z5,z8]),(0,[z261,z2,z3,z4,z5,z103]),(0,[z1,z2,z4,z124,z5,z103])],[(0,[z2,z254,z3,z4,z5,z103]),(0,[z1,z2,z323,z124,z5,z8])],[(0,[z73,z74,z3,z4,z5,z8]),(0,[z743,z2,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z166,z744]),(0,[z19,z1,z2,z4,z5,z103]),(0,[z1,z3,z4,z5,z8,z745]),(0,[z1,z107,z123,z4,z5,z8])]],
   [[(0,[z2,z746,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z747]),(0,[z102,z2,z3,z4,z5,z8]),(0,[z1,z2,z748,z4,z5,z8]),(0,[z131,z2,z3,z4,z8,z13]),(0,[z1,z749,z3,z4,z5,z8]),(0,[z750,z2,z3,z4,z5,z8]),(0,[z1,z2,z193,z4,z5,z8]),(0,[z1,z751,z3,z4,z5,z8]),(0,[z43,z1,z2,z3,z8,z68]),(0,[z752,z2,z3,z4,z5,z8]),(0,[z77,z1,z2,z193,z5,z85])],[(0,[z1,z753,z3,z4,z5,z8]),(0,[z1,z213,z3,z4,z5,z6]),(0,[z1,z49,z137,z4,z5,z103]),(0,[z1,z2,z20,z293,z5,z8])],[(0,[z1,z754,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z735,z105]),(0,[z1,z2,z755,z4,z5,z8]),(0,[z76,z2,z41,z4,z5,z8]),(0,[z337,z514,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z756])],[(0,[z1,z2,z3,z4,z5,z757]),(0,[z758,z1,z3,z4,z5,z8]),(0,[z759,z2,z3,z4,z5,z8]),(0,[z1,z2,z78,z4,z5,z9]),(0,[z1,z2,z364,z4,z98,z5])],[(0,[z1,z89,z452,z4,z5,z8]),(0,[z1,z2,z203,z4,z5,z8]),(0,[z2,z3,z760,z4,z5,z8]),(0,[z53,z1,z2,z257,z8,z54]),(0,[z1,z761,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z762,z5]),(0,[z1,z35,z3,z4,z5,z15]),(0,[z1,z2,z372,z4,z5,z103])],[(0,[z1,z2,z3,z4,z763,z8]),(0,[z1,z2,z4,z294,z5,z103]),(0,[z43,z136,z2,z3,z8,z68])],[(0,[z270,z1,z3,z4,z8,z428]),(0,[z1,z284,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z2,z765,z4,z5,z8]),(0,[z1,z2,z49,z4,z5,z103]),(0,[z766,z2,z3,z4,z5,z8]),(0,[z1,z35,z4,z5,z8,z103]),(0,[z1,z2,z3,z4,z5,z767])]],
   [[(0,[z57,z2,z50,z4,z5,z6]),(0,[z1,z768,z3,z4,z5,z8]),(0,[z1,z769,z3,z4,z5,z8]),(0,[z1,z2,z296,z4,z5,z103]),(0,[z162,z1,z3,z645,z5,z8]),(0,[z1,z2,z3,z4,z5,z770]),(0,[z1,z191,z3,z4,z217,z8]),(0,[z1,z771,z3,z4,z5,z8])],[(0,[z130,z2,z3,z18,z5,z103]),(0,[z1,z2,z3,z4,z772,z8])],[(0,[z631,z2,z174,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z2,z90,z4,z5,z774]),(0,[z775,z1,z3,z4,z5,z8]),(0,[z1,z2,z308,z4,z5,z103])],[(0,[z776,z1,z2,z3,z4,z5]),(0,[z162,z246,z3,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z777]),(0,[z2,z323,z4,z5,z8,z71])],[(0,[z2,z778,z3,z4,z5,z8]),(0,[z176,z2,z3,z4,z5,z103]),(0,[z1,z2,z20,z124,z5,z6]),(0,[z1,z2,z779,z4,z5,z8]),(0,[z1,z2,z4,z155,z8,z319]),(0,[z1,z2,z448,z4,z155,z8]),(0,[z212,z2,z3,z4,z5,z281])],[(0,[z57,z2,z760,z4,z5,z8]),(0,[z1,z780,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z154,z2,z3,z4,z5,z103]),(0,[z102,z2,z143,z4,z5,z8]),(0,[z1,z375,z143,z4,z5,z8]),(0,[z1,z2,z3,z4,z98,z10])],[(0,[z1,z241,z3,z4,z5,z103]),(0,[z136,z2,z3,z4,z5,z8]),(0,[z130,z2,z3,z782,z5,z8]),(0,[z1,z2,z4,z318,z5,z103]),(0,[z1,z783,z3,z4,z5,z8]),(0,[z53,z1,z101,z4,z8,z54])],[(0,[z93,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z257,z5,z205]),(0,[z1,z2,z3,z4,z5,z784]),(0,[z1,z2,z4,z785,z5,z267])]],
   [[(0,[z1,z2,z786,z4,z5,z8]),(0,[z1,z2,z567,z4,z5,z103]),(0,[z1,z787,z3,z4,z5,z8]),(0,[z1,z367,z2,z4,z5,z103])],[(0,[z1,z2,z3,z4,z5,z788]),(0,[z57,z2,z478,z4,z5,z8]),(0,[z1,z2,z324,z4,z5,z103]),(0,[z1,z101,z3,z4,z5,z8]),(0,[z789,z2,z3,z4,z5,z103])],[(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z90,z49,z4,z5,z103]),(0,[z1,z2,z329,z4,z5,z103]),(0,[z1,z2,z41,z4,z5,z83]),(0,[z270,z1,z3,z4,z450,z8]),(0,[z1,z2,z3,z4,z5,z791]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z793,z3,z4,z5,z8]),(0,[z93,z35,z3,z4,z5,z8]),(0,[z21,z149,z1,z2,z3,z4]),(0,[z1,z2,z794,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z795]),(0,[z1,z2,z78,z4,z5,z8]),(0,[z1,z2,z4,z332,z5,z103]),(0,[z212,z44,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z796]),(0,[z1,z213,z189,z4,z5,z8]),(0,[z1,z3,z4,z5,z797,z8]),(0,[z1,z2,z179,z4,z155,z322]),(0,[z102,z2,z320,z4,z5,z8]),(0,[z1,z375,z320,z4,z5,z8]),(0,[z1,z2,z3,z5,z8,z798])],[(0,[z1,z2,z637,z4,z5,z103]),(0,[z1,z2,z90,z4,z5,z380]),(0,[z162,z1,z3,z26,z5,z6]),(0,[z1,z107,z4,z5,z8,z103]),(0,[z1,z277,z3,z4,z5,z462]),(0,[z1,z2,z143,z4,z5,z398]),(0,[z1,z3,z4,z5,z8,z799])],[(0,[z1,z2,z800,z4,z5,z8]),(0,[z64,z213,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z801]),(0,[z337,z2,z3,z4,z5,z36])],[(0,[z1,z2,z802,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z803]),(0,[z1,z804,z3,z4,z5,z8]),(0,[z1,z2,z4,z129,z5,z103])]],
   [[(0,[z1,z2,z3,z805,z5,z8]),(0,[z246,z2,z3,z4,z5,z103]),(0,[z1,z2,z342,z4,z5,z103]),(0,[z1,z2,z806,z4,z5,z8])],[(0,[z57,z2,z50,z4,z5,z126]),(0,[z59,z3,z4,z132,z5,z8]),(0,[z58,z2,z3,z17,z5,z103]),(0,[z1,z2,z315,z4,z5,z103]),(0,[z1,z2,z807,z4,z5,z8]),(0,[z1,z191,z3,z4,z401,z8]),(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z2,z3,z4,z5,z15])],[(0,[z1,z2,z809,z4,z5,z8]),(0,[z1,z2,z189,z4,z5,z103]),(0,[z1,z810,z3,z4,z5,z8]),(0,[z162,z1,z3,z674,z5,z8]),(0,[z1,z2,z3,z4,z8,z811]),(0,[z1,z2,z143,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z43,z1,z2,z3,z281,z68])],[(0,[z172,z2,z174,z4,z5,z11]),(0,[z1,z2,z3,z782,z5,z8]),(0,[z1,z2,z4,z124,z5,z491])],[(0,[z1,z35,z3,z4,z5,z8]),(0,[z1,z2,z320,z4,z5,z398]),(0,[z1,z3,z4,z272,z5,z170])],[(0,[z1,z2,z189,z4,z5,z86]),(0,[z813,z2,z3,z4,z5,z8]),(0,[z725,z1,z2,z3,z4,z8])],[(0,[z1,z2,z3,z4,z5,z814]),(0,[z1,z2,z4,z5,z6,z399]),(0,[z152,z2,z3,z4,z5,z103]),(0,[z47,z1,z2,z4,z5,z103]),(0,[z815,z2,z3,z4,z5,z8]),(0,[z19,z337,z2,z4,z5,z103]),(0,[z816,z2,z3,z4,z5,z8])],[(0,[z1,z817,z3,z4,z5,z8]),(0,[z1,z2,z568,z124,z5,z8]),(0,[z1,z2,z3,z66,z5,z192]),(0,[z818,z2,z3,z4,z5,z8])]],
   [[(0,[z74,z3,z4,z696,z5,z8]),(0,[z1,z819,z3,z4,z5,z8]),(0,[z1,z2,z602,z4,z5,z103]),(0,[z1,z49,z4,z5,z196,z103]),(0,[z1,z2,z4,z361,z5,z103]),(0,[z232,z1,z2,z135,z5,z8]),(0,[z154,z2,z3,z4,z5,z406]),(0,[z820,z1,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z103,z170])],[(0,[z48,z2,z3,z4,z5,z6]),(0,[z1,z2,z364,z4,z5,z103]),(0,[z1,z2,z320,z4,z5,z103]),(0,[z1,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z785,z5]),(0,[z1,z2,z364,z4,z5,z85])],[(0,[z1,z2,z3,z4,z5,z821]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z2,z3,z4,z5,z823])],[(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z2,z4,z155,z5,z491]),(0,[z1,z2,z4,z5,z570,z103]),(0,[z97,z1,z2,z364,z4,z5])],[(0,[z172,z2,z174,z4,z5,z526]),(0,[z1,z2,z543,z4,z5,z103]),(0,[z1,z547,z90,z4,z5,z8]),(0,[z43,z1,z2,z3,z272,z68]),(0,[z282,z3,z4,z5,z8,z71])],[(0,[z1,z2,z825,z3,z4,z5]),(0,[z1,z2,z3,z826,z4,z5]),(0,[z1,z3,z4,z5,z8,z827]),(0,[z1,z2,z3,z4,z5,z83]),(0,[z828,z2,z3,z4,z5,z8]),(0,[z829,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z293,z5,z8]),(0,[z2,z3,z4,z5,z6,z71]),(0,[z1,z2,z830,z4,z5,z8])],[(0,[z1,z89,z90,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z470,z124,z5,z8]),(0,[z53,z303,z2,z4,z5,z103])],[(0,[z1,z512,z2,z4,z5,z103]),(0,[z1,z2,z3,z4,z833,z5]),(0,[z1,z2,z124,z5,z8,z370]),(0,[z834,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z835,z5,z8]),(0,[z1,z2,z4,z16,z155,z103])]],
   [[(0,[z1,z836,z3,z4,z5,z8]),(0,[z302,z1,z2,z4,z5,z103]),(0,[z303,z107,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z515,z103]),(0,[z43,z1,z2,z3,z103,z68]),(0,[z1,z2,z837,z4,z5,z8])],[(0,[z2,z3,z18,z5,z8,z328]),(0,[z1,z321,z3,z4,z5,z6]),(0,[z1,z2,z242,z4,z5,z103]),(0,[z838,z2,z3,z4,z5,z8]),(0,[z2,z839,z3,z4,z5,z8]),(0,[z249,z1,z2,z4,z5,z767]),(0,[z1,z2,z323,z4,z5,z6])],[(0,[z64,z2,z3,z4,z5,z563]),(0,[z1,z2,z4,z390,z5,z103]),(0,[z53,z1,z2,z4,z5,z103]),(0,[z163,z1,z2,z3,z5,z42]),(0,[z43,z1,z2,z8,z267,z68]),(0,[z282,z1,z4,z5,z8,z267])],[(0,[z194,z2,z174,z4,z5,z8]),(0,[z1,z2,z4,z5,z8,z840]),(0,[z1,z2,z622,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z841]),(0,[z1,z2,z3,z4,z5,z842]),(0,[z1,z2,z3,z843,z5,z8]),(0,[z53,z1,z2,z4,z54,z103])],[(0,[z1,z844,z3,z4,z5,z8]),(0,[z270,z1,z3,z4,z8,z196]),(0,[z48,z2,z329,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z845]),(0,[z1,z2,z193,z4,z5,z15]),(0,[z1,z154,z2,z4,z5,z103]),(0,[z1,z2,z4,z5,z6,z103]),(0,[z1,z2,z4,z5,z103,z42]),(0,[z1,z2,z3,z4,z533,z10])],[(0,[z0,z45,z3,z4,z5,z8]),(0,[z1,z2,z846,z4,z5,z8]),(0,[z130,z2,z3,z548,z5,z8]),(0,[z1,z2,z847,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z4,z849,z5]),(0,[z1,z2,z143,z4,z5,z281]),(0,[z1,z2,z3,z5,z8,z850])],[(0,[z303,z2,z3,z4,z5,z8]),(0,[z1,z851,z3,z4,z5,z8]),(0,[z1,z2,z4,z404,z5,z103]),(0,[z337,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z119]),(0,[z1,z2,z4,z5,z406,z103]),(0,[z1,z3,z4,z5,z8,z852])],[(0,[z1,z2,z295,z4,z5,z103]),(1,[z2,z760,z4,z5,z8]),(0,[z1,z853,z3,z4,z5,z8]),(0,[z62,z2,z189,z4,z5,z105]),(0,[z1,z514,z3,z4,z5,z6]),(0,[z1,z2,z418,z4,z5,z103]),(0,[z1,z2,z323,z4,z181,z5]),(0,[z1,z2,z78,z4,z5,z192])]],
   [[(0,[z512,z2,z3,z18,z5,z8]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z2,z3,z4,z5,z854]),(0,[z63,z1,z3,z4,z5,z244]),(0,[z1,z2,z4,z124,z5,z322]),(0,[z1,z2,z179,z4,z560,z8]),(0,[z855,z2,z3,z4,z5,z103])],[(0,[z1,z2,z728,z4,z5,z8]),(1,[z1,z2,z293,z5,z103]),(0,[z1,z856,z3,z4,z5,z8]),(0,[z857,z2,z3,z4,z5,z8])],[(0,[z858,z2,z3,z4,z5,z8]),(0,[z1,z323,z4,z5,z8,z170])],[(0,[z677,z1,z3,z26,z5,z8]),(0,[z1,z81,z3,z4,z5,z6]),(0,[z641,z1,z2,z4,z8,z54]),(0,[z859,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z8,z860,z54]),(0,[z1,z2,z4,z155,z8,z860]),(0,[z1,z2,z717,z4,z5,z267])],[(0,[z1,z2,z861,z4,z5,z8]),(0,[z1,z2,z3,z4,z862,z8]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z1,z2,z583,z4,z5,z103]),(0,[z1,z35,z123,z4,z5,z8]),(0,[z154,z2,z3,z4,z5,z205]),(0,[z1,z44,z143,z4,z5,z8]),(0,[z1,z2,z320,z4,z5,z281])],[(0,[z62,z2,z3,z4,z5,z229]),(0,[z864,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z2,z866,z4,z5,z8]),(0,[z76,z2,z3,z4,z5,z103]),(0,[z1,z867,z3,z4,z5,z8])],[(0,[z2,z50,z174,z4,z5,z103]),(0,[z237,z2,z174,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z869,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z16,z10]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z282,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z66,z5,z9]),(0,[z1,z2,z3,z4,z5,z871]),(0,[z77,z1,z2,z3,z5,z209])],[(0,[z172,z284,z174,z4,z5,z8]),(0,[z1,z2,z50,z4,z5,z103]),(0,[z172,z2,z174,z4,z5,z6]),(0,[z1,z872,z3,z4,z5,z8])]],
   [[(0,[z1,z74,z49,z4,z5,z103]),(0,[z614,z1,z2,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z2,z4,z155,z5,z322]),(0,[z1,z2,z467,z4,z5,z103])],[(0,[z1,z874,z3,z4,z5,z8]),(0,[z1,z875,z3,z4,z5,z8]),(0,[z162,z176,z3,z26,z5,z8]),(0,[z1,z2,z4,z597,z5,z103]),(0,[z1,z2,z4,z5,z876,z103]),(0,[z1,z877,z3,z4,z5,z103]),(0,[z878,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z879]),(0,[z152,z2,z3,z4,z5,z479]),(0,[z880,z2,z3,z4,z5,z8]),(0,[z19,z1,z2,z135,z5,z15])],[(0,[z1,z2,z3,z4,z5,z881]),(0,[z1,z3,z4,z5,z8,z170]),(0,[z1,z2,z882,z4,z5,z8]),(0,[z1,z2,z179,z4,z155,z8]),(0,[z1,z44,z320,z4,z5,z8])],[(0,[z57,z81,z3,z4,z5,z8]),(0,[z1,z321,z189,z4,z5,z8]),(0,[z1,z2,z3,z257,z5,z6]),(0,[z282,z1,z3,z4,z181,z5])],[(1,[z1,z2,z720,z4,z5]),(0,[z310,z2,z174,z4,z5,z8]),(0,[z1,z883,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z885,z3,z4,z5,z8]),(0,[z2,z3,z4,z8,z886,z13]),(0,[z1,z2,z123,z4,z5,z83]),(0,[z887,z2,z3,z4,z5,z8]),(0,[z1,z2,z41,z4,z5,z103]),(0,[z1,z2,z123,z293,z5,z8])],[(0,[z172,z241,z174,z4,z5,z8]),(0,[z1,z191,z3,z4,z457,z8]),(0,[z162,z1,z3,z888,z5,z8]),(0,[z1,z3,z137,z5,z8,z255]),(0,[z53,z154,z2,z4,z8,z54]),(0,[z659,z1,z2,z4,z5,z103]),(0,[z1,z2,z4,z5,z653,z103]),(0,[z1,z2,z3,z67,z8,z798])],[(0,[z1,z2,z4,z889,z5,z8]),(0,[z1,z284,z3,z4,z5,z11]),(0,[z1,z2,z890,z4,z5,z8]),(0,[z1,z379,z3,z4,z5,z6]),(0,[z1,z65,z2,z189,z4,z5]),(0,[z1,z2,z49,z4,z5,z380]),(0,[z891,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z160,z103]),(0,[z1,z2,z4,z5,z15,z103])]],
   [[(0,[z892,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z67,z195,z6]),(0,[z1,z2,z3,z4,z5,z850])],[(0,[z1,z893,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z894])],[(0,[z1,z2,z447,z4,z5,z103]),(0,[z60,z1,z49,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z895]),(0,[z19,z1,z35,z135,z5,z8]),(0,[z154,z2,z3,z257,z5,z8]),(0,[z725,z1,z2,z3,z4,z98])],[(0,[z1,z2,z3,z4,z5,z896]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z898,z3,z4,z5,z8]),(0,[z1,z899,z3,z4,z5,z8]),(0,[z1,z375,z3,z4,z5,z8]),(0,[z1,z900,z3,z4,z5,z8])],[(0,[z1,z2,z174,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z901]),(1,[z1,z3,z4,z5,z744]),(0,[z1,z2,z4,z451,z5,z103])],[(0,[z1,z2,z3,z4,z5,z902]),(0,[z1,z2,z453,z4,z5,z103]),(0,[z53,z1,z2,z4,z8,z370]),(0,[z97,z1,z2,z78,z4,z5])],[(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z2,z904,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z905]),(0,[z93,z2,z3,z4,z5,z103]),(0,[z1,z2,z179,z293,z5,z8])],[(1,[z746,z3,z4,z5,z8]),(0,[z202,z1,z2,z3,z4,z5]),(0,[z1,z2,z906,z3,z4,z5]),(0,[z1,z907,z3,z4,z5,z8]),(0,[z908,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z267,z103])]],
   [[(0,[z1,z2,z3,z5,z8,z909]),(0,[z1,z284,z3,z4,z5,z526]),(0,[z2,z174,z18,z4,z5,z103]),(0,[z53,z1,z2,z4,z5,z491])],[(0,[z2,z174,z4,z5,z424,z103]),(0,[z1,z2,z910,z4,z5,z8]),(0,[z176,z3,z4,z217,z5,z8]),(0,[z19,z1,z2,z4,z5,z876]),(0,[z1,z101,z3,z293,z5,z8]),(0,[z1,z3,z4,z5,z8,z911]),(0,[z623,z1,z3,z4,z5,z605]),(0,[z436,z1,z2,z3,z5,z85])],[(0,[z202,z2,z3,z4,z5,z105]),(0,[z1,z213,z3,z4,z5,z8]),(0,[z1,z912,z3,z4,z5,z8]),(0,[z1,z913,z3,z4,z5,z8]),(0,[z1,z107,z3,z4,z5,z103]),(0,[z1,z2,z3,z142,z5,z484]),(0,[z1,z2,z3,z142,z571,z5])],[(0,[z254,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z914,z5,z8]),(0,[z915,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z398])],[(0,[z1,z2,z720,z4,z5,z8]),(0,[z337,z2,z123,z4,z5,z8]),(1,[z725,z1,z2,z3,z4])],[(0,[z202,z1,z2,z846,z4,z5]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z189,z4,z5,z230]),(0,[z60,z111,z49,z4,z5,z8]),(0,[z917,z2,z3,z4,z5,z8]),(0,[z1,z3,z728,z4,z5,z8]),(0,[z212,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z918]),(0,[z202,z1,z2,z720,z4,z5]),(0,[z1,z2,z3,z4,z5,z919]),(0,[z1,z920,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z665,z103]),(0,[z97,z1,z2,z3,z448,z4]),(0,[z1,z2,z3,z4,z98,z540])],[(0,[z1,z59,z3,z4,z5,z103]),(0,[z64,z2,z3,z4,z5,z230]),(0,[z64,z2,z224,z3,z4,z5]),(0,[z111,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z3,z4,z5,z922]),(0,[z270,z176,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z103]),(0,[z556,z74,z3,z4,z5,z8]),(0,[z1,z2,z923,z4,z5,z8]),(0,[z924,z2,z3,z4,z5,z8]),(0,[z1,z925,z3,z4,z5,z8])],[(0,[z1,z2,z3,z926,z4,z5]),(0,[z57,z2,z50,z4,z5,z8]),(0,[z1,z23,z3,z4,z5,z6]),(0,[z261,z2,z3,z4,z5,z6]),(0,[z2,z927,z3,z4,z5,z8]),(0,[z19,z1,z2,z135,z5,z8]),(0,[z1,z928,z3,z4,z5,z103]),(0,[z1,z929,z3,z4,z5,z8])],[(0,[z2,z74,z174,z4,z5,z103]),(0,[z1,z930,z3,z4,z5,z8]),(0,[z2,z254,z3,z4,z5,z6]),(0,[z1,z2,z124,z5,z484,z103]),(0,[z303,z101,z3,z4,z5,z8]),(0,[z53,z1,z2,z4,z205,z54])],[(0,[z81,z3,z4,z17,z5,z8]),(0,[z1,z2,z3,z931,z5,z8]),(0,[z1,z2,z4,z5,z6,z534])],[(0,[z1,z2,z3,z4,z5,z932]),(0,[z131,z2,z3,z4,z6,z13]),(0,[z1,z2,z3,z4,z5,z933]),(0,[z1,z2,z4,z5,z767,z103]),(0,[z1,z2,z4,z5,z244,z103]),(0,[z43,z1,z2,z3,z6,z68])],[(0,[z934,z1,z2,z4,z5,z8]),(0,[z128,z1,z49,z4,z5,z8]),(0,[z1,z2,z935,z3,z4,z5]),(0,[z1,z2,z20,z124,z5,z8]),(0,[z43,z1,z2,z143,z8,z68])],[(0,[z1,z2,z3,z4,z5,z936]),(0,[z152,z2,z3,z4,z5,z380]),(0,[z623,z1,z49,z4,z5,z8]),(0,[z102,z375,z3,z4,z5,z8])],[(0,[z1,z937,z3,z4,z5,z8]),(0,[z938,z2,z3,z4,z5,z8]),(0,[z48,z2,z41,z4,z5,z8]),(0,[z1,z939,z3,z4,z5,z8]),(0,[z53,z1,z2,z4,z155,z103])]],
   [[(0,[z53,z1,z2,z4,z8,z860])],[(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z2,z3,z4,z941,z5]),(0,[z1,z2,z364,z4,z129,z5])],[(0,[z12,z2,z3,z4,z620,z8]),(0,[z111,z2,z3,z4,z5,z479]),(0,[z1,z2,z3,z4,z5,z942]),(0,[z1,z514,z3,z4,z5,z36]),(0,[z1,z2,z3,z4,z5,z943])],[(0,[z944,z1,z2,z4,z5,z8]),(0,[z1,z284,z3,z4,z5,z6]),(0,[z2,z174,z4,z5,z13,z103]),(0,[z1,z945,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z946]),(0,[z1,z2,z329,z4,z5,z166]),(0,[z469,z1,z2,z4,z5,z103]),(0,[z947,z2,z3,z4,z5,z8]),(0,[z43,z1,z3,z8,z170,z68])],[(0,[z1,z2,z948,z3,z5,z8]),(0,[z136,z3,z4,z5,z8,z170])],[(0,[z130,z2,z3,z18,z5,z6]),(0,[z949,z2,z3,z4,z5,z8]),(0,[z1,z107,z3,z4,z5,z406]),(0,[z53,z1,z2,z4,z5,z322])],[(0,[z1,z2,z3,z4,z5,z950]),(0,[z63,z1,z2,z189,z4,z5]),(0,[z1,z191,z49,z4,z5,z103]),(0,[z1,z89,z90,z4,z5,z83]),(0,[z162,z1,z3,z26,z5,z8]),(0,[z566,z1,z2,z4,z5,z103]),(0,[z102,z2,z3,z4,z5,z398])],[(0,[z215,z45,z3,z4,z5,z8]),(0,[z1,z951,z3,z4,z5,z8]),(0,[z12,z2,z174,z4,z5,z103]),(0,[z423,z2,z3,z17,z5,z8]),(0,[z1,z2,z952,z4,z5,z8]),(0,[z1,z2,z320,z67,z5,z8])]],
   [[(0,[z1,z2,z953,z4,z5,z8]),(0,[z176,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z4,z5,z491]),(0,[z337,z2,z3,z4,z5,z15]),(0,[z212,z2,z143,z4,z5,z8]),(0,[z97,z1,z2,z3,z4,z263])],[(0,[z1,z213,z203,z4,z5,z8]),(0,[z154,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z272,z5])],[(0,[z73,z74,z3,z4,z5,z103]),(0,[z1,z241,z3,z4,z5,z6]),(0,[z1,z954,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z8,z744]),(0,[z337,z2,z4,z5,z8,z103]),(0,[z1,z107,z3,z293,z5,z8]),(0,[z53,z1,z2,z293,z5,z103]),(0,[z185,z1,z2,z3,z448,z4])],[(0,[z1,z2,z3,z4,z5,z955]),(0,[z1,z2,z3,z4,z5,z956]),(0,[z337,z35,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z406]),(0,[z102,z2,z3,z4,z5,z103]),(0,[z1,z2,z193,z4,z5,z103]),(0,[z957,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z281]),(0,[z1,z2,z3,z4,z5,z958])],[(0,[z187,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z57,z2,z50,z4,z5,z343]),(0,[z1,z2,z189,z4,z5,z105]),(0,[z1,z960,z3,z4,z5,z8]),(0,[z961,z1,z3,z4,z5,z8]),(0,[z1,z962,z3,z4,z5,z8])],[(0,[z633,z45,z3,z4,z5,z8]),(0,[z1,z963,z3,z4,z5,z8]),(0,[z1,z2,z964,z4,z5,z8]),(0,[z62,z2,z3,z4,z5,z105]),(0,[z1,z965,z3,z4,z5,z8])],[(0,[z1,z2,z4,z5,z8,z966]),(0,[z1,z2,z3,z967,z5,z8]),(0,[z1,z2,z329,z4,z5,z6]),(0,[z1,z2,z4,z293,z5,z103])],[(0,[z172,z2,z760,z4,z5,z8]),(0,[z1,z2,z203,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z968]),(0,[z212,z2,z320,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z969,z5,z8]),(0,[z1,z2,z545,z4,z5,z103]),(0,[z1,z970,z3,z4,z5,z8]),(0,[z254,z3,z49,z4,z5,z8]),(0,[z1,z2,z4,z5,z178,z103]),(0,[z1,z2,z135,z5,z8,z239]),(0,[z53,z303,z2,z4,z8,z54])],[(0,[z1,z971,z3,z4,z5,z8]),(0,[z57,z59,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z972]),(0,[z973,z2,z3,z4,z5,z8]),(0,[z1,z2,z124,z5,z103,z68])],[(0,[z48,z2,z3,z4,z5,z8]),(0,[z237,z2,z3,z4,z5,z105]),(0,[z1,z44,z3,z4,z5,z8]),(0,[z641,z1,z2,z3,z8,z68])],[(0,[z57,z241,z3,z4,z5,z8]),(0,[z456,z1,z2,z4,z5,z103]),(0,[z1,z974,z3,z4,z5,z8]),(0,[z1,z191,z3,z4,z217,z103]),(0,[z1,z65,z3,z4,z5,z462])],[(0,[z1,z65,z297,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z479]),(0,[z1,z49,z4,z5,z462,z103]),(0,[z246,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z4,z8,z54])],[(0,[z58,z2,z174,z4,z5,z103]),(0,[z1,z975,z3,z4,z5,z8]),(0,[z58,z2,z3,z17,z5,z6]),(0,[z2,z3,z4,z782,z5,z8]),(0,[z1,z2,z3,z4,z5,z976]),(0,[z1,z2,z4,z5,z8,z977]),(0,[z1,z2,z4,z560,z5,z103]),(1,[z1,z2,z4,z5,z767]),(0,[z43,z1,z2,z3,z181,z68])],[(0,[z241,z3,z174,z4,z5,z8]),(0,[z1,z2,z189,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z491]),(0,[z1,z2,z4,z5,z229,z103]),(0,[z1,z2,z143,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z978])],[(0,[z202,z64,z2,z3,z4,z5]),(0,[z1,z2,z50,z4,z5,z11]),(0,[z58,z2,z3,z486,z5,z8]),(0,[z130,z81,z3,z4,z5,z8]),(0,[z1,z2,z979,z4,z5,z8]),(0,[z1,z2,z3,z980,z5,z8]),(0,[z2,z3,z4,z5,z8,z735]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z448,z4,z155,z103]),(0,[z1,z2,z4,z5,z8,z984])]],
   [[(0,[z1,z2,z985,z4,z5,z8]),(0,[z986,z2,z3,z4,z5,z8]),(0,[z19,z337,z2,z135,z5,z8]),(0,[z1,z987,z3,z4,z5,z8]),(0,[z988,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z729,z103]),(1,[z1,z2,z3,z5,z850])],[(0,[z989,z1,z2,z3,z4,z5]),(0,[z1,z191,z3,z4,z8,z811]),(0,[z19,z1,z2,z135,z5,z103]),(0,[z136,z2,z3,z4,z5,z103]),(0,[z2,z3,z4,z181,z5,z71])],[(0,[z1,z2,z3,z4,z5,z990]),(0,[z1,z321,z3,z4,z5,z8]),(0,[z202,z1,z65,z3,z4,z5]),(0,[z57,z2,z637,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z126]),(0,[z152,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z992,z2,z3,z4,z5,z8]),(0,[z1,z2,z323,z4,z5,z8]),(0,[z249,z1,z2,z4,z5,z103])],[(0,[z1,z2,z3,z4,z5,z993]),(0,[z2,z760,z174,z4,z5,z8]),(0,[z1,z2,z4,z575,z5,z103]),(0,[z2,z3,z18,z782,z5,z8]),(0,[z2,z3,z4,z5,z8,z886]),(0,[z1,z994,z3,z4,z5,z8]),(0,[z63,z76,z3,z4,z5,z33]),(0,[z1,z995,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z852,z103])],[(0,[z1,z2,z4,z577,z5,z103]),(0,[z996,z2,z3,z4,z5,z8]),(0,[z997,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z8,z998]),(0,[z1,z101,z3,z4,z5,z103])],[(0,[z19,z1,z2,z4,z5,z322]),(0,[z1,z2,z320,z4,z5,z6]),(0,[z1,z2,z364,z4,z5,z6]),(0,[z77,z1,z2,z78,z5,z85]),(0,[z1,z2,z3,z4,z5,z999])],[(0,[z111,z2,z3,z4,z5,z380]),(0,[z1,z2,z78,z4,z5,z103]),(0,[z1000,z2,z3,z4,z5,z8]),(0,[z102,z2,z3,z4,z5,z281]),(0,[z1,z2,z78,z4,z5,z85])],[(0,[z337,z2,z3,z4,z5,z8]),(0,[z554,z1,z2,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z3,z4,z217,z8,z811]),(0,[z759,z2,z3,z4,z5,z6]),(0,[z1002,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z3,z4,z5,z8,z1003]),(0,[z631,z1,z2,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z2,z3,z4,z5,z299]),(0,[z1,z2,z168,z3,z5,z351])],[(0,[z1,z2,z4,z588,z5,z103]),(0,[z1,z337,z2,z4,z5,z103]),(0,[z1,z2,z3,z357,z5,z9])],[(0,[z1005,z2,z3,z4,z5,z8]),(1,[z1,z107,z4,z5,z103])],[(0,[z1006,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1007,z5]),(0,[z1,z2,z1008,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z744]),(0,[z1,z2,z168,z124,z5,z8]),(0,[z1,z2,z123,z4,z5,z406]),(0,[z947,z2,z3,z4,z5,z103])],[(0,[z564,z74,z3,z4,z5,z8]),(0,[z1,z81,z3,z4,z5,z8]),(0,[z59,z3,z4,z17,z5,z8]),(0,[z62,z2,z203,z4,z5,z105]),(0,[z1,z2,z179,z4,z155,z119]),(0,[z1,z2,z948,z3,z5,z103])],[(0,[z131,z81,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1009]),(0,[z1010,z2,z3,z4,z5,z8]),(0,[z63,z48,z3,z4,z5,z33]),(0,[z102,z44,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z65,z3,z4,z5,z694]),(0,[z1,z2,z1012,z4,z5,z8]),(0,[z216,z1,z3,z4,z8,z196]),(0,[z345,z1,z2,z4,z5,z103]),(0,[z1,z2,z3,z4,z8,z860])],[(0,[z1,z1013,z3,z4,z5,z8]),(0,[z282,z1,z3,z4,z5,z8]),(0,[z1,z3,z1014,z4,z5,z8]),(0,[z1,z35,z3,z4,z5,z103]),(0,[z1,z107,z3,z257,z5,z8]),(0,[z53,z1,z2,z257,z5,z103]),(0,[z1,z2,z3,z4,z1015,z5])]],
   [[(0,[z0,z366,z3,z4,z5,z8]),(0,[z172,z2,z174,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z270,z1,z3,z4,z6,z196]),(0,[z97,z149,z1,z2,z418,z4])],[(0,[z1,z2,z3,z1017,z5,z8]),(0,[z1,z2,z1018,z4,z5,z8]),(0,[z623,z1,z3,z4,z5,z33]),(0,[z1019,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1020])],[(0,[z1,z2,z603,z4,z5,z103]),(0,[z1,z2,z1021,z4,z5,z8]),(0,[z1,z2,z50,z4,z5,z1022]),(0,[z136,z2,z3,z4,z272,z5]),(0,[z97,z149,z1,z2,z3,z4])],[(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z2,z3,z4,z5,z322]),(0,[z820,z1,z3,z4,z5,z103]),(0,[z1,z2,z418,z4,z5,z6]),(0,[z1,z2,z1024,z4,z5,z8])],[(0,[z1,z89,z165,z4,z5,z8]),(0,[z1,z2,z4,z5,z774,z103]),(0,[z1025,z2,z3,z4,z5,z8]),(0,[z1026,z2,z3,z4,z5,z8]),(0,[z1,z2,z1027,z4,z5,z8])],[(0,[z1,z2,z1028,z3,z4,z5]),(0,[z1,z65,z3,z4,z5,z744]),(0,[z1,z2,z3,z257,z5,z8]),(0,[z1,z2,z418,z4,z5,z406])],[(0,[z1,z1029,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z585,z1,z2,z4,z5,z103]),(0,[z1,z2,z143,z4,z5,z1031])],[(0,[z1,z1032,z3,z4,z5,z8]),(0,[z111,z89,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z101,z3,z4,z5,z406])]],
   [[(0,[z1,z379,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z11]),(0,[z57,z2,z622,z4,z5,z8]),(0,[z2,z3,z782,z17,z5,z8]),(0,[z1,z2,z3,z4,z5,z380]),(1,[z154,z2,z4,z5,z103]),(0,[z1,z2,z3,z293,z5,z103])],[(0,[z73,z746,z3,z4,z5,z8]),(0,[z1,z241,z3,z4,z5,z11]),(0,[z1,z2,z1034,z4,z5,z8]),(0,[z1,z321,z203,z4,z5,z8]),(0,[z1,z89,z90,z4,z5,z103]),(0,[z1,z2,z3,z888,z5,z8]),(0,[z76,z2,z3,z4,z5,z6]),(0,[z19,z1,z514,z4,z5,z103])],[(0,[z1,z2,z1035,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z213,z3,z4,z5,z8,z105]),(1,[z1,z2,z3,z8,z798])],[(0,[z1,z2,z3,z1037,z5,z8]),(0,[z97,z149,z1,z2,z364,z4])],[(0,[z1,z2,z354,z4,z5,z6]),(0,[z2,z839,z3,z4,z5,z103]),(0,[z663,z1,z2,z4,z5,z103])],[(0,[z2,z3,z4,z5,z230,z735]),(0,[z1,z2,z3,z5,z850,z85])],[(0,[z746,z74,z3,z4,z5,z8]),(0,[z1038,z2,z3,z4,z5,z8]),(0,[z1039,z2,z3,z4,z5,z8]),(0,[z2,z1040,z3,z4,z5,z8])],[(0,[z1,z2,z4,z5,z1022,z103]),(0,[z1,z2,z1041,z4,z5,z8]),(0,[z1,z2,z4,z5,z8,z767]),(0,[z1,z1042,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z170])]],
   [[(0,[z0,z45,z3,z4,z5,z103]),(0,[z1,z2,z760,z4,z5,z8]),(0,[z2,z3,z4,z5,z1043,z8])],[(0,[z1,z2,z635,z4,z5,z103]),(0,[z202,z1,z213,z3,z4,z5]),(0,[z1,z45,z49,z4,z5,z103]),(0,[z1,z2,z329,z4,z5,z33]),(0,[z1,z2,z41,z4,z5,z6]),(0,[z1,z1044,z3,z4,z5,z8]),(0,[z303,z2,z3,z4,z5,z103]),(0,[z1,z2,z4,z5,z6,z664])],[(0,[z1,z2,z3,z4,z5,z1045]),(0,[z1046,z1,z2,z3,z4,z5]),(0,[z1,z241,z3,z4,z5,z526]),(0,[z1,z2,z3,z4,z1047,z8]),(0,[z1,z2,z1048,z4,z5,z8]),(0,[z1049,z2,z3,z4,z5,z8]),(0,[z1,z2,z639,z4,z5,z103])],[(0,[z194,z1,z49,z4,z5,z8]),(0,[z1,z2,z329,z4,z5,z178]),(0,[z1,z2,z779,z3,z5,z8]),(0,[z136,z2,z323,z4,z5,z8])],[(0,[z1,z2,z3,z720,z4,z5]),(0,[z1,z2,z3,z4,z1050,z8]),(0,[z471,z1,z49,z4,z5,z8]),(0,[z723,z2,z3,z4,z5,z8]),(0,[z76,z2,z329,z4,z5,z8]),(1,[z1,z2,z779,z5,z8]),(0,[z1,z1051,z3,z4,z5,z8])],[(0,[z154,z2,z4,z5,z8,z103])],[(0,[z212,z2,z3,z4,z5,z8]),(0,[z334,z1,z3,z4,z8,z196]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z730,z3,z4,z5,z8]),(0,[z1,z2,z168,z3,z5,z85]),(0,[z1,z2,z4,z5,z8,z1053])],[(0,[z1,z2,z3,z4,z5,z1054]),(0,[z1055,z2,z3,z4,z5,z8]),(0,[z642,z1,z2,z4,z5,z103]),(0,[z1056,z2,z3,z4,z5,z8])]],
   [[(0,[z202,z73,z74,z3,z4,z5]),(0,[z131,z2,z3,z4,z8,z638]),(0,[z1,z2,z3,z4,z5,z1057]),(0,[z176,z89,z3,z4,z5,z8]),(0,[z1,z2,z779,z124,z5,z8]),(0,[z1,z2,z4,z5,z8,z267]),(0,[z1,z3,z4,z181,z5,z170])],[(0,[z1,z2,z3,z4,z5,z1058]),(0,[z237,z2,z174,z4,z5,z103]),(0,[z191,z254,z3,z4,z217,z8])],[(0,[z1,z23,z3,z4,z5,z8]),(0,[z261,z2,z3,z4,z5,z8]),(0,[z1,z2,z90,z4,z5,z103]),(0,[z1,z2,z1059,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z876]),(0,[z1060,z2,z3,z4,z5,z8]),(0,[z93,z2,z3,z4,z5,z6]),(0,[z1,z2,z439,z4,z5,z6])],[(0,[z2,z254,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1022]),(0,[z1061,z2,z3,z4,z5,z8]),(0,[z76,z3,z4,z5,z8,z33]),(0,[z1,z2,z78,z4,z98,z5])],[(0,[z1,z2,z3,z4,z5,z1062]),(0,[z1,z1063,z3,z4,z5,z8]),(0,[z1,z89,z567,z4,z5,z8]),(0,[z1,z2,z4,z5,z6,z546])],[(0,[z301,z2,z3,z4,z5,z86]),(0,[z1,z44,z3,z4,z5,z281]),(0,[z1,z2,z3,z4,z8,z798]),(0,[z1,z2,z1064,z4,z5,z8]),(0,[z283,z149,z1,z2,z3,z4]),(0,[z149,z725,z1,z2,z3,z4])],[(0,[z1065,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z1066,z5,z8]),(0,[z128,z1,z2,z4,z5,z103]),(0,[z1,z107,z3,z4,z5,z6]),(0,[z1,z2,z179,z4,z155,z103])],[(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z2,z179,z4,z8,z860])]],
   [[],[(0,[z0,z746,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1068]),(0,[z270,z1,z3,z4,z8,z811]),(0,[z1,z180,z3,z4,z5,z166]),(0,[z1,z2,z3,z5,z1069,z103]),(0,[z1,z375,z3,z4,z5,z398]),(0,[z1,z2,z1070,z4,z5,z8])],[(0,[z1,z2,z437,z4,z5,z103]),(0,[z176,z3,z4,z26,z5,z8]),(0,[z1,z2,z1071,z4,z5,z8]),(0,[z1072,z2,z3,z4,z5,z8]),(0,[z1,z2,z143,z4,z5,z1073]),(0,[z136,z282,z3,z4,z5,z8])],[(0,[z1,z59,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z65,z3,z4,z5,z166])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z284,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1075,z8]),(0,[z63,z1,z3,z4,z5,z744]),(0,[z1,z514,z3,z4,z5,z15]),(0,[z154,z107,z3,z4,z5,z8]),(0,[z303,z2,z3,z4,z5,z406]),(0,[z53,z1,z2,z293,z8,z54]),(0,[z1,z2,z3,z4,z129,z540])],[(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z2,z503,z4,z5,z6]),(0,[z60,z1,z49,z4,z5,z103])],[(0,[z1,z2,z4,z5,z343,z103]),(0,[z130,z2,z3,z18,z5,z8]),(0,[z58,z23,z3,z17,z5,z8]),(0,[z1,z2,z4,z673,z5,z103]),(0,[z1,z3,z888,z26,z5,z8]),(0,[z1,z1077,z3,z4,z5,z8]),(0,[z1,z375,z3,z4,z5,z103])],[(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z1079,z3,z4,z5,z8]),(0,[z1,z2,z4,z681,z5,z103]),(0,[z25,z254,z3,z4,z5,z8]),(1,[z1,z35,z4,z5,z103]),(0,[z1,z2,z323,z4,z5,z823]),(0,[z1,z2,z3,z4,z5,z1080])]],
   [[(0,[z1,z2,z4,z686,z5,z103]),(0,[z1,z1081,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1082]),(0,[z202,z1,z3,z4,z5,z33]),(0,[z483,z2,z3,z4,z8,z13]),(0,[z303,z2,z3,z293,z5,z8]),(0,[z1,z101,z3,z257,z5,z8]),(0,[z1,z2,z307,z4,z5,z6]),(0,[z1,z2,z1083,z4,z5,z8])],[(0,[z264,z74,z3,z4,z5,z8]),(0,[z154,z2,z3,z4,z5,z8]),(0,[z1,z1084,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z8,z886]),(0,[z1,z2,z323,z293,z5,z8]),(0,[z1,z2,z3,z4,z181,z5]),(0,[z1,z1085,z3,z4,z5,z8])],[(0,[z1,z2,z1086,z4,z5,z8]),(0,[z1,z241,z3,z4,z5,z8]),(0,[z705,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z131,z2,z3,z4,z8,z886]),(0,[z310,z1,z2,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z1088]),(0,[z1089,z2,z3,z4,z5,z8]),(0,[z1,z2,z1090,z4,z5,z8]),(0,[z53,z1,z107,z4,z5,z103]),(0,[z1,z2,z3,z142,z5,z9])],[(0,[z697,z74,z3,z4,z5,z8]),(0,[z58,z2,z3,z466,z5,z8]),(0,[z1091,z2,z3,z4,z5,z8]),(0,[z957,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z1092]),(0,[z1093,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z43,z1,z2,z323,z8,z68])],[(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1,z2,z3,z4,z1096,z8]),(0,[z1,z213,z3,z4,z5,z103]),(0,[z1097,z2,z3,z4,z5,z8]),(0,[z1,z2,z262,z4,z5,z103]),(0,[z1,z2,z3,z4,z1098,z5]),(0,[z53,z1,z2,z4,z8,z624])],[(0,[z73,z327,z74,z3,z4,z5]),(0,[z1,z2,z3,z1099,z5,z8]),(0,[z111,z3,z49,z4,z5,z8]),(0,[z641,z1,z2,z4,z5,z103]),(0,[z21,z1,z2,z4,z5,z103]),(0,[z789,z2,z3,z4,z5,z8]),(0,[z1,z2,z364,z4,z5,z9])],[(0,[z59,z3,z174,z4,z5,z8]),(0,[z1,z2,z329,z4,z5,z8]),(0,[z1100,z2,z3,z4,z5,z8]),(0,[z1,z1101,z3,z4,z5,z8])]],
   [[(0,[z147,z74,z3,z4,z5,z8]),(0,[z353,z45,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1102]),(0,[z1103,z1,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z1104]),(0,[z1105,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1106])],[(0,[z1,z1107,z3,z4,z5,z8]),(0,[z93,z514,z3,z4,z5,z8]),(0,[z1,z2,z107,z4,z5,z103]),(0,[z2,z4,z5,z8,z267,z71])],[(0,[z74,z3,z603,z4,z5,z8]),(0,[z1,z2,z1108,z4,z5,z8]),(0,[z1,z3,z4,z217,z8,z113]),(0,[z1,z1109,z3,z4,z5,z8])],[(0,[z2,z3,z4,z5,z8,z1110]),(0,[z2,z1111,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z1112])],[(0,[z57,z2,z50,z4,z5,z103]),(0,[z1,z1113,z3,z4,z5,z8]),(0,[z1,z2,z478,z4,z5,z103]),(0,[z1,z107,z3,z4,z5,z205]),(0,[z1114,z2,z3,z4,z5,z8]),(0,[z1,z2,z1115,z4,z5,z8]),(0,[z97,z725,z1,z2,z3,z4])],[(0,[z246,z2,z3,z4,z5,z8]),(0,[z677,z2,z3,z17,z5,z8]),(0,[z58,z59,z3,z17,z5,z8]),(0,[z1,z2,z3,z4,z5,z91]),(0,[z1,z2,z1116,z4,z5,z8]),(0,[z261,z191,z3,z4,z217,z8]),(0,[z43,z1,z44,z3,z8,z68]),(0,[z1,z1117,z3,z4,z5,z8]),(0,[z1,z2,z3,z195,z8,z798]),(0,[z1,z1118,z3,z4,z5,z8])],[(0,[z73,z74,z3,z4,z5,z6]),(0,[z45,z746,z3,z4,z5,z8]),(0,[z58,z2,z3,z17,z5,z8]),(0,[z1119,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z103,z239]),(0,[z1,z1120,z3,z4,z5,z8])],[(0,[z1121,z1,z2,z3,z4,z5]),(0,[z1,z2,z189,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z143,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1123]),(0,[z104,z2,z3,z4,z5,z229]),(0,[z102,z2,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z5,z42]),(0,[z1,z2,z193,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1124])]],
   [[(0,[z1125,z2,z3,z4,z5,z8]),(0,[z1,z2,z20,z124,z5,z103]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1,z2,z3,z4,z98,z352])],[(0,[z0,z169,z3,z4,z5,z8]),(0,[z1127,z1,z3,z4,z5,z8]),(0,[z1128,z1,z3,z4,z5,z8]),(0,[z623,z1,z49,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z1129]),(0,[z1,z1130,z3,z4,z5,z8]),(0,[z19,z1,z2,z304,z5,z8]),(0,[z1,z375,z3,z4,z5,z281]),(0,[z136,z2,z4,z5,z8,z267])],[(0,[z74,z3,z4,z5,z8,z460]),(0,[z2,z50,z760,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1131]),(0,[z1,z2,z1132,z4,z5,z8]),(1,[z2,z3,z782,z5,z8]),(0,[z1,z2,z4,z31,z5,z103]),(0,[z63,z1,z329,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z205]),(0,[z1,z2,z4,z38,z5,z103])],[(0,[z152,z2,z3,z4,z5,z8]),(0,[z584,z74,z3,z4,z5,z8]),(0,[z1,z2,z452,z4,z5,z103]),(0,[z1,z2,z203,z4,z5,z6]),(0,[z1,z514,z3,z4,z5,z8]),(0,[z1,z35,z3,z4,z5,z36]),(0,[z1133,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1134]),(0,[z1,z2,z46,z4,z5,z103]),(0,[z162,z1,z49,z4,z5,z103]),(0,[z1,z2,z123,z4,z5,z6]),(0,[z43,z1,z375,z3,z8,z68]),(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z2,z4,z272,z5,z267])],[(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z3,z4,z5,z343]),(0,[z553,z2,z3,z4,z8,z13]),(0,[z2,z3,z1136,z4,z5,z8]),(0,[z251,z1,z2,z4,z5,z103]),(0,[z1,z2,z3,z1137,z5,z8]),(0,[z19,z93,z2,z4,z5,z103]),(0,[z2,z3,z4,z5,z1138,z103]),(0,[z1139,z2,z3,z4,z5,z8]),(0,[z43,z2,z3,z8,z71,z68])],[(0,[z89,z254,z3,z4,z5,z8]),(0,[z176,z25,z3,z4,z5,z8]),(0,[z1,z2,z1140,z4,z5,z8]),(0,[z1,z2,z320,z4,z5,z8]),(0,[z1,z2,z364,z4,z5,z8]),(0,[z1,z2,z1141,z4,z5,z8]),(0,[z1,z1142,z3,z4,z5,z8]),(0,[z77,z1,z2,z3,z5,z850])],[(0,[z1,z2,z3,z4,z5,z1143]),(0,[z1,z3,z4,z5,z8,z1144]),(0,[z58,z2,z3,z782,z5,z8]),(0,[z176,z3,z49,z4,z5,z8]),(0,[z1,z2,z3,z1145,z5,z8]),(0,[z1,z191,z3,z4,z217,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z774]),(0,[z53,z1,z2,z4,z6,z54])],[(0,[z1,z65,z213,z3,z4,z5]),(0,[z60,z1,z49,z4,z5,z479]),(0,[z589,z1,z2,z4,z5,z103]),(0,[z162,z1,z3,z26,z5,z103]),(0,[z1,z2,z3,z67,z701,z8]),(0,[z282,z1,z323,z4,z5,z8])],[(0,[z1,z2,z3,z1146,z5,z8]),(0,[z74,z3,z4,z636,z5,z8]),(0,[z202,z76,z2,z3,z4,z5]),(0,[z0,z2,z174,z4,z5,z103]),(0,[z1,z3,z4,z5,z8,z1147]),(0,[z62,z213,z3,z4,z5,z105]),(0,[z154,z2,z123,z4,z5,z8]),(0,[z1,z2,z4,z155,z5,z103]),(0,[z53,z1,z2,z4,z406,z54])],[(0,[z190,z45,z3,z4,z5,z8])],[(0,[z1148,z1,z2,z3,z5,z8]),(0,[z1,z2,z4,z5,z86,z103]),(0,[z1,z2,z1149,z4,z5,z8]),(0,[z1,z2,z779,z20,z5,z8]),(0,[z1,z2,z293,z5,z8,z103]),(0,[z43,z212,z2,z3,z8,z68])],[(0,[z64,z65,z74,z3,z4,z5]),(0,[z1,z2,z4,z5,z532,z103]),(0,[z1,z2,z95,z4,z5,z103]),(0,[z1,z2,z1150,z4,z5,z8]),(0,[z1,z2,z1151,z4,z5,z8]),(0,[z1152,z2,z3,z4,z5,z8]),(0,[z93,z2,z3,z4,z5,z36]),(0,[z19,z1,z2,z135,z5,z6]),(0,[z136,z2,z3,z4,z5,z6])],[(0,[z216,z1,z2,z4,z5,z103]),(0,[z1,z3,z4,z888,z5,z8]),(0,[z1,z2,z3,z4,z5,z1153]),(0,[z303,z2,z3,z257,z5,z8])],[(0,[z274,z74,z3,z4,z5,z8]),(0,[z1154,z2,z3,z4,z5,z8]),(0,[z1,z960,z3,z4,z5,z103])]],
   [[(0,[z1155,z2,z3,z4,z5,z8]),(0,[z504,z1,z3,z26,z5,z8]),(0,[z1,z2,z1156,z3,z4,z5]),(0,[z1,z101,z3,z4,z5,z6]),(0,[z1,z44,z3,z4,z5,z398])],[(0,[z1,z2,z174,z4,z5,z103]),(0,[z81,z3,z174,z4,z5,z8]),(0,[z1157,z2,z3,z4,z5,z8]),(0,[z1158,z2,z3,z4,z5,z8]),(0,[z1159,z2,z3,z4,z5,z8])],[(0,[z270,z1,z3,z4,z196,z103]),(0,[z1,z2,z3,z4,z5,z1160]),(0,[z1,z2,z3,z1161,z5,z8]),(0,[z1,z2,z3,z5,z8,z1069]),(0,[z1,z2,z78,z4,z5,z6])],[(0,[z1,z2,z4,z5,z83,z103]),(0,[z1,z2,z3,z4,z1162,z5]),(0,[z2,z3,z4,z5,z8,z1138]),(0,[z136,z2,z3,z4,z181,z5]),(0,[z1,z2,z3,z142,z5,z850])],[(0,[z1,z2,z117,z4,z5,z103]),(0,[z1,z2,z1163,z4,z5,z8]),(0,[z19,z93,z2,z135,z5,z8]),(0,[z53,z1,z101,z4,z5,z103]),(0,[z1,z2,z418,z4,z5,z8]),(0,[z1164,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z16,z542]),(0,[z1,z2,z3,z67,z195,z8]),(0,[z2,z1165,z3,z4,z5,z8])],[(0,[z672,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1166,z8]),(0,[z301,z2,z3,z4,z5,z230]),(0,[z1167,z2,z3,z4,z5,z8]),(0,[z48,z2,z3,z4,z5,z103]),(0,[z855,z2,z3,z4,z5,z8]),(0,[z1,z44,z3,z4,z5,z103]),(0,[z1,z2,z320,z5,z8,z68])],[(0,[z1,z3,z4,z5,z8,z811]),(0,[z19,z1,z2,z124,z5,z103]),(0,[z154,z101,z3,z4,z5,z8]),(0,[z232,z1,z2,z4,z5,z103]),(0,[z77,z1,z2,z3,z5,z85])],[(0,[z687,z2,z50,z4,z5,z8]),(1,[z2,z3,z4,z5,z735]),(0,[z60,z1,z728,z4,z5,z8]),(0,[z1168,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z36]),(0,[z278,z2,z3,z4,z5,z424]),(0,[z1169,z2,z3,z4,z5,z8]),(0,[z1,z1170,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z9,z850])]],
   [[(0,[z1,z2,z327,z3,z4,z5]),(0,[z1,z2,z1171,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1172]),(0,[z1,z1173,z3,z4,z5,z8])],[(0,[z2,z3,z4,z5,z8,z71])],[(0,[z76,z2,z3,z4,z5,z8]),(0,[z1174,z2,z3,z4,z5,z8]),(0,[z43,z282,z1,z3,z8,z68]),(0,[z725,z1,z2,z3,z4,z10])],[(0,[z1,z2,z1175,z3,z4,z5]),(0,[z1,z2,z476,z4,z5,z103]),(0,[z1176,z2,z3,z4,z5,z8]),(0,[z1,z35,z3,z4,z5,z6]),(0,[z1,z2,z293,z5,z8,z54]),(0,[z1,z2,z4,z5,z8,z860]),(0,[z53,z1,z2,z4,z5,z729]),(0,[z1,z2,z1177,z4,z5,z8])],[(0,[z312,z74,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z526]),(0,[z1,z2,z3,z4,z5,z1178]),(0,[z1,z2,z203,z4,z5,z343]),(0,[z1,z2,z1179,z4,z5,z8]),(0,[z64,z2,z3,z4,z5,z424]),(0,[z1,z2,z3,z1180,z5,z8]),(0,[z1181,z2,z3,z4,z5,z8]),(0,[z1,z1182,z3,z4,z5,z8]),(0,[z2,z1183,z3,z4,z5,z8])],[(0,[z1,z2,z3,z1184,z5,z8]),(0,[z0,z434,z3,z4,z5,z8]),(0,[z1,z2,z151,z4,z5,z103]),(0,[z553,z1,z2,z4,z5,z103]),(0,[z1,z2,z123,z4,z5,z343]),(0,[z1,z321,z3,z4,z5,z103]),(1,[z337,z2,z4,z5,z103]),(0,[z1,z2,z323,z4,z5,z103]),(0,[z1,z2,z1185,z4,z5,z8]),(0,[z43,z1,z2,z3,z8,z798])],[(0,[z1,z2,z20,z124,z5,z491]),(0,[z1,z877,z3,z4,z5,z8])],[(0,[z1,z2,z1186,z4,z5,z8])]],
   [[(0,[z1,z1042,z3,z4,z5,z8]),(0,[z1,z728,z49,z4,z5,z8]),(0,[z1,z2,z135,z323,z5,z8]),(0,[z2,z3,z4,z5,z103,z1104]),(0,[z1,z2,z207,z3,z5,z484]),(0,[z1,z2,z3,z4,z5,z1073]),(0,[z1,z2,z1187,z4,z5,z8]),(0,[z1,z4,z5,z8,z267,z170])],[(0,[z1127,z1,z3,z4,z5,z103]),(0,[z1,z180,z3,z4,z5,z178]),(0,[z1,z2,z3,z8,z798,z68])],[(0,[z1,z161,z3,z4,z217,z8]),(0,[z1,z2,z171,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z1188]),(0,[z1,z2,z41,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1189]),(0,[z1,z2,z177,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z1190]),(0,[z337,z2,z3,z4,z5,z103])],[(0,[z111,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z175,z5,z103]),(0,[z1,z514,z3,z4,z5,z103]),(0,[z19,z1,z514,z135,z5,z8]),(0,[z1,z2,z4,z5,z355,z103])],[(0,[z76,z65,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z744,z33]),(0,[z19,z1,z2,z28,z5,z8]),(0,[z1,z2,z3,z293,z5,z6]),(0,[z1,z2,z123,z4,z5,z767]),(0,[z231,z1,z3,z4,z5,z244]),(0,[z1,z2,z320,z4,z5,z777]),(0,[z43,z1,z2,z3,z398,z68]),(0,[z3,z4,z5,z8,z170,z71])],[(0,[z62,z76,z2,z3,z4,z5]),(0,[z60,z1,z49,z4,z5,z380]),(0,[z1,z89,z728,z4,z5,z8]),(0,[z1,z89,z90,z4,z5,z6]),(0,[z471,z1,z2,z4,z5,z103]),(0,[z1191,z2,z3,z4,z5,z8]),(0,[z19,z1,z2,z779,z5,z8]),(0,[z1,z2,z135,z293,z5,z8]),(0,[z1,z1192,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z1193]),(0,[z1139,z2,z3,z4,z5,z103])],[(0,[z64,z76,z2,z3,z4,z5]),(0,[z1,z2,z168,z124,z5,z103]),(0,[z1,z2,z35,z4,z5,z103]),(0,[z1,z101,z3,z4,z5,z205]),(0,[z1,z2,z3,z293,z5,z406])],[(0,[z130,z59,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1194]),(0,[z1,z81,z3,z4,z5,z103])]],
   [[(0,[z63,z1,z213,z3,z4,z5]),(0,[z1,z2,z20,z124,z5,z299])],[(0,[z1,z2,z3,z4,z5,z1195]),(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z2,z3,z4,z5,z1197]),(0,[z1,z2,z4,z5,z192,z103])],[(0,[z154,z2,z3,z293,z5,z8]),(0,[z282,z1,z3,z4,z5,z103])],[(0,[z93,z2,z3,z4,z5,z8]),(0,[z172,z2,z174,z4,z5,z103]),(0,[z270,z254,z3,z4,z5,z8]),(1,[z1,z3,z4,z8,z811]),(0,[z1,z2,z3,z4,z5,z1198]),(0,[z1,z2,z4,z5,z6,z767])],[(0,[z396,z74,z3,z4,z5,z8]),(0,[z0,z45,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1199]),(1,[z1,z2,z4,z8,z860]),(0,[z1,z2,z422,z4,z5,z103])],[(0,[z1200,z1,z2,z3,z4,z5]),(0,[z1201,z2,z3,z4,z5,z8]),(0,[z63,z1,z41,z4,z5,z33]),(0,[z576,z1,z2,z4,z5,z103]),(0,[z303,z2,z3,z4,z5,z6]),(0,[z1,z1202,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1203])],[(0,[z1,z2,z3,z4,z5,z1204]),(0,[z1,z2,z1205,z4,z5,z8]),(0,[z1,z2,z4,z5,z596,z103]),(0,[z1,z2,z135,z779,z5,z8]),(0,[z1,z2,z323,z4,z272,z5])],[(0,[z1,z107,z3,z4,z5,z8]),(0,[z1,z1206,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z103,z1144])]],
   [[(0,[z1,z1207,z3,z4,z5,z8]),(0,[z1,z2,z3,z257,z5,z103])],[(0,[z1,z2,z323,z4,z5,z1080])],[(0,[z1,z2,z1208,z4,z5,z8]),(0,[z1,z1209,z3,z4,z5,z8]),(0,[z62,z321,z3,z4,z5,z105]),(0,[z1210,z2,z3,z4,z5,z8])],[(0,[z1,z746,z3,z4,z5,z8]),(0,[z0,z559,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1211]),(0,[z1,z379,z3,z4,z5,z103]),(0,[z1,z3,z4,z8,z811,z196]),(0,[z43,z102,z2,z3,z8,z68]),(0,[z1,z2,z320,z4,z5,z812])],[(0,[z176,z2,z3,z4,z5,z8]),(0,[z1,z59,z3,z4,z5,z8]),(0,[z12,z2,z3,z4,z520,z8]),(0,[z62,z1,z2,z329,z4,z5]),(0,[z1,z2,z1212,z4,z5,z8]),(0,[z1213,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z67,z195,z103]),(0,[z1,z2,z4,z5,z6,z267]),(0,[z212,z375,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z1214,z5,z8]),(0,[z131,z59,z3,z4,z5,z8]),(0,[z64,z1,z2,z329,z4,z5]),(0,[z53,z1,z107,z4,z8,z54]),(0,[z1,z1215,z3,z4,z5,z8]),(0,[z1216,z2,z3,z4,z5,z8])],[(0,[z1,z89,z90,z4,z5,z91]),(0,[z1,z2,z3,z4,z5,z1217]),(0,[z1,z2,z3,z4,z5,z1218]),(0,[z1219,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z4,z5,z15]),(0,[z1,z928,z3,z4,z5,z8]),(0,[z1,z872,z3,z4,z5,z6])],[(0,[z237,z2,z3,z4,z5,z477]),(0,[z1,z2,z3,z4,z5,z1220])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 518) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 518).take 516) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1034).take 224) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1258)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [518, 516, 224] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 90).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 181).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [90, 91, 75] = true :=
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

end PEqualNP.Outside.L_meta_38545

theorem PEqualNP.Outside.L_meta_38545 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008224936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008224936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38545.solve