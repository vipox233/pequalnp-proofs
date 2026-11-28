import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40529

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276658336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000110828430b550#64 ++ 0x4000110828430b55#64 ++ 0xe04f318f8471ffff#64 ++ 0xae04f318f8471fff#64 : BitVec 256),
   (0x1094563645865ccc#64 ++ 0x81094563645865cc#64 ++ 0xb1b4de76478e7ccf#64 ++ 0x7b1b4de76478e7cc#64 : BitVec 256),
   (0x0628e058580b0aa9#64 ++ 0x00628e058580b0aa#64 ++ 0xee38e078780f8ffe#64 ++ 0xfee38e078780f8ff#64 : BitVec 256),
   (0x4b40fb806ed00f0e#64 ++ 0x04b40fb806ed00f0#64 ++ 0x5fc0ff807ff00f0d#64 ++ 0xf5fc0ff807ff00f0#64 : BitVec 256),
   (0x2dff0000336de000#64 ++ 0x02dff0000336de00#64 ++ 0x6fff00007ffff00b#64 ++ 0xf6fff00007ffff00#64 : BitVec 256),
   (0x8ffead6d00000000#64 ++ 0x08ffead6d0000000#64 ++ 0x9fffffff80000007#64 ++ 0xe9fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe04f318f8471ffff 0xae04f318f8471fff

def z1 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee38e078780f8ffe 0xfee38e078780f8ff

def z2 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4de76478e7ccf 0x7b1b4de76478e7cc

def z3 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff00007ffff00b 0xf6fff00007ffff00

def z4 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z5 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x11c71f8780000001 0x011c71f878000000

def z6 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1fb0ce7000000000 0x41fb0ce700000000

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x20300000400e000a 0x720300000400e000

def z8 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fffffff80000007 0xe9fffffff8000000

def z9 : W := mkw 0xc200ffed4c900f0e 0x0c200ffed4c900f0 0x9000ffff80000f04 0x09000ffff80000f0

def z10 : W := mkw 0x400052806ed00f0e 0x0400052806ed00f0 0x400000007ff00f08 0x1400000007ff00f0

def z11 : W := mkw 0x84be046d00000000 0x084be046d0000000 0x803f007f80000002 0x0803f007f8000000

def z12 : W := mkw 0x0094042400000000 0x0009404240000000 0x91b4de7600000007 0x691b4de760000000

def z13 : W := mkw 0x2dff0424336de000 0x02dff0424336de00 0xffffde767ffff00f 0xfffffde767ffff00

def z14 : W := mkw 0xafffad6d112de000 0x0afffad6d112de00 0xbfffffff800ff007 0xebfffffff800ff00

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000200000000f0c 0xa4000200000000f0

def z16 : W := mkw 0x0628a04818090221 0x00628a0481809022 0x0e00000038000000 0x00e0000003800000

def z17 : W := mkw 0x0200a00008000200 0x00200a0000800020 0x4e00200038000300 0x84e0020003800030

def z18 : W := mkw 0x0200e05848020aa9 0x00200e05848020aa 0x8000e07800000ff4 0x08000e07800000ff

def z19 : W := mkw 0x0428000010090000 0x0042800001009000 0x6e380000780f800a 0xf6e380000780f800

def z20 : W := mkw 0x0000000010090000 0x0000000001009000 0x60000000780f8008 0x160000000780f800

def z21 : W := mkw 0x04280058100b00a1 0x004280058100b00a 0xa0380078000f80f2 0x0a0380078000f80f

def z22 : W := mkw 0x49401b8026d00506 0x049401b8026d0050 0x11c01f8007f00001 0x011c01f8007f0000

def z23 : W := mkw 0x0940000022400000 0x0094000002240000 0x4fc000007ff00009 0xf4fc000007ff0000

def z24 : W := mkw 0xaffead6d334d4000 0x0affead6d334d400 0x1fb0ce707b8e0000 0x51fb0ce707b8e000

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0xe008200800018ffe 0xae008200800018ff

def z26 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x1fc0df807ff00001 0x51fc0df807ff0000

def z27 : W := mkw 0x109456b645965dcc 0x8109456b645965dc 0xf1f4fff647fe7fcf 0xff1f4fff647fe7fc

def z28 : W := mkw 0x0000401040020888 0x0000040104002088 0xa030c070400e0cce 0x7a030c070400e0cc

def z29 : W := mkw 0x1094162605845444 0x8109416260584544 0x11841e0607807001 0x011841e060780700

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x0047118780000001 0x0004711878000000

def z31 : W := mkw 0x2dfe0000334d4000 0x02dfe0000334d400 0x2fb400007f8e700b 0x72fb400007f8e700

def z32 : W := mkw 0x8200ad6d00000000 0x08200ad6d0000000 0x9000ffff80000004 0x09000ffff8000000

def z33 : W := mkw 0x4b40a9802a500302 0x04b40a9802a50030 0x4e40218038700300 0x84e4021803870030

def z34 : W := mkw 0x5bd4ffb66fd65fce 0x85bd4ffb66fd65fc 0xfff4fff67ffe7fcf 0xffff4fff67ffe7fc

def z35 : W := mkw 0x0f68e0587a4b0aa9 0x00f68e0587a4b0aa 0xeff8e0787fff8fff 0xfeff8e0787fff8ff

def z36 : W := mkw 0xcffeffed6ed00f0e 0x0cffeffed6ed00f0 0xdffffffffff00f0f 0xfdffffffffff00f0

def z37 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x11b4de76478e7001 0x511b4de76478e700

def z38 : W := mkw 0x400042006ac00a0e 0x0400042006ac00a0 0x000000007b800000 0x1000000007b80000

def z39 : W := mkw 0x0dff00000020a000 0x00dff00000020a00 0x6fff00000471f00b 0xe6fff00000471f00

def z40 : W := mkw 0x400052806ed00f0e 0x0400052806ed00f0 0x404031807ff00f0d 0xb404031807ff00f0

def z41 : W := mkw 0x10940436010650c0 0x810940436010650c 0xa1b40076478e70cb 0x7a1b40076478e70c

def z42 : W := mkw 0xafffad6d336de000 0x0afffad6d336de00 0xfffffffffffff00f 0xffffffffffffff00

def z43 : W := mkw 0x8f6aa94900000000 0x08f6aa9490000000 0x0e4b218980000000 0x80e4b21898000000

def z44 : W := mkw 0x9ffeff7f45865ccc 0x89ffeff7f45865cc 0xbfffffffc78e7ccf 0xfbfffffffc78e7cc

def z45 : W := mkw 0x0628a058100b00a1 0x00628a058100b00a 0xae38e078000f80f6 0xeae38e078000f80f

def z46 : W := mkw 0x109446344186488c 0x8109446344186488 0x11b0ce70438e0000 0x511b0ce70438e000

def z47 : W := mkw 0x2d6b00003269a000 0x02d6b00003269a00 0x4e4b000038718000 0x84e4b00003871800

def z48 : W := mkw 0x8dfe0d2500000000 0x08dfe0d250000000 0x1fff1f8780000003 0xe1fff1f878000000

def z49 : W := mkw 0x00004010580b0aa9 0x000004010580b0aa 0xe030c070780f8ffe 0x7e030c070780f8ff

def z50 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xffffffff80018fff 0xeffffffff80018ff

def z51 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1ff7dff780000001 0x41ff7dff78000000

def z52 : W := mkw 0x2d6a000032490000 0x02d6a00003249000 0x0e00000038000000 0x00e0000003800000

def z53 : W := mkw 0x2dff40107b6feaa9 0x02dff40107b6feaa 0x6fff00007ffffffb 0xf6fff00007ffffff

def z54 : W := mkw 0x4bd4fb806fd44f0e 0x04bd4fb806fd44f0 0x7ff4ff807ffe7f0f 0xf7ff4ff807ffe7f0

def z55 : W := mkw 0x8fffbdef8430b550 0x48fffbdef8430b55 0xffffffff8471ffff 0xeffffffff8471fff

def z56 : W := mkw 0x8fffad6d0020a000 0x08fffad6d0020a00 0xffffffff8471f00f 0xeffffffff8471f00

def z57 : W := mkw 0x4b41fb82eef0bf5e 0x44b41fb82eef0bf5 0xffcfff8ffff1ffff 0xfffcfff8ffff1fff

def z58 : W := mkw 0x9ffebf6f05845444 0x89ffebf6f0584544 0x9fffffff87807007 0xe9fffffff8780700

def z59 : W := mkw 0x009514a68430b550 0x4009514a68430b55 0xf1ffffff8471ffff 0xef1ffffff8471fff

def z60 : W := mkw 0x4b41fb80eef0af1e 0x44b41fb80eef0af1 0x5fcbff89fff18f3d 0xf5fcbff89fff18f3

def z61 : W := mkw 0x000100000020a000 0x0000100000020a00 0x604f00000471f00b 0xa604f00000471f00

def z62 : W := mkw 0x2dfe0000334d4000 0x02dfe0000334d400 0x0fb000007b8e0000 0x50fb000007b8e000

def z63 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fb000007ffff008 0x56fb000007ffff00

def z64 : W := mkw 0xafffed7d7b6feaa9 0x0afffed7d7b6feaa 0xffffffffffffffff 0xffffffffffffffff

def z65 : W := mkw 0x5b40ffb66ed21fce 0x85b40ffb66ed21fc 0xdfc0fff67ff00fcd 0xfdfc0fff67ff00fc

def z66 : W := mkw 0x20010000336de000 0x020010000336de00 0x600000007ffff008 0x1600000007ffff00

def z67 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xffc8ff887ff18fff 0xfffc8ff887ff18ff

def z68 : W := mkw 0x0000100204001440 0x0000010020400144 0xa004100604007ccf 0x2a004100604007cc

def z69 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0xee08e00878018ffe 0xfee08e00878018ff

def z70 : W := mkw 0x0094142604001440 0x0009414260400144 0xb1b4de7604007ccf 0x6b1b4de7604007cc

def z71 : W := mkw 0x49401b8026d00506 0x049401b8026d0050 0x5fc01f807ff00009 0xf5fc01f807ff0000

def z72 : W := mkw 0x4f68fbd87edb0faf 0x04f68fbd87edb0fa 0xfff8fff87fff8fff 0xffff8fff87fff8ff

def z73 : W := mkw 0x4200fb806ed00f0e 0x04200fb806ed00f0 0x5000ff807ff00f0c 0x15000ff807ff00f0

def z74 : W := mkw 0x3095563677effccc 0x83095563677effcc 0xf1b4de767ffffccf 0x7f1b4de767ffffcc

def z75 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x4e38e078780f8330 0xd4e38e078780f833

def z76 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1ffbeff980000000 0xc1ffbeff98000000

def z77 : W := mkw 0xcfffffefeef0bf5e 0x4cfffffefeef0bf5 0xfffffffffff1ffff 0xffffffffffff1fff

def z78 : W := mkw 0x000100028020b050 0x4000100028020b05 0xa00f000f8001f0f2 0x0a00f000f8001f0f

def z79 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x1f80ce007b800000 0x51f80ce007b80000

def z80 : W := mkw 0x4f68eb587acb0aaf 0x04f68eb587acb0aa 0x1fb0ce707b8e0000 0x51fb0ce707b8e000

def z81 : W := mkw 0x0000100204001440 0x0000010020400144 0xa04f318f84007ccf 0xaa04f318f84007cc

def z82 : W := mkw 0x94be567f45865ccc 0x894be567f45865cc 0xb1bfde7fc78e7ccf 0x7b1bfde7fc78e7cc

def z83 : W := mkw 0x0628a04800000000 0x00628a0480000000 0x0e30c07000000000 0x40e30c0700000000

def z84 : W := mkw 0x8f6aa94900000000 0x08f6aa9490000000 0x0e00000000000000 0x00e0000000000000

def z85 : W := mkw 0x8ffeed7d580b0aa9 0x08ffeed7d580b0aa 0xfffffffff80f8fff 0xffffffffff80f8ff

def z86 : W := mkw 0xcffebfed26d00506 0x0cffebfed26d0050 0x9fffffff87f00007 0xe9fffffff87f0000

def z87 : W := mkw 0x04284058580b0aa9 0x004284058580b0aa 0xe0380078780f8ffa 0x1e0380078780f8ff

def z88 : W := mkw 0x1000521245865ccc 0x81000521245865cc 0x3180de00478e7ccd 0x73180de00478e7cc

def z89 : W := mkw 0x0000108004100500 0x0000010800410050 0xe048318804718fff 0xae048318804718ff

def z90 : W := mkw 0x0628a04818090221 0x00628a0481809022 0xce38e07838018336 0xece38e0783801833

def z91 : W := mkw 0x0dfe000022400000 0x00dfe00002240000 0x4fff00007ff0000b 0xf4fff00007ff0000

def z92 : W := mkw 0x8ffebded04100500 0x08ffebded0410050 0xdfffffff84700f0f 0xedfffffff84700f0

def z93 : W := mkw 0xa4bf046d112de000 0x0a4bf046d112de00 0xa03f007f800ff002 0x0a03f007f800ff00

def z94 : W := mkw 0x0000000018090221 0x0000000001809022 0x4000000038018330 0x0400000003801833

def z95 : W := mkw 0x4b41b982ae70b752 0x44b41b982ae70b75 0xee4f318fbc71ffff 0xaee4f318fbc71fff

def z96 : W := mkw 0x0428000010090000 0x0042800001009000 0x20380000000f8002 0x020380000000f800

def z97 : W := mkw 0x0094042401044000 0x0009404240104400 0xb1b4de76478e700f 0x7b1b4de76478e700

def z98 : W := mkw 0x89d71da78430b550 0x489d71da78430b55 0xf1cf3f8f8471ffff 0xaf1cf3f8f8471fff

def z99 : W := mkw 0x10000436000210c0 0x810000436000210c 0x80000076000000c0 0x080000076000000c

def z100 : W := mkw 0x000042004080080c 0x0000042004080080 0x1180ce0043800000 0x51180ce004380000

def z101 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x31b0ce70478e7cc8 0x531b0ce70478e7cc

def z102 : W := mkw 0xadff046d336de000 0x0adff046d336de00 0xefff007ffffff00b 0xfefff007ffffff00

def z103 : W := mkw 0x0000108284101550 0x4000010828410155 0x8000318f80000ff4 0x08000318f80000ff

def z104 : W := mkw 0x0094000001044000 0x0009400000104400 0x21b40000478e700b 0x721b40000478e700

def z105 : W := mkw 0x4bd4ffa46ed00f0e 0x04bd4ffa46ed00f0 0xdff4fff67ff00f0f 0xfdff4fff67ff00f0

def z106 : W := mkw 0x1000563644821ccc 0x81000563644821cc 0xb030de76400e0cce 0x7b030de76400e0cc

def z107 : W := mkw 0x8ffead6d01044000 0x08ffead6d0104400 0xbfffffffc78e700f 0xfbfffffffc78e700

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000200800000ff4 0x08000200800000ff

def z109 : W := mkw 0x16bcf67e5d8f5eed 0x816bcf67e5d8f5ee 0xbfb4de767f8e7ccf 0x7bfb4de767f8e7cc

def z110 : W := mkw 0x4b40eb806ad00b0e 0x04b40eb806ad00b0 0x5fc0ef807bf00300 0xd5fc0ef807bf0030

def z111 : W := mkw 0x00004010580b0aa9 0x000004010580b0aa 0x60000000780f8ff8 0x160000000780f8ff

def z112 : W := mkw 0x1000521245865ccc 0x81000521245865cc 0x20000000478e7cc8 0x120000000478e7cc

def z113 : W := mkw 0x494052806ed00f0e 0x0494052806ed00f0 0x4fc000007ff00f09 0xf4fc000007ff00f0

def z114 : W := mkw 0x000100808030a110 0x4000100808030a11 0x404b218980718330 0x8404b21898071833

def z115 : W := mkw 0x0dfe000000000000 0x00dfe00000000000 0x8fff318f80000007 0xe8fff318f8000000

def z116 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x21ff000007fff003 0x021ff000007fff00

def z117 : W := mkw 0x1094162605845444 0x8109416260584544 0x91b4de7607807007 0x691b4de760780700

def z118 : W := mkw 0x0000001000020080 0x0000000100002008 0xa0300070000e00c2 0x0a0300070000e00c

def z119 : W := mkw 0x4940098022500102 0x0494009802250010 0x0040018000700000 0x0004001800070000

def z120 : W := mkw 0x0b40e90048000a08 0x00b40e90048000a0 0x5fc0ff8078000f0d 0xf5fc0ff8078000f0

def z121 : W := mkw 0x500052926fd65fce 0x8500052926fd65fc 0x600000007ffe7fc8 0x1600000007ffe7fc

def z122 : W := mkw 0x16bce47e590f5ae9 0x816bce47e590f5ae 0xee3ce07e780ffffe 0xfee3ce07e780ffff

def z123 : W := mkw 0x0000108004100500 0x0000010800410050 0x0040118004700001 0x0004011800470000

def z124 : W := mkw 0x0000108284101550 0x4000010828410155 0xe008318f80018ffe 0xae008318f80018ff

def z125 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xae30c070780e0cce 0x7ae30c070780e0cc

def z126 : W := mkw 0x8ffeed7d580b0aa9 0x08ffeed7d580b0aa 0xffb8ee78780f8ffe 0xfffb8ee78780f8ff

def z127 : W := mkw 0x4f68fbc87ed90f2f 0x04f68fbc87ed90f2 0x5fc8ff887ff18f3d 0xf5fc8ff887ff18f3

def z128 : W := mkw 0x1000563644821ccc 0x81000563644821cc 0x9000de7600000cc4 0x09000de7600000cc

def z129 : W := mkw 0x0200e01048020a88 0x00200e01048020a8 0xee30e070780e0fce 0xfee30e070780e0fc

def z130 : W := mkw 0x109556b6c5b6fddc 0xc109556b6c5b6fdd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z131 : W := mkw 0x2dff0002b36df050 0x42dff0002b36df05 0xefff000ffffff0fb 0xfefff000ffffff0f

def z132 : W := mkw 0x10940436010650c0 0x810940436010650c 0xa0340076000e70c2 0x0a0340076000e70c

def z133 : W := mkw 0x24bf0000112de000 0x024bf0000112de00 0x203f0000000ff002 0x0203f0000000ff00

def z134 : W := mkw 0x0000008000100100 0x0000000800010010 0x4040218000700300 0x8404021800070030

def z135 : W := mkw 0x0000520044800c0c 0x00000520044800c0 0x1180de0047800c0d 0x71180de0047800c0

def z136 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x5fc0ce007ff00009 0xf5fc0ce007ff0000

def z137 : W := mkw 0x100052125d8f5eed 0x8100052125d8f5ee 0x600000007f8ffff8 0x1600000007f8ffff

def z138 : W := mkw 0x000110808430a510 0x4000110808430a51 0x404b318984718f3d 0xa404b318984718f3

def z139 : W := mkw 0x9294ff7f45865ccc 0x89294ff7f45865cc 0xb1b4ffffc78e7ccf 0x7b1b4ffffc78e7cc

def z140 : W := mkw 0x1094162605845444 0x8109416260584544 0xb1841e0607807ccf 0x2b1841e0607807cc

def z141 : W := mkw 0x8f6aa94900000000 0x08f6aa9490000000 0x8e4f318f80000007 0xa8e4f318f8000000

def z142 : W := mkw 0x1000563645865ccc 0x81000563645865cc 0xb000de76478e7ccc 0x1b000de76478e7cc

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004100600000007 0x2800410060000000

def z144 : W := mkw 0x0200e010580b0aa9 0x00200e010580b0aa 0x6e00e000780f8ffc 0xf6e00e000780f8ff

def z145 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x0e30c070780e0000 0x50e30c070780e000

def z146 : W := mkw 0x2dff1082b77df550 0x42dff1082b77df55 0xefff318fffffffff 0xfefff318ffffffff

def z147 : W := mkw 0x0000000280001050 0x4000000028000105 0x8000000f800000f0 0x08000000f800000f

def z148 : W := mkw 0x2fffe0587b6feaa9 0x02fffe0587b6feaa 0xefffe0787fffffff 0xfefffe0787ffffff

def z149 : W := mkw 0x29d700002364e000 0x029d700002364e00 0x01c7000007f07001 0x001c7000007f0700

def z150 : W := mkw 0x4200fb804c900f0e 0x04200fb804c900f0 0x1000ff8000000f04 0x01000ff8000000f0

def z151 : W := mkw 0x0000108284101550 0x4000010828410155 0x804f318f80000ff7 0xa804f318f80000ff

def z152 : W := mkw 0x0000108284101550 0x4000010828410155 0x0000118780000000 0x0000011878000000

def z153 : W := mkw 0x89d71da78430b550 0x489d71da78430b55 0x11c71f8784707001 0x011c71f878470700

def z154 : W := mkw 0x0000100204001440 0x0000010020400144 0xe00c300e0401ffff 0xae00c300e0401fff

def z155 : W := mkw 0x6bd7fb806ff4ef0e 0x06bd7fb806ff4ef0 0x5fc7ff807ff07f0d 0xf5fc7ff807ff07f0

def z156 : W := mkw 0x0000108284101550 0x4000010828410155 0xa004318f84007fff 0x2a004318f84007ff

def z157 : W := mkw 0x99d61f2705845444 0x899d61f270584544 0x11c71f8787807001 0x011c71f878780700

def z158 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x0ff700007ffe7001 0x50ff700007ffe700

def z159 : W := mkw 0x00004010580b0aa9 0x000004010580b0aa 0x00000000780e0000 0x100000000780e000

def z160 : W := mkw 0x3dfe563677cf5ccc 0x83dfe563677cf5cc 0xbfb4de767f8e7ccf 0x7bfb4de767f8e7cc

def z161 : W := mkw 0x10000012010650c0 0x810000012010650c 0x20000000000e70c0 0x020000000000e70c

def z162 : W := mkw 0x6ffffb807ffdef0e 0x06ffffb807ffdef0 0x7fffff807fffff0f 0xf7fffff807fffff0

def z163 : W := mkw 0x0000501244021cc8 0x00000501244021cc 0xa034d076440e7ccf 0x7a034d076440e7cc

def z164 : W := mkw 0x0629e058582baaa9 0x00629e058582baaa 0xee7fe0787c7fffff 0xfee7fe0787c7ffff

def z165 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff318ffffff00f 0xfefff318ffffff00

def z166 : W := mkw 0x0000120004800404 0x0000012000480040 0x11801e0007800001 0x011801e000780000

def z167 : W := mkw 0x0000108004100500 0x0000010800410050 0x4000000004700f08 0x04000000004700f0

def z168 : W := mkw 0x0428004810090021 0x0042800481009002 0x0008000800018030 0x0000800080001803

def z169 : W := mkw 0x5200ffb64c921fce 0x85200ffb64c921fc 0x9000fff600000fc4 0x09000fff600000fc

def z170 : W := mkw 0x0b40a90022400000 0x00b40a9002240000 0x5fc0ff807ff0000d 0xf5fc0ff807ff0000

def z171 : W := mkw 0xcb40ffed6ed00f0e 0x0cb40ffed6ed00f0 0xdfc0fffffff00f0d 0xfdfc0fffffff00f0

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0x600800000001800a 0xa600800000001800

def z173 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1ffffffc78e7ccf 0xfb1ffffffc78e7cc

def z174 : W := mkw 0x0000400040000808 0x0000040004000080 0x0000c00040000c0c 0x70000c00040000c0

def z175 : W := mkw 0xc9d61fa526d00506 0x0c9d61fa526d0050 0x11c71f8787f00001 0x011c71f8787f0000

def z176 : W := mkw 0x000110828430b550 0x4000110828430b55 0x600000000471fff8 0x0600000000471fff

def z177 : W := mkw 0x40001b8004900506 0x040001b800490050 0x10001f8000000000 0x010001f800000000

def z178 : W := mkw 0x24290000336de000 0x024290000336de00 0x6e3800007ffff00a 0xf6e3800007ffff00

def z179 : W := mkw 0x2d6b0000336de000 0x02d6b0000336de00 0x6e4b00007ffff008 0x96e4b00007ffff00

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008200800000006 0xa800820080000000

def z181 : W := mkw 0x200100002364e000 0x0200100002364e00 0x0000000007f07000 0x00000000007f0700

def z182 : W := mkw 0x09411082a670b550 0x409411082a670b55 0xefcf318ffff1ffff 0xfefcf318ffff1fff

def z183 : W := mkw 0x6ffffbd87fffefaf 0x06ffffbd87fffefa 0xfffffff87fffffff 0xffffffff87ffffff

def z184 : W := mkw 0x0b40a90000000000 0x00b40a9000000000 0x1fc0ff8000000005 0xe1fc0ff800000000

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x1180de0000000005 0x61180de000000000

def z186 : W := mkw 0x8f6ba9c98030a110 0x48f6ba9c98030a11 0x4e4b218980718330 0x84e4b21898071833

def z187 : W := mkw 0x0ffea04800000000 0x00ffea0480000000 0x8fffe07800000007 0xe8fffe0780000000

def z188 : W := mkw 0x0629a0c89839a331 0x40629a0c89839a33 0x4e4b2189b8718330 0x84e4b2189b871833

def z189 : W := mkw 0x10015292c5b6fddc 0xc10015292c5b6fdd 0x6000000047fffff8 0x16000000047fffff

def z190 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x1f80ff807b800f04 0x51f80ff807b800f0

def z191 : W := mkw 0x10941436050654c0 0x810941436050654c 0xa0341076040e7ccf 0x2a0341076040e7cc

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00000078000008 0xf4e0000007800000

def z193 : W := mkw 0x1294f67e4d865eed 0x81294f67e4d865ee 0xb1b4fe7e478e7fff 0x7b1b4fe7e478e7ff

def z194 : W := mkw 0x24bf0000336de000 0x024bf0000336de00 0x603f00007ffff00a 0x1603f00007ffff00

def z195 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff20087fffffff 0xfefff20087ffffff

def z196 : W := mkw 0x49411b82a6f0b556 0x449411b82a6f0b55 0x11c71f8787f07001 0x011c71f8787f0700

def z197 : W := mkw 0x8f6aa94918090221 0x08f6aa9491809022 0x4e4b2189b8018330 0x84e4b2189b801833

def z198 : W := mkw 0x69d71b8027f4e506 0x069d71b8027f4e50 0x11c71f8007f07001 0x011c71f8007f0700

def z199 : W := mkw 0x400052804c900f0e 0x0400052804c900f0 0x0000000000000f00 0x00000000000000f0

def z200 : W := mkw 0x0000100204001440 0x0000010020400144 0x0004100604007001 0x0000410060400700

def z201 : W := mkw 0x0000108004100500 0x0000010800410050 0x4040318004700f0d 0xa4040318004700f0

def z202 : W := mkw 0x4b40a9002a400202 0x04b40a9002a40020 0x0e00000038000000 0x00e0000003800000

def z203 : W := mkw 0x16bce67c598f4aad 0x816bce67c598f4aa 0xffb8ee787b8f8ffe 0xfffb8ee787b8f8ff

def z204 : W := mkw 0x4b40b9802e500702 0x04b40b9802e50070 0x4e4031803c700f0d 0xa4e4031803c700f0

def z205 : W := mkw 0x8ffead6d18090221 0x08ffead6d1809022 0xdfffffffb8018337 0xedfffffffb801833

def z206 : W := mkw 0x1094563644821ccc 0x81094563644821cc 0x91b4de7600000cc7 0x691b4de7600000cc

def z207 : W := mkw 0x29410000336de000 0x029410000336de00 0x6fc000007ffff009 0xf6fc000007ffff00

def z208 : W := mkw 0x20011082b77df550 0x420011082b77df55 0x600000007ffffff8 0x1600000007ffffff

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040318000000005 0xa004031800000000

def z210 : W := mkw 0x1200f67e4c821eed 0x81200f67e4c821ee 0x9000fe7e00000ff4 0x09000fe7e00000ff

def z211 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0x4e00e00078000f0c 0xf4e00e00078000f0

def z212 : W := mkw 0x0bd4ad2400000000 0x00bd4ad240000000 0x9ff4fff600000007 0xe9ff4fff60000000

def z213 : W := mkw 0x0000108284101550 0x4000010828410155 0xc040318f84700ffd 0xac040318f84700ff

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x200400000400700b 0x2200400000400700

def z215 : W := mkw 0x09d6000000000000 0x009d600000000000 0x01c7000000000001 0x001c700000000000

def z216 : W := mkw 0x3dff563677effccc 0x83dff563677effcc 0xffffde767ffffccf 0xfffffde767ffffcc

def z217 : W := mkw 0x9ffeff7f5d8f5eed 0x89ffeff7f5d8f5ee 0xffffffffff8fffff 0xfffffffffff8ffff

def z218 : W := mkw 0x1628f25a5d8f5eed 0x81628f25a5d8f5ee 0xee38e0787f8ffffe 0xfee38e0787f8ffff

def z219 : W := mkw 0x0628a04818090221 0x00628a0481809022 0x4e08200838018330 0x84e0820083801833

def z220 : W := mkw 0x16bcf67e5d8f5eed 0x816bcf67e5d8f5ee 0xffbcfe7e7f8fffff 0xfffbcfe7e7f8ffff

def z221 : W := mkw 0x4200fb804c900f0e 0x04200fb804c900f0 0x5e00ff8078000f0c 0xf5e00ff8078000f0

def z222 : W := mkw 0x20950000336de000 0x020950000336de00 0x61b400007ffff00b 0x761b400007ffff00

def z223 : W := mkw 0x9ffeef7d4186488c 0x89ffeef7d4186488 0x9fffffffc38e0007 0xf9fffffffc38e000

def z224 : W := mkw 0x8ffeff6d44800c0c 0x08ffeff6d44800c0 0x9fffffffc7800c0f 0xf9fffffffc7800c0

def z225 : W := mkw 0x109514b68536f5d0 0xc109514b68536f5d 0xe07f31ff847fffff 0xae07f31ff847ffff

def z226 : W := mkw 0x400000802a500302 0x0400000802a50030 0x4000000038700300 0x0400000003870030

def z227 : W := mkw 0x4b40fb82eed01f5e 0x44b40fb82eed01f5 0xdfc0ff8ffff00ffd 0xfdfc0ff8ffff00ff

def z228 : W := mkw 0x8bd6ad6d00000000 0x08bd6ad6d0000000 0x91c7ffff80000005 0x091c7ffff8000000

def z229 : W := mkw 0xcffefffd7edb0faf 0x0cffefffd7edb0fa 0xffffffffffff8fff 0xfffffffffffff8ff

def z230 : W := mkw 0x000110828430b550 0x4000110828430b55 0xc04b318f80718ff4 0x8c04b318f80718ff

def z231 : W := mkw 0x094100002260a000 0x0094100002260a00 0x6fcf00007ff1f00b 0xf6fcf00007ff1f00

def z232 : W := mkw 0x200100003269a000 0x0200100003269a00 0x4000000038718000 0x0400000003871800

def z233 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe000318f8471fffc 0x0e000318f8471fff

def z234 : W := mkw 0xcffeef6d6ac00a0e 0x0cffeef6d6ac00a0 0x1fb0ce707b800000 0x51fb0ce707b80000

def z235 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x6e30c070780f8ff8 0x56e30c070780f8ff

def z236 : W := mkw 0x0094000001044000 0x0009400000104400 0x0184000007807001 0x0018400000780700

def z237 : W := mkw 0x1094162605845444 0x8109416260584544 0x31b41e06478e700b 0x731b41e06478e700

def z238 : W := mkw 0x0629f0dadc3bbff9 0x40629f0dadc3bbff 0xee7ff1fffc7fffff 0xfee7ff1fffc7ffff

def z239 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x4fcf00003ff1f001 0x84fcf00003ff1f00

def z240 : W := mkw 0x14bc5636558f5ccc 0x814bc5636558f5cc 0xffbcde767f8ffccf 0xfffbcde767f8ffcc

def z241 : W := mkw 0x0628a04800000000 0x00628a0480000000 0x8e38e07800000006 0xe8e38e0780000000

def z242 : W := mkw 0x0200a90000000000 0x00200a9000000000 0x1000ff8000000004 0x01000ff800000000

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x804f318f80000007 0xa804f318f8000000

def z244 : W := mkw 0x109516a685b4f554 0xc109516a685b4f55 0xf1cf3f8f87f1ffff 0xaf1cf3f8f87f1fff

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0080008000180f2 0x0a0080008000180f

def z246 : W := mkw 0xafffad6d336de000 0x0afffad6d336de00 0x7fffce707ffff00b 0xf7fffce707ffff00

def z247 : W := mkw 0x0628f0dadc1b1ff9 0x40628f0dadc1b1ff 0xee38f1fff80f8ffe 0xfee38f1fff80f8ff

def z248 : W := mkw 0x00015092dc3bbff9 0x400015092dc3bbff 0x600000007c7ffff8 0x1600000007c7ffff

def z249 : W := mkw 0x0428000010090000 0x0042800001009000 0x4e08000038018000 0x84e0800003801800

def z250 : W := mkw 0x04284058500b08a9 0x004284058500b08a 0xa038c078400f8cfe 0x7a038c078400f8cf

def z251 : W := mkw 0x8000046d00000000 0x08000046d0000000 0x8000007f80000000 0x08000007f8000000

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x4040000004700009 0xa404000000470000

def z253 : W := mkw 0x0000401040020888 0x0000040104002088 0x8000c07000000cc4 0x08000c07000000cc

def z254 : W := mkw 0x8ffebd6f04001440 0x08ffebd6f0400144 0xbfffffff84007ccf 0xebfffffff84007cc

def z255 : W := mkw 0x0094042400000000 0x0009404240000000 0x91ffffff80000007 0xe91ffffff8000000

def z256 : W := mkw 0x0628f2585c8b0ead 0x00628f2585c8b0ea 0xffb8fe787f8f8fff 0xfffb8fe787f8f8ff

def z257 : W := mkw 0x9ffead7f010650c0 0x89ffead7f010650c 0xbfffffff800e70c7 0xebfffffff800e70c

def z258 : W := mkw 0x0094562444800c0c 0x00094562444800c0 0x91b4de7647800c0f 0x791b4de7647800c0

def z259 : W := mkw 0x8628ad6d00000000 0x08628ad6d0000000 0x9e38ffff80000006 0xe9e38ffff8000000

def z260 : W := mkw 0x2fffa048336de000 0x02fffa048336de00 0xefffe0787ffff00f 0xfefffe0787ffff00

def z261 : W := mkw 0x000100808030a110 0x4000100808030a11 0xc04f318f80718337 0xac04f318f8071833

def z262 : W := mkw 0x0dfe000000000000 0x00dfe00000000000 0x0fff000000000003 0xe0fff00000000000

def z263 : W := mkw 0x000110828430b550 0x4000110828430b55 0x0047118784707001 0x0004711878470700

def z264 : W := mkw 0x06bca46c00000000 0x006bca46c0000000 0x9fbcfe7e00000007 0xe9fbcfe7e0000000

def z265 : W := mkw 0x0428000010090000 0x0042800001009000 0x0e300000780e0000 0x50e300000780e000

def z266 : W := mkw 0x4b40bb802ed00706 0x04b40bb802ed0070 0x5fc03f803ff00301 0x85fc03f803ff0030

def z267 : W := mkw 0x1000162604801444 0x8100016260480144 0x10001e0600000000 0x010001e060000000

def z268 : W := mkw 0x000100000020a000 0x0000100000020a00 0x600000000471f008 0x0600000000471f00

def z269 : W := mkw 0x24bf0000112de000 0x024bf0000112de00 0x607f0000047ff00b 0xa607f0000047ff00

def z270 : W := mkw 0x0b40e0006a400a08 0x00b40e0006a400a0 0x4fc0e0007ff00f0d 0xf4fc0e0007ff00f0

def z271 : W := mkw 0x000110800430a500 0x0000110800430a50 0x604f31800471ff0f 0xa604f31800471ff0

def z272 : W := mkw 0x8628ed7d580b0aa9 0x08628ed7d580b0aa 0xfe38fffff80f8ffe 0xffe38fffff80f8ff

def z273 : W := mkw 0x4200fb804c900f0e 0x04200fb804c900f0 0x1180ff8047800f0d 0x71180ff8047800f0

def z274 : W := mkw 0x3dff521277effccc 0x83dff521277effcc 0x6fff00007ffffccb 0xf6fff00007ffffcc

def z275 : W := mkw 0x2ffee0587b4f4aa9 0x02ffee0587b4f4aa 0xefb8e0787b8f8ffe 0xfefb8e0787b8f8ff

def z276 : W := mkw 0x80000d2500000000 0x080000d250000000 0x10001f8780000000 0x010001f878000000

def z277 : W := mkw 0x042910da943bb5f1 0x4042910da943bb5f 0xe07f31ff847fffff 0xae07f31ff847ffff

def z278 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x1fc0ff807b800005 0xf1fc0ff807b80000

def z279 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x11c0ff8007f00f05 0x011c0ff8007f00f0

def z280 : W := mkw 0x042900001029a000 0x0042900001029a00 0x6e7f00007c7ff00b 0xf6e7f00007c7ff00

def z281 : W := mkw 0x0200f0dacc121ff9 0x40200f0dacc121ff 0x8000f1ff80000ff4 0x08000f1ff80000ff

def z282 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0x0000e00000000f04 0x00000e00000000f0

def z283 : W := mkw 0x000100008020a010 0x4000100008020a01 0x000b000980018030 0x0000b00098001803

def z284 : W := mkw 0x6f6ba9803a79a302 0x06f6ba9803a79a30 0x4e4b218038718300 0x84e4b21803871830

def z285 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xdfcfff8ffff00f0f 0xfdfcfff8ffff00f0

def z286 : W := mkw 0xadff0d25336de000 0x0adff0d25336de00 0x7fff1f87fffff00b 0xf7fff1f87fffff00

def z287 : W := mkw 0xaffead6d334d4000 0x0affead6d334d400 0x9ffffffffb8e0007 0xf9ffffffffb8e000

def z288 : W := mkw 0x0000520244801c4c 0x00000520244801c4 0xb184de0647807ccf 0x7b184de0647807cc

def z289 : W := mkw 0x000110828430b550 0x4000110828430b55 0x404f318f8471f331 0x8404f318f8471f33

def z290 : W := mkw 0x14bc047e110f50e1 0x814bc047e110f50e 0xa03c007e000ff0f2 0x0a03c007e000ff0f

def z291 : W := mkw 0x8ffead6d10090000 0x08ffead6d1009000 0xfffffffff80f800f 0xffffffffff80f800

def z292 : W := mkw 0x4000128026d00506 0x04000128026d0050 0x0000000007f00000 0x00000000007f0000

def z293 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xf1bcfe7e478fffff 0xff1bcfe7e478ffff

def z294 : W := mkw 0xafffa949336de000 0x0afffa949336de00 0x6fff2189fffff00b 0xf6fff2189fffff00

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000000018ff8 0x06000000000018ff

def z296 : W := mkw 0x0094401041064888 0x0009440104106488 0xa1b4c070478e7ccf 0x7a1b4c070478e7cc

def z297 : W := mkw 0x7fffffb67fffffce 0x87fffffb67fffffc 0xfffffff67fffffcf 0xffffffff67fffffc

def z298 : W := mkw 0x34bf563655affccc 0x834bf563655affcc 0xb1bfde76478ffccf 0x7b1bfde76478ffcc

def z299 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91cf3f8f80000007 0xa91cf3f8f8000000

def z300 : W := mkw 0x20010000336de000 0x020010000336de00 0x604f00007ffff00b 0xb604f00007ffff00

def z301 : W := mkw 0x0000100204001440 0x0000010020400144 0x8000100600000cc4 0x08000100600000cc

def z302 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fb4de7600000007 0x69fb4de760000000

def z303 : W := mkw 0x200140107b6feaa9 0x0200140107b6feaa 0x600000007ffffff8 0x1600000007ffffff

def z304 : W := mkw 0x000100808030a110 0x4000100808030a11 0x604f21898471f33b 0xa604f21898471f33

def z305 : W := mkw 0x2d6b00003269a000 0x02d6b00003269a00 0x6e7b0000787f800a 0xf6e7b0000787f800

def z306 : W := mkw 0x000110828430b550 0x4000110828430b55 0x804f318f84707007 0xa804f318f8470700

def z307 : W := mkw 0x24bf1082953df550 0x424bf1082953df55 0xe07f318f847fffff 0xae07f318f847ffff

def z308 : W := mkw 0x3dff463473efe88c 0x83dff463473efe88 0x7fffce707ffff00b 0xf7fffce707ffff00

def z309 : W := mkw 0x0b40a90000000000 0x00b40a9000000000 0x9fcfff8f80000007 0xe9fcfff8f8000000

def z310 : W := mkw 0x3ffff67e7feffeed 0x83ffff67e7feffee 0xfffffe7e7fffffff 0xffffffe7e7ffffff

def z311 : W := mkw 0x0f68a94800000000 0x00f68a9480000000 0x9ff8fff800000007 0xe9ff8fff80000000

def z312 : W := mkw 0x2dff0058336fe0a1 0x02dff0058336fe0a 0xefff00787ffff0fb 0xfefff00787ffff0f

def z313 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb034de76000e7cc6 0x0b034de76000e7cc

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000000cce 0x2a000000000000cc

def z315 : W := mkw 0x8fffaded8030a110 0x48fffaded8030a11 0xdfffffff80718337 0xedfffffff8071833

def z316 : W := mkw 0x100042104186488c 0x8100042104186488 0x00000000438e0000 0x100000000438e000

def z317 : W := mkw 0x2d6b0080b279a110 0x42d6b0080b279a11 0x4e4b2189b8718330 0x84e4b2189b871833

def z318 : W := mkw 0x00004010580b0aa9 0x000004010580b0aa 0xe0082008780f8ffe 0xbe0082008780f8ff

def z319 : W := mkw 0x2dff00002364e000 0x02dff00002364e00 0x0fff000007f07003 0xe0fff000007f0700

def z320 : W := mkw 0x04284010500b0888 0x004284010500b088 0xee38c070780f8cce 0xfee38c070780f8cc

def z321 : W := mkw 0x0094520045844c0c 0x00094520045844c0 0x31b4de00478e7c0f 0x731b4de00478e7c0

def z322 : W := mkw 0x8200ad6d00000000 0x08200ad6d0000000 0x904fffff80000007 0xa904fffff8000000

def z323 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91f7dff780000007 0x691f7dff78000000

def z324 : W := mkw 0x2ffee0587b4f4aa9 0x02ffee0587b4f4aa 0x0fb0c0707b8e0000 0x50fb0c0707b8e000

def z325 : W := mkw 0x8f6aa94900000000 0x08f6aa9490000000 0x1fcbff8980000005 0xe1fcbff898000000

def z326 : W := mkw 0x24bf0002912df050 0x424bf0002912df05 0xa03f000f800ff0f2 0x0a03f000f800ff0f

def z327 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5f80ce007ff00f08 0x55f80ce007ff00f0

def z328 : W := mkw 0x0000108204101540 0x0000010820410154 0xe044318604707fcf 0xae044318604707fc

def z329 : W := mkw 0x6ffeeb007bcd4a0e 0x06ffeeb007bcd4a0 0x1fb0ce007b8e0000 0x51fb0ce007b8e000

def z330 : W := mkw 0x9fffffffc5b6fddc 0xc9fffffffc5b6fdd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z331 : W := mkw 0x042910829439b550 0x4042910829439b55 0xee7f318ffc7fffff 0xfee7f318ffc7ffff

def z332 : W := mkw 0x00000058000200a1 0x000000058000200a 0x80000078000000f0 0x080000078000000f

def z333 : W := mkw 0x100156b6c4b2bddc 0xc100156b6c4b2bdd 0xf04fffff8471ffff 0xaf04fffff8471fff

def z334 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xa038e078000f8ff6 0x0a038e078000f8ff

def z335 : W := mkw 0x8201bdef8430b550 0x48201bdef8430b55 0xf04fffff8471ffff 0xaf04fffff8471fff

def z336 : W := mkw 0x3dff56b6f7fffddc 0xc3dff56b6f7fffdd 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x4b41a980aa70a312 0x44b41a980aa70a31 0x4e4b2189b8718330 0x84e4b2189b871833

def z338 : W := mkw 0x8f6aa94900000000 0x08f6aa9490000000 0x8e7be1f980000006 0xe8e7be1f98000000

def z339 : W := mkw 0x0200a04800000000 0x00200a0480000000 0x8000e07800000004 0x08000e0780000000

def z340 : W := mkw 0x0940090000000000 0x0094009000000000 0x11c01f8000000001 0x011c01f800000000

def z341 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x31841e06478e7cc9 0x131841e06478e7cc

def z342 : W := mkw 0x29d71082a774f550 0x429d71082a774f55 0x01c7118787f07001 0x001c7118787f0700

def z343 : W := mkw 0x9ffeff7f45865ccc 0x89ffeff7f45865cc 0xbfb4de76478e7ccf 0x7bfb4de76478e7cc

def z344 : W := mkw 0x8f6aad6d00000000 0x08f6aad6d0000000 0x9e4bffff80000004 0x89e4bffff8000000

def z345 : W := mkw 0x20010000112de000 0x020010000112de00 0x20000000000ff000 0x020000000000ff00

def z346 : W := mkw 0x4b40fb906ed20f8e 0x04b40fb906ed20f8 0xfff0fff07ffe0fcf 0xffff0fff07ffe0fc

def z347 : W := mkw 0x0628e04848000a08 0x00628e04848000a0 0xce38e07878000f0e 0xfce38e07878000f0

def z348 : W := mkw 0x509456b66fd65fce 0x8509456b66fd65fc 0xf1b4de767ffe7fcf 0x7f1b4de767ffe7fc

def z349 : W := mkw 0x1000563644821ccc 0x81000563644821cc 0xb004de7604007ccf 0x2b004de7604007cc

def z350 : W := mkw 0x09d4000023444000 0x009d400002344400 0x6ff400007ffe700b 0xf6ff400007ffe700

def z351 : W := mkw 0x4b40e9806a500b0a 0x04b40e9806a500b0 0x4e40e18078700f0c 0xf4e40e18078700f0

def z352 : W := mkw 0x9ffeff7f44821ccc 0x89ffeff7f44821cc 0x9fffffff80000cc7 0xe9fffffff80000cc

def z353 : W := mkw 0x8f6ae959580b0aa9 0x08f6ae959580b0aa 0xee7be1f9f80f8ffe 0xfee7be1f9f80f8ff

def z354 : W := mkw 0x20011082b77df550 0x420011082b77df55 0xe04f318fffffffff 0xbe04f318ffffffff

def z355 : W := mkw 0x04280058100b00a1 0x004280058100b00a 0xe0382078000f8ffe 0xae0382078000f8ff

def z356 : W := mkw 0x9200ff7f44821ccc 0x89200ff7f44821cc 0x9000ffff80000cc4 0x09000ffff80000cc

def z357 : W := mkw 0x3dfe463473cf488c 0x83dfe463473cf488 0x1fb0ce707b8e0000 0x51fb0ce707b8e000

def z358 : W := mkw 0x0000100204001440 0x0000010020400144 0x2000000004007cc8 0x02000000004007cc

def z359 : W := mkw 0x8942090100000000 0x0894209010000000 0x0043018180000000 0x0004301818000000

def z360 : W := mkw 0x0428000000000000 0x0042800000000000 0x0e38000000000002 0xe0e3800000000000

def z361 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000001 0xe0fc000000000000

def z362 : W := mkw 0x16bdf6feddbffffd 0xc16bdf6feddbffff 0xffffffffffffffff 0xffffffffffffffff

def z363 : W := mkw 0x2dff00003269a000 0x02dff00003269a00 0x4fff000038718003 0xe4fff00003871800

def z364 : W := mkw 0x0628f05a5c0b1ee9 0x00628f05a5c0b1ee 0xee3cf07e7c0fffff 0xfee3cf07e7c0ffff

def z365 : W := mkw 0x0000401040020888 0x0000040104002088 0x20000000400e0cc8 0x120000000400e0cc

def z366 : W := mkw 0x000110828430b550 0x4000110828430b55 0xa00f318f8001fff6 0x0a00f318f8001fff

def z367 : W := mkw 0x6b41fb807ffdef0e 0x06b41fb807ffdef0 0x7fc0ff807fffff0d 0xf7fc0ff807fffff0

def z368 : W := mkw 0x000110828430b550 0x4000110828430b55 0xa04f118f8471f0f3 0x0a04f118f8471f0f

def z369 : W := mkw 0x0000000001044000 0x0000000000104400 0x20000000478e7008 0x120000000478e700

def z370 : W := mkw 0x0629e05ad82bbaf9 0x40629e05ad82bbaf 0xee3fe07ff80ffffe 0xfee3fe07ff80ffff

def z371 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x6e082008780f8ff8 0x96e082008780f8ff

def z372 : W := mkw 0x5bd4ffa66fd45f4e 0x85bd4ffa66fd45f4 0x5fc4ff867ff07f0d 0xf5fc4ff867ff07f0

def z373 : W := mkw 0x000110828430b550 0x4000110828430b55 0x4047318784707f0d 0xa4047318784707f0

def z374 : W := mkw 0x0628a04818090221 0x00628a0481809022 0xee08200838018ffe 0xaee08200838018ff

def z375 : W := mkw 0x10944636418658cc 0x810944636418658c 0xb1b4ce76438e70c2 0x5b1b4ce76438e70c

def z376 : W := mkw 0x4f68a9c83a590323 0x04f68a9c83a59032 0x4e48218838718330 0x84e4821883871833

def z377 : W := mkw 0x0940000022400000 0x0094000002240000 0x4e40000038700000 0x84e4000003870000

def z378 : W := mkw 0x000100828030b150 0x4000100828030b15 0xe04f218f8071f3f2 0x8e04f218f8071f3f

def z379 : W := mkw 0x8ffeed7d40020888 0x08ffeed7d4002088 0xbfffffffc00e0ccf 0xfbfffffffc00e0cc

def z380 : W := mkw 0xcffeaded2a500302 0x0cffeaded2a50030 0xdfffffffb8700307 0xedfffffffb870030

def z381 : W := mkw 0xefffffed7ffdef0e 0x0efffffed7ffdef0 0xffffffffffffff0f 0xfffffffffffffff0

def z382 : W := mkw 0x1294f6364d865ecc 0x81294f6364d865ec 0xffb4fe767f8e7fcf 0xfffb4fe767f8e7fc

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x004f000000000003 0xa004f00000000000

def z384 : W := mkw 0x1000521245865ccc 0x81000521245865cc 0xa030c070478e7cce 0x7a030c070478e7cc

def z385 : W := mkw 0x8bd6ad2500000000 0x08bd6ad250000000 0x1fc7ff8780000005 0xe1fc7ff878000000

def z386 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x4e4021807ff00f08 0x94e4021807ff00f0

def z387 : W := mkw 0x5ffcfffe7fdf5fef 0x85ffcfffe7fdf5fe 0xfffcfffe7fffffff 0xffffcfffe7ffffff

def z388 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x2fbf00007b8ff002 0x52fbf00007b8ff00

def z389 : W := mkw 0x0dfe000010090000 0x00dfe00001009000 0x6fff0000780f800b 0xf6fff0000780f800

def z390 : W := mkw 0xcf6aa9c92a500302 0x0cf6aa9c92a50030 0x4e4b2189b8700300 0x84e4b2189b870030

def z391 : W := mkw 0x2dfe0000334d4000 0x02dfe0000334d400 0x4ff000007ffe0009 0xf4ff000007ffe000

def z392 : W := mkw 0x842a004900000000 0x0842a00490000000 0x000b000980000000 0x0000b00098000000

def z393 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fb8ee7800000006 0xe9fb8ee780000000

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000047800009 0x7018000004780000

def z395 : W := mkw 0x59d41fa627d45546 0x859d41fa627d4554 0x11c41f8607f07001 0x011c41f8607f0700

def z396 : W := mkw 0x4b40fb804c900f0e 0x04b40fb804c900f0 0x1fc0ff8000000f05 0xe1fc0ff8000000f0

def z397 : W := mkw 0x000100000020a000 0x0000100000020a00 0x200f00000001f002 0x0200f00000001f00

def z398 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x4e30e070780e0f0c 0xf4e30e070780e0f0

def z399 : W := mkw 0x0000401048020aa9 0x00000401048020aa 0x0000000000000ff0 0x00000000000000ff

def z400 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5e40ff8038700f04 0x85e40ff8038700f0

def z401 : W := mkw 0x5bd4ffb46fd64f8e 0x85bd4ffb46fd64f8 0x5ff0fff07ffe0f0d 0xf5ff0fff07ffe0f0

def z402 : W := mkw 0x2dff1080377de500 0x02dff1080377de50 0x6fff31807fffff0f 0xf6fff31807fffff0

def z403 : W := mkw 0x4b40a9802a500302 0x04b40a9802a50030 0x4fc021807ff00309 0xf4fc021807ff0030

def z404 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe00f000f8471fffa 0x0e00f000f8471fff

def z405 : W := mkw 0x0628a04800000000 0x00628a0480000000 0xee38e07800018ffe 0xeee38e07800018ff

def z406 : W := mkw 0x109446344186488c 0x8109446344186488 0xb1b0ce70438e0cce 0x7b1b0ce70438e0cc

def z407 : W := mkw 0x000100808030a110 0x4000100808030a11 0xe04b218980718ffe 0xae04b218980718ff

def z408 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x9184de7607807cc5 0x09184de7607807cc

def z409 : W := mkw 0x0940520066c00c0c 0x00940520066c00c0 0x5fc0de007ff00c0d 0xf5fc0de007ff00c0

def z410 : W := mkw 0x2dff520077edec0c 0x02dff520077edec0 0x7fffde007ffffc0f 0xf7fffde007ffffc0

def z411 : W := mkw 0x0200e05848020aa9 0x00200e05848020aa 0x0000c07000000000 0x00000c0700000000

def z412 : W := mkw 0x04bc0000110d4000 0x004bc0000110d400 0x6fbc00007f8ff00b 0xf6fbc00007f8ff00

def z413 : W := mkw 0x0628a04800000000 0x00628a0480000000 0x0e08200800000000 0x80e0820080000000

def z414 : W := mkw 0x86bead6d00000000 0x086bead6d0000000 0x903fffff80000006 0x0903fffff8000000

def z415 : W := mkw 0x6dff52807ffdef0e 0x06dff52807ffdef0 0x6fff00007fffff0b 0xf6fff00007fffff0

def z416 : W := mkw 0x0000108284101550 0x4000010828410155 0x0000000000000ff0 0x00000000000000ff

def z417 : W := mkw 0x109456365d8f5eed 0x8109456365d8f5ee 0xf1b4de767f8fffff 0x7f1b4de767f8ffff

def z418 : W := mkw 0x4b40a9802a500302 0x04b40a9802a50030 0x5fc0ff8038700305 0xe5fc0ff803870030

def z419 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x11800e0000000000 0x011800e000000000

def z420 : W := mkw 0x84be046d00000000 0x084be046d0000000 0x91bfde7f80000007 0x691bfde7f8000000

def z421 : W := mkw 0xaf6ba9493269a000 0x0af6ba9493269a00 0x4e4b2189b8718000 0x84e4b2189b871800

def z422 : W := mkw 0x000110828430b550 0x4000110828430b55 0x604711878471fff9 0x0604711878471fff

def z423 : W := mkw 0x6fffa9803b7de302 0x06fffa9803b7de30 0x6fff21807ffff30b 0xf6fff21807ffff30

def z424 : W := mkw 0x109556b6c5b6fddc 0xc109556b6c5b6fdd 0xb1f7dff7c7fe7ccf 0x7b1f7dff7c7fe7cc

def z425 : W := mkw 0x5bd4ff366fc65ece 0x85bd4ff366fc65ec 0xbfb4de767f8e7ccf 0x7bfb4de767f8e7cc

def z426 : W := mkw 0x000110828430b550 0x4000110828430b55 0x8047318f84707ff5 0x08047318f84707ff

def z427 : W := mkw 0x3dff0436336ff0c0 0x83dff0436336ff0c 0xefff00767ffff0cb 0xfefff00767ffff0c

def z428 : W := mkw 0x000100028020b050 0x4000100028020b05 0xa04f318f8001f0f7 0xaa04f318f8001f0f

def z429 : W := mkw 0x600152807ffdef0e 0x0600152807ffdef0 0x600000007fffff08 0x1600000007fffff0

def z430 : W := mkw 0x0094000001044000 0x0009400000104400 0x01b00000438e0000 0x501b00000438e000

def z431 : W := mkw 0x86bea46d00000000 0x086bea46d0000000 0x8e3fe07f80000006 0xe8e3fe07f8000000

def z432 : W := mkw 0x000100808030a110 0x4000100808030a11 0x0043018180700000 0x0004301818070000

def z433 : W := mkw 0x000100000020a000 0x0000100000020a00 0x404b000000718000 0x8404b00000071800

def z434 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1fffce7000000003 0xe1fffce700000000

def z435 : W := mkw 0x0dfe000000000000 0x00dfe00000000000 0x0fb0000000000000 0x40fb000000000000

def z436 : W := mkw 0x000100000020a000 0x0000100000020a00 0xe04f20080471ffff 0xae04f20080471fff

def z437 : W := mkw 0x4b41fb82eef0bf5e 0x44b41fb82eef0bf5 0x5fc7ff87fff07f0d 0xf5fc7ff87fff07f0

def z438 : W := mkw 0x0b40a90000000000 0x00b40a9000000000 0x1f80ce0000000000 0x41f80ce000000000

def z439 : W := mkw 0x29d70000336de000 0x029d70000336de00 0x61c700007ffff009 0x161c700007ffff00

def z440 : W := mkw 0x4b40fb826ed01f4e 0x04b40fb826ed01f4 0xffc4ff867ff07fcf 0xfffc4ff867ff07fc

def z441 : W := mkw 0x8ffeed7d48020aa9 0x08ffeed7d48020aa 0x9fffffff80000ff7 0xe9fffffff80000ff

def z442 : W := mkw 0x6dff1b8037fde506 0x06dff1b8037fde50 0x7fff1f807ffff00b 0xf7fff1f807ffff00

def z443 : W := mkw 0x000110828430b550 0x4000110828430b55 0x604b21898471fff8 0x8604b21898471fff

def z444 : W := mkw 0x4ffefb806ed00f0e 0x04ffefb806ed00f0 0x5fffff807ff00f0f 0xf5fffff807ff00f0

def z445 : W := mkw 0x9ffeef7d4186488c 0x89ffeef7d4186488 0x1fb0ce70438e0000 0x51fb0ce70438e000

def z446 : W := mkw 0x10940436010650c0 0x810940436010650c 0xb1b4de76000e70c7 0x6b1b4de76000e70c

def z447 : W := mkw 0x86bee47d580b0aa9 0x086bee47d580b0aa 0xee3fe07ff80f8ffe 0xfee3fe07ff80f8ff

def z448 : W := mkw 0x29d700002364e000 0x029d700002364e00 0x4fc700007ff07009 0xf4fc700007ff0700

def z449 : W := mkw 0x0000000200001040 0x0000000020000104 0xa0040006000070c2 0x0a0040006000070c

def z450 : W := mkw 0x0200e058580b0aa9 0x00200e058580b0aa 0xe000e078780f8ffc 0x1e000e078780f8ff

def z451 : W := mkw 0x2fffe0587b6feaa9 0x02fffe0587b6feaa 0x6fffc0707ffff00b 0xf6fffc0707ffff00

def z452 : W := mkw 0x8fffad6f8020b050 0x48fffad6f8020b05 0xbfffffff8001f0f7 0xebfffffff8001f0f

def z453 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xce08e07838018ff4 0x8ce08e07838018ff

def z454 : W := mkw 0x109446344186488c 0x8109446344186488 0x31b4ce70478e700b 0x731b4ce70478e700

def z455 : W := mkw 0x400052907edb0faf 0x0400052907edb0fa 0x600000007fff8ff8 0x1600000007fff8ff

def z456 : W := mkw 0x8096042500000000 0x0809604250000000 0x0007000780000000 0x0000700078000000

def z457 : W := mkw 0xcbd6ffa56ed00f0e 0x0cbd6ffa56ed00f0 0x5fc7ff87fff00f0d 0xf5fc7ff87fff00f0

def z458 : W := mkw 0x000110028420b450 0x4000110028420b45 0xa00f100f8401fcff 0x2a00f100f8401fcf

def z459 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0x0e00c00078000000 0x50e00c0007800000

def z460 : W := mkw 0x0940000022400000 0x0094000002240000 0x01c0000007f00001 0x001c0000007f0000

def z461 : W := mkw 0x2dff0000112de000 0x02dff0000112de00 0x2fff0000000ff003 0xe2fff0000000ff00

def z462 : W := mkw 0xafffad6d2364e000 0x0afffad6d2364e00 0x9fffffff87f07007 0xe9fffffff87f0700

def z463 : W := mkw 0x000100000020a000 0x0000100000020a00 0x0047000004707001 0x0004700000470700

def z464 : W := mkw 0x0629b0ca9c39b771 0x40629b0ca9c39b77 0xee4f318fbc71ffff 0xaee4f318fbc71fff

def z465 : W := mkw 0x000100028020b050 0x4000100028020b05 0xe00f200f8001fffe 0xae00f200f8001fff

def z466 : W := mkw 0x4200a98008100302 0x04200a9800810030 0x0000218000000300 0x0000021800000030

def z467 : W := mkw 0x0628e00058090a08 0x00628e00058090a0 0x6e38e000780f8f0e 0xf6e38e000780f8f0

def z468 : W := mkw 0x84bf14ef8430b550 0x484bf14ef8430b55 0xe07f31ff8471ffff 0xae07f31ff8471fff

def z469 : W := mkw 0x8ffebdef84101550 0x48ffebdef8410155 0x9fffffff80000ff7 0xe9fffffff80000ff

def z470 : W := mkw 0xafffad6d3269a000 0x0afffad6d3269a00 0xdfffffffb8718007 0xedfffffffb871800

def z471 : W := mkw 0x2ffff0daff7ffff9 0x42ffff0daff7ffff 0xeffff1ffffffffff 0xfeffff1fffffffff

def z472 : W := mkw 0x4200eb0048800a0e 0x04200eb0048800a0 0x1000ce0000000000 0x01000ce000000000

def z473 : W := mkw 0x4200fb804c900f0e 0x04200fb804c900f0 0x5040ff8004700f0d 0xa5040ff8004700f0

def z474 : W := mkw 0x0201f0dacc32bff9 0x40201f0dacc32bff 0xe04ff1ff8471ffff 0xae04ff1ff8471fff

def z475 : W := mkw 0x000100028020b050 0x4000100028020b05 0xe04f000f8471f0fb 0xae04f000f8471f0f

def z476 : W := mkw 0x8fffbdef8430b550 0x48fffbdef8430b55 0x9fffffff84707007 0xe9fffffff8470700

def z477 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x8e30e078780e0ff4 0x58e30e078780e0ff

def z478 : W := mkw 0x000110828430b550 0x4000110828430b55 0x604f11878471f00b 0xa604f11878471f00

def z479 : W := mkw 0x84be047d100b00a1 0x084be047d100b00a 0xa03f007f800f80f2 0x0a03f007f800f80f

def z480 : W := mkw 0x2f6be0587a6baaa9 0x02f6be0587a6baaa 0xee7be078787f8ffe 0xfee7be078787f8ff

def z481 : W := mkw 0x04284010580b0aa9 0x004284010580b0aa 0x6e380000780f8ffa 0xf6e380000780f8ff

def z482 : W := mkw 0x8ffea94900000000 0x08ffea9490000000 0x0fff218980000003 0xe0fff21898000000

def z483 : W := mkw 0x2dff1082b77df550 0x42dff1082b77df55 0x6fff1187fffff00b 0xf6fff1187fffff00

def z484 : W := mkw 0x0628e05840020888 0x00628e0584002088 0xae38e078400e0cce 0xfae38e078400e0cc

def z485 : W := mkw 0x49401b8026d00506 0x049401b8026d0050 0x51c03f8007f00f0d 0xa51c03f8007f00f0

def z486 : W := mkw 0x8ffeed7d580b0aa9 0x08ffeed7d580b0aa 0x9ffffffff80e0007 0xf9ffffffff80e000

def z487 : W := mkw 0x2fffa0483b6de221 0x02fffa0483b6de22 0x6fff20087ffff33b 0xf6fff20087ffff33

def z488 : W := mkw 0x24bf0058112fe0a1 0x024bf0058112fe0a 0xa03f0078000ff0f2 0x0a03f0078000ff0f

def z489 : W := mkw 0x0ffee058580b0aa9 0x00ffee058580b0aa 0xefffe078780f8fff 0xfefffe078780f8ff

def z490 : W := mkw 0x4200fb82cc901f5e 0x44200fb82cc901f5 0x9000ff8f80000ff4 0x09000ff8f80000ff

def z491 : W := mkw 0x0200a04808000221 0x00200a0480800022 0x0000200800000330 0x0000020080000033

def z492 : W := mkw 0x00000010100b00a1 0x000000010100b00a 0x20000000000f80f0 0x020000000000f80f

def z493 : W := mkw 0x4b40bb8026d00506 0x04b40bb8026d0050 0x1fc0ff8007f00005 0xe1fc0ff8007f0000

def z494 : W := mkw 0x0094042400000000 0x0009404240000000 0x8034007600000002 0x0803400760000000

def z495 : W := mkw 0x4628fbd85c9b0faf 0x04628fbd85c9b0fa 0xfe38fff8780f8ffe 0xffe38fff8780f8ff

def z496 : W := mkw 0x0628a04800000000 0x00628a0480000000 0x8e7ff1ff80000007 0xe8e7ff1ff8000000

def z497 : W := mkw 0x2d6b00003269a000 0x02d6b00003269a00 0x6e4f00003c71f00b 0xa6e4f00003c71f00

def z498 : W := mkw 0x00015092c432bdd8 0x400015092c432bdd 0xe07ff1ffc47fffff 0xfe07ff1ffc47ffff

def z499 : W := mkw 0x3dff162637edf444 0x83dff162637edf44 0x7fff1e067ffff00b 0xf7fff1e067ffff00

def z500 : W := mkw 0x34bf0436112ff0c0 0x834bf0436112ff0c 0xa03f0076000ff0c2 0x0a03f0076000ff0c

def z501 : W := mkw 0x000100028020b050 0x4000100028020b05 0x0007000780007000 0x0000700078000700

def z502 : W := mkw 0x109456b6c5965ddc 0xc109456b6c5965dd 0xb1b4ffffc78e7fff 0x7b1b4ffffc78e7ff

def z503 : W := mkw 0x4200f2806ed00f0e 0x04200f2806ed00f0 0x4e00e0007ff00f0c 0xf4e00e0007ff00f0

def z504 : W := mkw 0x4b40fbd86ed20faf 0x04b40fbd86ed20fa 0xdfc0fff87ff00ffd 0xfdfc0fff87ff00ff

def z505 : W := mkw 0x000100808030a110 0x4000100808030a11 0x4000000000718330 0x0400000000071833

def z506 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xae38c078780f80f2 0x5ae38c078780f80f

def z507 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee7ff1fff80f8fff 0xfee7ff1fff80f8ff

def z508 : W := mkw 0x26bfe058592feaa9 0x026bfe058592feaa 0xee3fe078780ffffe 0xfee3fe078780ffff

def z509 : W := mkw 0x2dff0080b37de110 0x42dff0080b37de11 0x6fff2189fffff33b 0xf6fff2189fffff33

def z510 : W := mkw 0x2dff1082b77df550 0x42dff1082b77df55 0x6fff00007ffffffb 0xf6fff00007ffffff

def z511 : W := mkw 0x0dfe042400000000 0x00dfe04240000000 0x9fffde7600000007 0xe9fffde760000000

def z512 : W := mkw 0x2f6ba0483a69a221 0x02f6ba0483a69a22 0x4e4b200838718330 0x84e4b20083871833

def z513 : W := mkw 0x2dfe0000334d4000 0x02dfe0000334d400 0x0fff00007b8e0003 0xf0fff00007b8e000

def z514 : W := mkw 0x10944436410658c8 0x810944436410658c 0xa034c076400e7cce 0x7a034c076400e7cc

def z515 : W := mkw 0x5bd5ffb6eff6ffde 0xc5bd5ffb6eff6ffd 0xffffffffffffffff 0xffffffffffffffff

def z516 : W := mkw 0x1094563445864c8c 0x81094563445864c8 0x11b0de70478e0c0d 0x711b0de70478e0c0

def z517 : W := mkw 0x2dff4010736fe888 0x02dff4010736fe88 0xefffc0707ffffccf 0xfefffc0707ffffcc

def z518 : W := mkw 0x1000120205845444 0x8100012020584544 0x0000000007807000 0x0000000000780700

def z519 : W := mkw 0x4f68e9d87a5b0bab 0x04f68e9d87a5b0ba 0xee78e1f8787f8ffe 0xfee78e1f8787f8ff

def z520 : W := mkw 0x4f68fbd87edb0faf 0x04f68fbd87edb0fa 0x5ff0fff07ffe0f0d 0xf5ff0fff07ffe0f0

def z521 : W := mkw 0x0094042400000000 0x0009404240000000 0x11841e0600000001 0x011841e060000000

def z522 : W := mkw 0x0201f082cc30bf58 0x40201f082cc30bf5 0xee4ff18ffc71ffff 0xfee4ff18ffc71fff

def z523 : W := mkw 0x0ffea90000000000 0x00ffea9000000000 0x1fffff8000000007 0xe1fffff800000000

def z524 : W := mkw 0x24be0000110d4000 0x024be0000110d400 0x00300000000e0000 0x000300000000e000

def z525 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1ff0fff000000005 0xe1ff0fff00000000

def z526 : W := mkw 0x24bf0000112de000 0x024bf0000112de00 0x6e3f0000780ff00a 0xf6e3f0000780ff00

def z527 : W := mkw 0x04280058100b00a1 0x004280058100b00a 0xee380078780f80fa 0xfee380078780f80f

def z528 : W := mkw 0x2dff1002376df440 0x02dff1002376df44 0xefff10067ffffccf 0xfefff10067ffffcc

def z529 : W := mkw 0x29d700002364e000 0x029d700002364e00 0x21f7000047fe700b 0x721f7000047fe700

def z530 : W := mkw 0x0b40fb0044800c0c 0x00b40fb0044800c0 0x1fc0ff8047800c0d 0xf1fc0ff8047800c0

def z531 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe00820080471fffe 0xae00820080471fff

def z532 : W := mkw 0x0094000000000000 0x0009400000000000 0x01b4000000000003 0x601b400000000000

def z533 : W := mkw 0x0628e04858090a29 0x00628e04858090a2 0x4e08e00878018f3c 0xf4e08e00878018f3

def z534 : W := mkw 0x8ffead6d22400000 0x08ffead6d2240000 0xdffffffffff0000f 0xfdffffffffff0000

def z535 : W := mkw 0x0000000022400000 0x0000000002240000 0x400000007ff00008 0x1400000007ff0000

def z536 : W := mkw 0x294300002260a000 0x0294300002260a00 0x0043000000700000 0x0004300000070000

def z537 : W := mkw 0x2d6b1082b679b550 0x42d6b1082b679b55 0xee4f318fbc71ffff 0xaee4f318fbc71fff

def z538 : W := mkw 0x00015282c4b0bd5c 0x400015282c4b0bd5 0xf1cfff8fc7f1ffff 0xff1cfff8fc7f1fff

def z539 : W := mkw 0x0200e05848020aa9 0x00200e05848020aa 0xe008e07800018ffe 0xae008e07800018ff

def z540 : W := mkw 0x10941636058654c4 0x810941636058654c 0xb1b41e76078e70c3 0x0b1b41e76078e70c

def z541 : W := mkw 0x59d45fb667d65dce 0x859d45fb667d65dc 0xb1f4dff647fe7ccf 0x7b1f4dff647fe7cc

def z542 : W := mkw 0x1dfe563645865ccc 0x81dfe563645865cc 0xbfffde76478e7ccf 0xfbfffde76478e7cc

def z543 : W := mkw 0xa9d70d252364e000 0x0a9d70d252364e00 0x11c71f8787f07001 0x011c71f8787f0700

def z544 : W := mkw 0x1094062401844004 0x8109406240184400 0x11800e0003800000 0x011800e000380000

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000318f80000004 0x08000318f8000000

def z546 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fbfce7f80000002 0x49fbfce7f8000000

def z547 : W := mkw 0x109556b6c5b6fddc 0xc109556b6c5b6fdd 0xf1b4de7647ffffff 0x7f1b4de7647fffff

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x800f000f80000002 0x0800f000f8000000

def z549 : W := mkw 0xcffeffed6ed00f0e 0x0cffeffed6ed00f0 0x5ff0fff07ff00f0d 0xf5ff0fff07ff00f0

def z550 : W := mkw 0x94be047f010650c0 0x894be047f010650c 0xa03f007f800e70c2 0x0a03f007f800e70c

def z551 : W := mkw 0x000110828430b550 0x4000110828430b55 0x604031800471fffd 0xa604031800471fff

def z552 : W := mkw 0x40015282eef0bf5e 0x440015282eef0bf5 0x600000007ff1fff8 0x1600000007ff1fff

def z553 : W := mkw 0x1094521245865ccc 0x81094521245865cc 0x21b40000478e7ccb 0x721b40000478e7cc

def z554 : W := mkw 0x0094000001044000 0x0009400000104400 0x20340000000e7002 0x020340000000e700

def z555 : W := mkw 0x20000000334d4000 0x020000000334d400 0x000000007b8e0000 0x1000000007b8e000

def z556 : W := mkw 0x06bce47c580b0aa9 0x006bce47c580b0aa 0xffbcfe7e780f8fff 0xfffbcfe7e780f8ff

def z557 : W := mkw 0x000110828430b550 0x4000110828430b55 0x0000000004707000 0x0000000000470700

def z558 : W := mkw 0x4b40fb907edb0faf 0x04b40fb907edb0fa 0x7fc0ff807fff8ffd 0xf7fc0ff807fff8ff

def z559 : W := mkw 0x3001521277effccc 0x83001521277effcc 0x600000007ffffcc8 0x1600000007ffffcc

def z560 : W := mkw 0xdffeffff6fd65fce 0x8dffeffff6fd65fc 0xfffffffffffe7fcf 0xffffffffffffe7fc

def z561 : W := mkw 0x0200e05848020aa9 0x00200e05848020aa 0xa030e078400e0ffe 0x7a030e078400e0ff

def z562 : W := mkw 0x0428000010090000 0x0042800001009000 0xee382008780f8ffe 0xfee382008780f8ff

def z563 : W := mkw 0x49405b806ed00f0e 0x049405b806ed00f0 0x51c01f807ff00f09 0x151c01f807ff00f0

def z564 : W := mkw 0x0628e05848020aa9 0x00628e05848020aa 0x8e38e07800000ff6 0xe8e38e07800000ff

def z565 : W := mkw 0x6ffefb807fdd4f0e 0x06ffefb807fdd4f0 0x5ff0ff807ffe0f0d 0xf5ff0ff807ffe0f0

def z566 : W := mkw 0x16bce67c598f4aad 0x816bce67c598f4aa 0x1fb0ce707b8e0000 0x51fb0ce707b8e000

def z567 : W := mkw 0x8ffead7d100b00a1 0x08ffead7d100b00a 0xbfffffff800f80f7 0xebfffffff800f80f

def z568 : W := mkw 0x2d6b00003269a000 0x02d6b00003269a00 0x4fcb00007ff18009 0xf4fcb00007ff1800

def z569 : W := mkw 0x10015292c5b6fddc 0xc10015292c5b6fdd 0xe04f318fc7ffffff 0xbe04f318fc7fffff

def z570 : W := mkw 0x04be000000000000 0x004be00000000000 0x003f000000000002 0x0003f00000000000

def z571 : W := mkw 0x209700000124e000 0x0209700000124e00 0x0007000000007000 0x0000700000000700

def z572 : W := mkw 0x1094043401064080 0x8109404340106408 0x00300070000e0000 0x000300070000e000

def z573 : W := mkw 0x0940000022400000 0x0094000002240000 0x0f8000007b800000 0x50f8000007b80000

def z574 : W := mkw 0x1094562645845c4c 0x81094562645845c4 0x1184de0647807c0d 0x71184de0647807c0

def z575 : W := mkw 0x29d700002364e000 0x029d700002364e00 0x61cf000007f1f00b 0xa61cf000007f1f00

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z577 : W := mkw 0x1000521245865ccc 0x81000521245865cc 0xa0041006478e7ccf 0x3a0041006478e7cc

def z578 : W := mkw 0x8dfe0d6d00000000 0x08dfe0d6d0000000 0x91ff1fff80000003 0x091ff1fff8000000

def z579 : W := mkw 0x1000521244821ccc 0x81000521244821cc 0x0000000000000cc0 0x00000000000000cc

def z580 : W := mkw 0x0000108004100500 0x0000010800410050 0xc04f318f84700f0f 0xac04f318f84700f0

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x004b218980000000 0x8004b21898000000

def z582 : W := mkw 0x109446344186488c 0x8109446344186488 0x91b4de76438e0007 0x791b4de76438e000

def z583 : W := mkw 0x0094443440020888 0x0009444344002088 0xb1b4de76400e0ccf 0x7b1b4de76400e0cc

def z584 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1fcf3f8f80000001 0x81fcf3f8f8000000

def z585 : W := mkw 0x0b40a90000000000 0x00b40a9000000000 0x0e40218000000000 0x80e4021800000000

def z586 : W := mkw 0x8ffffdffdc3bbff9 0x48ffffdffdc3bbff 0xfffffffffc7fffff 0xffffffffffc7ffff

def z587 : W := mkw 0x0000042400000000 0x0000004240000000 0x9000de7600000004 0x09000de760000000

def z588 : W := mkw 0x84be046d00000000 0x084be046d0000000 0x0030007000000000 0x0003000700000000

def z589 : W := mkw 0x49405b8066d00d0e 0x049405b8066d00d0 0x11c0df8047f00c0d 0x711c0df8047f00c0

def z590 : W := mkw 0x2629e0587b6feaa9 0x02629e0587b6feaa 0xee38e0787ffffffe 0xfee38e0787ffffff

def z591 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x6e38c070780f800a 0xf6e38c070780f800

def z592 : W := mkw 0x109516a685b4f554 0xc109516a685b4f55 0x11c71f8787f07001 0x011c71f8787f0700

def z593 : W := mkw 0x0628a058180b02a1 0x00628a058180b02a 0xee382078380f83f2 0x8ee382078380f83f

def z594 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x8e7f21ff80000002 0x88e7f21ff8000000

def z595 : W := mkw 0x4628f2d87edb0faf 0x04628f2d87edb0fa 0xee38e0787fff8ffe 0xfee38e0787fff8ff

def z596 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xa0340076478e7cca 0x1a0340076478e7cc

def z597 : W := mkw 0xcf6afbc96ed00f0e 0x0cf6afbc96ed00f0 0x5fcbff89fff00f0d 0xf5fcbff89fff00f0

def z598 : W := mkw 0x0f68e958580b0aa9 0x00f68e958580b0aa 0xfff8fff8780f8fff 0xffff8fff8780f8ff

def z599 : W := mkw 0x2dfe0000334d4000 0x02dfe0000334d400 0x6fb800007b8f800a 0xf6fb800007b8f800

def z600 : W := mkw 0xafffbdefb77df550 0x4afffbdefb77df55 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x000110828430b550 0x4000110828430b55 0xa047118784707ccf 0x2a047118784707cc

def z602 : W := mkw 0x000110020420b440 0x0000110020420b44 0xe04f10060471fccf 0xae04f10060471fcc

def z603 : W := mkw 0x6fffeb007bedea0e 0x06fffeb007bedea0 0x7fffce007ffff00b 0xf7fffce007ffff00

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x8030c07000000006 0x68030c0700000000

def z605 : W := mkw 0x0000520044800c0c 0x00000520044800c0 0x1000de0000000c04 0x01000de0000000c0

def z606 : W := mkw 0x0000108004100500 0x0000010800410050 0x0000318000000f04 0x00000318000000f0

def z607 : W := mkw 0x4b41fb82eef0bf5e 0x44b41fb82eef0bf5 0x7fc0ff807ff1fffd 0xf7fc0ff807ff1fff

def z608 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6e7f0000387ff002 0x86e7f0000387ff00

def z609 : W := mkw 0x0629b0ca8430b550 0x40629b0ca8430b55 0xee7ff1ff8471ffff 0xeee7ff1ff8471fff

def z610 : W := mkw 0x009500000124e000 0x0009500000124e00 0x61ff000047fff00b 0xf61ff000047fff00

def z611 : W := mkw 0x29d71082a774f550 0x429d71082a774f55 0xe1cf318f87f1ffff 0xae1cf318f87f1fff

def z612 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fb0ffff80000004 0x49fb0ffff8000000

def z613 : W := mkw 0x8200ad6d00000000 0x08200ad6d0000000 0x1000ce7000000000 0x01000ce700000000

def z614 : W := mkw 0x39d7563667e6fccc 0x839d7563667e6fcc 0xb1f7de7647fe7ccf 0x7b1f7de7647fe7cc

def z615 : W := mkw 0x4201fb82ccb0bf5e 0x44201fb82ccb0bf5 0xf04fff8f8471ffff 0xaf04fff8f8471fff

def z616 : W := mkw 0x0000401040020888 0x0000040104002088 0xe038e078400f8ffe 0xfe038e078400f8ff

def z617 : W := mkw 0x4f69fbdafefbbfff 0x44f69fbdafefbbff 0xffffffffffffffff 0xffffffffffffffff

def z618 : W := mkw 0x4f68fb807ed90f0e 0x04f68fb807ed90f0 0x7ff8ff807fff8f0f 0xf7ff8ff807fff8f0

def z619 : W := mkw 0x00015092dc3bbff9 0x400015092dc3bbff 0xe04f318ffc7fffff 0xbe04f318ffc7ffff

def z620 : W := mkw 0x1bd4ff3645865ccc 0x81bd4ff3645865cc 0xbff4fff6478e7ccf 0xfbff4fff6478e7cc

def z621 : W := mkw 0x0000521044820c8c 0x00000521044820c8 0xb1b0de70478e0ccf 0x7b1b0de70478e0cc

def z622 : W := mkw 0x06bce058590f4aa9 0x006bce058590f4aa 0xefbce0787f8fffff 0xfefbce0787f8ffff

def z623 : W := mkw 0x1628f67e5c8b1eed 0x81628f67e5c8b1ee 0xfe38fe7e780f8ffe 0xffe38fe7e780f8ff

def z624 : W := mkw 0x8f6bb9cb8430b550 0x48f6bb9cb8430b55 0xee4f318f8471ffff 0xaee4f318f8471fff

def z625 : W := mkw 0x0000400048000a08 0x00000400048000a0 0x4000000078000f08 0x14000000078000f0

def z626 : W := mkw 0x0d68000032490000 0x00d6800003249000 0x6ff800007fff800b 0xf6ff800007fff800

def z627 : W := mkw 0x0428004800000000 0x0042800480000000 0x8038007800000002 0x0803800780000000

def z628 : W := mkw 0x49411b82a6f0b556 0x449411b82a6f0b55 0xf1cf3f8f87f1ffff 0xaf1cf3f8f87f1fff

def z629 : W := mkw 0x5bd4ef346bc64a8e 0x85bd4ef346bc64a8 0x1fb0ce707b8e0000 0x51fb0ce707b8e000

def z630 : W := mkw 0x10955636c5a6fcdc 0xc10955636c5a6fcd 0xb1bfde7fc78ffcff 0x7b1bfde7fc78ffcf

def z631 : W := mkw 0x0000528044900d0c 0x00000528044900d0 0x51c0ff8047f00f0d 0xf51c0ff8047f00f0

def z632 : W := mkw 0x1094042601045040 0x8109404260104504 0x0004000600007000 0x0000400060000700

def z633 : W := mkw 0x84be046d00000000 0x084be046d0000000 0x807f31ff80000007 0xa807f31ff8000000

def z634 : W := mkw 0x0000520044800c0c 0x00000520044800c0 0x0000000047800c08 0x10000000047800c0

def z635 : W := mkw 0xbfffff7f77effccc 0x8bfffff7f77effcc 0xfffffffffffffccf 0xffffffffffffffcc

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008200800018330 0x8400820080001833

def z637 : W := mkw 0x0000008080100110 0x4000000808010011 0x0000218980000330 0x0000021898000033

def z638 : W := mkw 0xcffeef6d6ac00a0e 0x0cffeef6d6ac00a0 0x9ffffffffb800007 0xf9ffffffffb80000

def z639 : W := mkw 0x49400b0022c00006 0x049400b0022c0000 0x11800e0003800000 0x011800e000380000

def z640 : W := mkw 0x4200fbd84c920faf 0x04200fbd84c920fa 0x9000fff800000ff4 0x09000fff800000ff

def z641 : W := mkw 0x8b40ad6d00000000 0x08b40ad6d0000000 0x9fc0ffff80000005 0xe9fc0ffff8000000

def z642 : W := mkw 0x0000401040020888 0x0000040104002088 0x0030c070400e0000 0x50030c070400e000

def z643 : W := mkw 0x8ffeed6d48000a08 0x08ffeed6d48000a0 0xdffffffff8000f0f 0xfdffffffff8000f0

def z644 : W := mkw 0x39d7162627e4f444 0x839d7162627e4f44 0x11c71e0607f07001 0x011c71e0607f0700

def z645 : W := mkw 0x4b40fb006ec00e0e 0x04b40fb006ec00e0 0x1f80de007f800c0d 0x71f80de007f800c0

def z646 : W := mkw 0x0200f2004c800e0c 0x00200f2004c800e0 0x5f80fe007f800f0d 0xf5f80fe007f800f0

def z647 : W := mkw 0x5294ffb64d965fce 0x85294ffb64d965fc 0xb1b4fff6478e7fcf 0x7b1b4fff6478e7fc

def z648 : W := mkw 0x29d6000023444000 0x029d600002344400 0x0180000003800000 0x0018000000380000

def z649 : W := mkw 0x009510828534f550 0x4009510828534f55 0xe1ff318fc7ffffff 0xfe1ff318fc7fffff

def z650 : W := mkw 0x16bcf67e45865ccc 0x816bcf67e45865cc 0xbfbcfe7e478e7ccf 0xfbfbcfe7e478e7cc

def z651 : W := mkw 0x0094100205045440 0x0009410020504544 0xa1b41006478e7ccf 0x7a1b41006478e7cc

def z652 : W := mkw 0x8200a94900000000 0x08200a9490000000 0x0000218980000000 0x0000021898000000

def z653 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x8e38e078780e0006 0xf8e38e078780e000

def z654 : W := mkw 0x1095563645a6fccc 0x81095563645a6fcc 0xf1ffde7647fffccf 0xff1ffde7647fffcc

def z655 : W := mkw 0x0628a04818090221 0x00628a0481809022 0x6e382008780f833a 0xf6e382008780f833

def z656 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe00410060471ffff 0x2e00410060471fff

def z657 : W := mkw 0x000100000020a000 0x0000100000020a00 0xe04f318f8471f00f 0xae04f318f8471f00

def z658 : W := mkw 0x2fffa900336de000 0x02fffa900336de00 0x7fffff807ffff00f 0xf7fffff807ffff00

def z659 : W := mkw 0x6ffffb82fffdff5e 0x46ffffb82fffdff5 0xffffff8fffffffff 0xfffffff8ffffffff

def z660 : W := mkw 0x000100028020b050 0x4000100028020b05 0x200000000001f0f0 0x0200000000001f0f

def z661 : W := mkw 0x8200ed7d48020aa9 0x08200ed7d48020aa 0x9000ffff80000ff4 0x09000ffff80000ff

def z662 : W := mkw 0x400052806ed00f0e 0x0400052806ed00f0 0x5180de007ff00f0d 0x75180de007ff00f0

def z663 : W := mkw 0x0429005a902bb0f1 0x40429005a902bb0f 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z664 : W := mkw 0x100056b6c4921ddc 0xc100056b6c4921dd 0x9000ffff80000ff4 0x09000ffff80000ff

def z665 : W := mkw 0x0940108026500500 0x0094010802650050 0x4fc031807ff00f0d 0xf4fc031807ff00f0

def z666 : W := mkw 0x0dfe000001044000 0x00dfe00000104400 0x2fff0000478e700b 0xf2fff0000478e700

def z667 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x91b0de76438e0cc4 0x591b0de76438e0cc

def z668 : W := mkw 0x99d65f3745865ccc 0x899d65f3745865cc 0xb1f7dff7c78e7ccf 0x7b1f7dff7c78e7cc

def z669 : W := mkw 0x0628a04810090000 0x00628a0481009000 0xee38e078780f800e 0xfee38e078780f800

def z670 : W := mkw 0x0200e05848020aa9 0x00200e05848020aa 0xce00e07878000ffc 0xfce00e07878000ff

def z671 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x5f80ee007b800f0c 0xf5f80ee007b800f0

def z672 : W := mkw 0x2fffe0007b6dea08 0x02fffe0007b6dea0 0x6fffe0007fffff0f 0xf6fffe0007fffff0

def z673 : W := mkw 0x0094042400000000 0x0009404240000000 0x11b0ce7000000000 0x411b0ce700000000

def z674 : W := mkw 0x8200bdef84101550 0x48200bdef8410155 0x9000ffff80000ff4 0x09000ffff80000ff

def z675 : W := mkw 0x24bf0000112de000 0x024bf0000112de00 0x21bf0000478ff00b 0x721bf0000478ff00

def z676 : W := mkw 0x8294ad6d00000000 0x08294ad6d0000000 0x91b4ffff80000007 0x691b4ffff8000000

def z677 : W := mkw 0x0200a00000000000 0x00200a0000000000 0x0e00e00000000004 0xe0e00e0000000000

def z678 : W := mkw 0x0dff10828430b550 0x40dff10828430b55 0xefff318f8471ffff 0xeefff318f8471fff

def z679 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x4ffb00007bff8000 0xd4ffb00007bff800

def z680 : W := mkw 0x04280058100b00a1 0x004280058100b00a 0x00300070000e0000 0x000300070000e000

def z681 : W := mkw 0x242b00001029a000 0x0242b00001029a00 0x000b000000018000 0x0000b00000001800

def z682 : W := mkw 0x0b41b9828430b550 0x40b41b9828430b55 0xffcfff8f8471ffff 0xeffcfff8f8471fff

def z683 : W := mkw 0x14bc567e558f5ced 0x814bc567e558f5ce 0xb1bcde7e478ffcff 0x7b1bcde7e478ffcf

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0xe04f318f80018fff 0xae04f318f80018ff

def z685 : W := mkw 0x0628f0d85c1b0fa9 0x00628f0d85c1b0fa 0xee78f1f87c7f8fff 0xfee78f1f87c7f8ff

def z686 : W := mkw 0x4f68eb587acb0aaf 0x04f68eb587acb0aa 0xffb8ee787b8f8ffe 0xfffb8ee787b8f8ff

def z687 : W := mkw 0x84bf046f8020b050 0x484bf046f8020b05 0xa03f007f8001f0f2 0x0a03f007f8001f0f

def z688 : W := mkw 0x1000563644821ccc 0x81000563644821cc 0x9180de7647800ccd 0x79180de7647800cc

def z689 : W := mkw 0x6f6bfb807ef9af0e 0x06f6bfb807ef9af0 0x5fcbff807ff18f0d 0xf5fcbff807ff18f0

def z690 : W := mkw 0x0200f0804c100f08 0x00200f0804c100f0 0x4e40f1807c700f0d 0xf4e40f1807c700f0

def z691 : W := mkw 0x0b40b98004100500 0x00b40b9800410050 0x5fc0ff8004700f0d 0xe5fc0ff8004700f0

def z692 : W := mkw 0x8dfe046d00000000 0x08dfe046d0000000 0x8fff007f80000003 0xe8fff007f8000000

def z693 : W := mkw 0x109504368126f0d0 0xc109504368126f0d 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z694 : W := mkw 0x0629e0d8d83babb9 0x40629e0d8d83babb 0xee7be1f9f87f8ffe 0xfee7be1f9f87f8ff

def z695 : W := mkw 0x8ffeed7d580b0aa9 0x08ffeed7d580b0aa 0x1fb0ce70780e0000 0x51fb0ce70780e000

def z696 : W := mkw 0x0d6a000000000000 0x00d6a00000000000 0x0e4b000000000000 0x80e4b00000000000

def z697 : W := mkw 0x0000100004000400 0x0000010000400040 0x0000100004000c0d 0x20000100004000c0

def z698 : W := mkw 0x4f68fbc86ed00f0e 0x04f68fbc86ed00f0 0xdff8fff87ff00f0f 0xfdff8fff87ff00f0

def z699 : W := mkw 0x5b40fb926fd65fce 0x85b40fb926fd65fc 0x7fc0ff807ffe7fcd 0xf7fc0ff807ffe7fc

def z700 : W := mkw 0x19d4563667c65ccc 0x819d4563667c65cc 0xfff4de767ffe7ccf 0xffff4de767ffe7cc

def z701 : W := mkw 0x100046344082088c 0x8100046344082088 0x1000ce7000000000 0x01000ce700000000

def z702 : W := mkw 0x4b41fb806ef0af0e 0x04b41fb806ef0af0 0x7fcfff807ff1ff0f 0xf7fcfff807ff1ff0

def z703 : W := mkw 0x0629f0dadc3bbff9 0x40629f0dadc3bbff 0xee38e0787c7ffffe 0xfee38e0787c7ffff

def z704 : W := mkw 0xcffeffed4c900f0e 0x0cffeffed4c900f0 0x9fffffff80000f07 0xe9fffffff80000f0

def z705 : W := mkw 0x000110828430b550 0x4000110828430b55 0x604f00000471fffb 0xa604f00000471fff

def z706 : W := mkw 0x40015282eef0bf5e 0x440015282eef0bf5 0xe04f318ffff1ffff 0xbe04f318ffff1fff

def z707 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1f7dff7c78e7ccf 0x7b1f7dff7c78e7cc

def z708 : W := mkw 0x89d64d35580b0aa9 0x089d64d35580b0aa 0x71c71f87f80f8ff9 0x171c71f87f80f8ff

def z709 : W := mkw 0x8ffead6d18090221 0x08ffead6d1809022 0xfffffffff80f833f 0xffffffffff80f833

def z710 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6ff000007ffff009 0xf6ff000007ffff00

def z711 : W := mkw 0x8bd6ad2500000000 0x08bd6ad250000000 0x9ff7fff780000007 0xe9ff7fff78000000

def z712 : W := mkw 0x9f6afb5b45865ccc 0x89f6afb5b45865cc 0x2e4b2189c78e7cc8 0x92e4b2189c78e7cc

def z713 : W := mkw 0xa201ad6d336de000 0x0a201ad6d336de00 0xf000fffffffff00c 0x1f000fffffffff00

def z714 : W := mkw 0x0629f0dadc3bbff9 0x40629f0dadc3bbff 0x0e77d1f7fc7e7001 0x50e77d1f7fc7e700

def z715 : W := mkw 0xc4be56ed6ed00f0e 0x0c4be56ed6ed00f0 0xc03f007ffff00f0a 0x1c03f007ffff00f0

def z716 : W := mkw 0x109456b645965dcc 0x8109456b645965dc 0xb1f4dff647fe7ccf 0x7b1f4dff647fe7cc

def z717 : W := mkw 0x0b40a90022400000 0x00b40a9002240000 0x5fc0ce007ff00009 0xf5fc0ce007ff0000

def z718 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b0ce70478e7cce 0x7b1b0ce70478e7cc

def z719 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee7be1f9f80f8ffe 0xfee7be1f9f80f8ff

def z720 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xefb8e0787f8f8fff 0xfefb8e0787f8f8ff

def z721 : W := mkw 0x0bd4ad2400000000 0x00bd4ad240000000 0x9fffffff80000007 0xe9fffffff8000000

def z722 : W := mkw 0x0b40fb0066c00c0c 0x00b40fb0066c00c0 0x5fc0ff807ff00c0d 0xf5fc0ff807ff00c0

def z723 : W := mkw 0x8200ad6d00000000 0x08200ad6d0000000 0x904bffff80000004 0x8904bffff8000000

def z724 : W := mkw 0x34bf0434112fe080 0x834bf0434112fe08 0x203f0070000ff002 0x0203f0070000ff00

def z725 : W := mkw 0x2dff0424336de000 0x02dff0424336de00 0x7fff1e067ffff00b 0xf7fff1e067ffff00

def z726 : W := mkw 0x2dff0048336de000 0x02dff0048336de00 0xefff00787ffff00b 0xfefff00787ffff00

def z727 : W := mkw 0x0b40f2006ec00e0c 0x00b40f2006ec00e0 0x5fc0fe007ff00f0d 0xf5fc0fe007ff00f0

def z728 : W := mkw 0xaffead6d334d4000 0x0affead6d334d400 0xbfffffffff8e700f 0xfbfffffffff8e700

def z729 : W := mkw 0x0940000022400000 0x0094000002240000 0x5fc0de007ff0000d 0xf5fc0de007ff0000

def z730 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff31807ffff00f 0xf6fff31807ffff00

def z731 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4de76078e7cc7 0x0b1b4de76078e7cc

def z732 : W := mkw 0x2d6b0000336de000 0x02d6b0000336de00 0x6fcb00007ffff009 0xf6fcb00007ffff00

def z733 : W := mkw 0x34bf0436912ff0d0 0xc34bf0436912ff0d 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z734 : W := mkw 0x0628a058180b02a1 0x00628a058180b02a 0xee382078380f8ffe 0xaee382078380f8ff

def z735 : W := mkw 0x494052806ed00f0e 0x0494052806ed00f0 0x5fc0de007ff00f0d 0xf5fc0de007ff00f0

def z736 : W := mkw 0x10944636418658cc 0x810944636418658c 0x31b0ce70438e70c0 0x531b0ce70438e70c

def z737 : W := mkw 0x109546b4c1b6e99c 0xc109546b4c1b6e99 0x51fbeff9c3ff8330 0xd51fbeff9c3ff833

def z738 : W := mkw 0x4628eb58588b0aaf 0x04628eb58588b0aa 0xfe38ee78780f8ffe 0xffe38ee78780f8ff

def z739 : W := mkw 0x04284058580b0aa9 0x004284058580b0aa 0xee380078780f8ffa 0xfee380078780f8ff

def z740 : W := mkw 0x10944636418658cc 0x810944636418658c 0x11b4ce76438e7000 0x511b4ce76438e700

def z741 : W := mkw 0x862aad6d00000000 0x0862aad6d0000000 0x900bffff80000004 0x0900bffff8000000

def z742 : W := mkw 0x3d6b563676ebbccc 0x83d6b563676ebbcc 0xde4bde7638718cc4 0x8de4bde7638718cc

def z743 : W := mkw 0x109456b645965dcc 0x8109456b645965dc 0xf1ffffffc7fe7fcf 0xff1ffffffc7fe7fc

def z744 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xdfffffff80018337 0xedfffffff8001833

def z745 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x1fc0ff807ff00f05 0x51fc0ff807ff00f0

def z746 : W := mkw 0x4b40fb826ed01f4e 0x04b40fb826ed01f4 0xffccff8e7ff1ffff 0xfffccff8e7ff1fff

def z747 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x4fff00007ffff001 0xd4fff00007ffff00

def z748 : W := mkw 0x2dff0000b36de010 0x42dff0000b36de01 0x6fff0009fffff03b 0xf6fff0009fffff03

def z749 : W := mkw 0x109456b645965dcc 0x8109456b645965dc 0xb1b4fff6478e7fcf 0x7b1b4fff6478e7fc

def z750 : W := mkw 0x09d500002364e000 0x009d500002364e00 0x6fff00007ffff00b 0xf6fff00007ffff00

def z751 : W := mkw 0x4f69a9c8ba79a333 0x44f69a9c8ba79a33 0x4e4b2189b8718330 0x84e4b2189b871833

def z752 : W := mkw 0xadff046d336de000 0x0adff046d336de00 0xffffde7ffffff00f 0xfffffde7ffffff00

def z753 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9ff7dff780000007 0x69ff7dff78000000

def z754 : W := mkw 0x1200f6fecc921ffd 0xc1200f6fecc921ff 0x9000ffff80000ff4 0x09000ffff80000ff

def z755 : W := mkw 0x2bd7e0586b66eaa9 0x02bd7e0586b66eaa 0x81c7e07807f07ff5 0x081c7e07807f07ff

def z756 : W := mkw 0x4b40fb826ed01f4e 0x04b40fb826ed01f4 0xffcfff8ffff07fcf 0xfffcfff8ffff07fc

def z757 : W := mkw 0x16bcb66e1d8d5665 0x816bcb66e1d8d566 0x5f8c3e0e3f81f331 0x85f8c3e0e3f81f33

def z758 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xffb4de767f8e7ccf 0xfffb4de767f8e7cc

def z759 : W := mkw 0x109456364d865eed 0x8109456364d865ee 0xb1b4de76478e7fff 0x7b1b4de76478e7ff

def z760 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fffffffc780000f 0xf9fffffffc780000

def z761 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x2ff700007ffe700b 0x72ff700007ffe700

def z762 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x6e38e078780f8ff8 0xd6e38e078780f8ff

def z763 : W := mkw 0x0dfe042400000000 0x00dfe04240000000 0x9fffffff80000007 0xe9fffffff8000000

def z764 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x6e38c070780f8ffa 0xf6e38c070780f8ff

def z765 : W := mkw 0x0628e958580b0aa9 0x00628e958580b0aa 0xfe38fff8780f8ffe 0xffe38fff8780f8ff

def z766 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xdfc8ff887ff00f0f 0xfdfc8ff887ff00f0

def z767 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fcbff89fff00f0d 0xf5fcbff89fff00f0

def z768 : W := mkw 0x4b40bb802ed00706 0x04b40bb802ed0070 0x5fc03f803ff00f0d 0xa5fc03f803ff00f0

def z769 : W := mkw 0x8ffead6d10090000 0x08ffead6d1009000 0x9ffffffff80e0007 0xf9ffffffff80e000

def z770 : W := mkw 0x4b40fb906ed20f8e 0x04b40fb906ed20f8 0xfff8fff87fff8fff 0xffff8fff87fff8ff

def z771 : W := mkw 0x24bd0000336de000 0x024bd0000336de00 0x6fbc00007ffff00b 0xf6fbc00007ffff00

def z772 : W := mkw 0x109456364d865ecc 0x8109456364d865ec 0xf1b4de767f8e7fcf 0x7f1b4de767f8e7fc

def z773 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1f4fff6478e7ccf 0xfb1f4fff6478e7cc

def z774 : W := mkw 0x2d6b0000336de000 0x02d6b0000336de00 0x6e0000007ffff008 0x16e0000007ffff00

def z775 : W := mkw 0xadff0d25336de000 0x0adff0d25336de00 0xffffdff7fffff00f 0xfffffdff7fffff00

def z776 : W := mkw 0x4d681bd836db05a7 0x04d681bd836db05a 0xb1f81ff807ff80f3 0x0b1f81ff807ff80f

def z777 : W := mkw 0x8f6aad6d00000000 0x08f6aad6d0000000 0x9fcbffff80000005 0xe9fcbffff8000000

def z778 : W := mkw 0x2dff0424336de000 0x02dff0424336de00 0xfffffffffffff00f 0xffffffffffffff00

def z779 : W := mkw 0x5bd4adb62b5653c2 0x85bd4adb62b5653c 0xee7421f6387e73c2 0x8ee7421f6387e73c

def z780 : W := mkw 0x66bffb805dbdef0e 0x066bffb805dbdef0 0x303fff80000fff06 0x0303fff80000fff0

def z781 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x1fc0ff807ff00005 0xf1fc0ff807ff0000

def z782 : W := mkw 0x34bf0426112df040 0x834bf0426112df04 0x203f0006000ff002 0x0203f0006000ff00

def z783 : W := mkw 0x8ffead6d22400000 0x08ffead6d2240000 0x9fffffff87f00007 0xe9fffffff87f0000

def z784 : W := mkw 0x10015292c4b2bddc 0xc10015292c4b2bdd 0x600000000471fff8 0x0600000000471fff

def z785 : W := mkw 0x49401b8026d00506 0x049401b8026d0050 0x5fc01f803ff00001 0x85fc01f803ff0000

def z786 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xf1b4de76478fffff 0x7f1b4de76478ffff

def z787 : W := mkw 0x4b40bb802ed00706 0x04b40bb802ed0070 0x5fc0ff803ff00305 0xe5fc0ff803ff0030

def z788 : W := mkw 0x10940436010650c0 0x810940436010650c 0xb1b4de76478e70cf 0x7b1b4de76478e70c

def z789 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1ff7fff780000005 0xe1ff7fff78000000

def z790 : W := mkw 0x34bf047e112ff0e1 0x834bf047e112ff0e 0xa03f007e000ff0f2 0x0a03f007e000ff0f

def z791 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee382078780f8ffa 0x9ee382078780f8ff

def z792 : W := mkw 0x109446344186488c 0x8109446344186488 0xb1b4de76478e700f 0x7b1b4de76478e700

def z793 : W := mkw 0x20010000336de000 0x020010000336de00 0x6e0000007ffff008 0xf6e0000007ffff00

def z794 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9ffbffff80000004 0xc9ffbffff8000000

def z795 : W := mkw 0x84be046d00000000 0x084be046d0000000 0x91ffffff80000007 0xe91ffffff8000000

def z796 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x91b4de76478e7cc5 0x591b4de76478e7cc

def z797 : W := mkw 0x109446344186488c 0x8109446344186488 0xb1b4ce70478e7ccf 0x7b1b4ce70478e7cc

def z798 : W := mkw 0x2dfe1082b75d5550 0x42dfe1082b75d555 0x8fb0318ffb8e0ff4 0x58fb0318ffb8e0ff

def z799 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x91ffffff80000007 0x091ffffff8000000

def z800 : W := mkw 0x24bf0424112de000 0x024bf0424112de00 0xa03f0076000ff002 0x0a03f0076000ff00

def z801 : W := mkw 0x0094443441064888 0x0009444344106488 0xb1b4de76478e7ccf 0x7b1b4de76478e7cc

def z802 : W := mkw 0x4b40fb82eed01f5e 0x44b40fb82eed01f5 0x5fc0ff87fff00f0d 0xf5fc0ff87fff00f0

def z803 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0ff807bf00f04 0xd5fc0ff807bf00f0

def z804 : W := mkw 0x49401b8026d00506 0x049401b8026d0050 0x1fc01f807ff00001 0x51fc01f807ff0000

def z805 : W := mkw 0xaffead6d23444000 0x0affead6d2344400 0x9fffffff83800007 0xe9fffffff8380000

def z806 : W := mkw 0xcb42fb816ed00f0e 0x0cb42fb816ed00f0 0x5fc3ff81fff00f0d 0xf5fc3ff81fff00f0

def z807 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xdffffffff800000f 0xfdffffffff800000

def z808 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xce38e078780f8ff4 0xdce38e078780f8ff

def z809 : W := mkw 0x29d50000336de000 0x029d50000336de00 0x6ff400007ffff00b 0xf6ff400007ffff00

def z810 : W := mkw 0x06bca46c00000000 0x006bca46c0000000 0x9fffffff80000007 0xe9fffffff8000000

def z811 : W := mkw 0x8fffbdef8430b550 0x48fffbdef8430b55 0x7fb0ce700471fff8 0x47fb0ce700471fff

def z812 : W := mkw 0x4b40fbdaeed21fff 0x44b40fbdaeed21ff 0xdfc0fffffff00ffd 0xfdfc0fffffff00ff

def z813 : W := mkw 0x8ffead6d18090221 0x08ffead6d1809022 0xffffffffb8018fff 0xeffffffffb8018ff

def z814 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x31b4ce70478e7ccb 0x731b4ce70478e7cc

def z815 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xdfffffff80000f0f 0xedfffffff80000f0

def z816 : W := mkw 0x4b41eb02eae0ba5e 0x44b41eb02eae0ba5 0xbf8fce0ffb81f0f2 0x5bf8fce0ffb81f0f

def z817 : W := mkw 0x0f68a94800000000 0x00f68a9480000000 0x9fffffff80000007 0xe9fffffff8000000

def z818 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5f80ee007ff00f0c 0xf5f80ee007ff00f0

def z819 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee3fe07ff80f8ffe 0xfee3fe07ff80f8ff

def z820 : W := mkw 0x8294ad6d00000000 0x08294ad6d0000000 0x91ffffff80000007 0xe91ffffff8000000

def z821 : W := mkw 0x49405b806ed00f0e 0x049405b806ed00f0 0x5fc01f807ff00f09 0xf5fc01f807ff00f0

def z822 : W := mkw 0x29410000336de000 0x029410000336de00 0x6e4000007ffff008 0x96e4000007ffff00

def z823 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x1f80ce007ff00000 0x51f80ce007ff0000

def z824 : W := mkw 0x24290000336de000 0x024290000336de00 0x6e7f00007ffff00b 0xf6e7f00007ffff00

def z825 : W := mkw 0xadff046d336de000 0x0adff046d336de00 0xefff31fffffff00f 0xfefff31fffffff00

def z826 : W := mkw 0x24290000336de000 0x024290000336de00 0x6e3000007ffff008 0x56e3000007ffff00

def z827 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff10067ffff00f 0xfefff10067ffff00

def z828 : W := mkw 0x0001128284b0b554 0x40001128284b0b55 0xf1cf3f8f87f1ffff 0xaf1cf3f8f87f1fff

def z829 : W := mkw 0x9096563745865ccc 0x89096563745865cc 0xb1b7de77c78e7ccf 0x7b1b7de77c78e7cc

def z830 : W := mkw 0xaffeed7d7b4f4aa9 0x0affeed7d7b4f4aa 0x1fb0ce707b8e0000 0x51fb0ce707b8e000

def z831 : W := mkw 0x29410000336de000 0x029410000336de00 0x6fcf00007ffff00b 0xf6fcf00007ffff00

def z832 : W := mkw 0x86bead6d00000000 0x086bead6d0000000 0x91bfffff80000007 0x691bfffff8000000

def z833 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff1187fffff00b 0xf6fff1187fffff00

def z834 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe07f318fc47fffff 0xfe07f318fc47ffff

def z835 : W := mkw 0xadff0425336de000 0x0adff0425336de00 0x6fff0007fffff00b 0xf6fff0007fffff00

def z836 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee78f1f8780f8fff 0xfee78f1f8780f8ff

def z837 : W := mkw 0x1000521245865ccc 0x81000521245865cc 0xb1b0de70478e7ccf 0x7b1b0de70478e7cc

def z838 : W := mkw 0x10015292c5b6fddc 0xc10015292c5b6fdd 0x2000000047fe7cc8 0x12000000047fe7cc

def z839 : W := mkw 0x0b40b98026500500 0x00b40b9802650050 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z840 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fffffff80000ff7 0xe9fffffff80000ff

def z841 : W := mkw 0x10015292ddbffffd 0xc10015292ddbffff 0x600000007ffffff8 0x1600000007ffffff

def z842 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe07ff1ff8471ffff 0xee07ff1ff8471fff

def z843 : W := mkw 0x4b40a9802a500302 0x04b40a9802a50030 0x5fc0ff807ff0030d 0xf5fc0ff807ff0030

def z844 : W := mkw 0x8bd6ad6d00000000 0x08bd6ad6d0000000 0x91cfffff80000007 0xa91cfffff8000000

def z845 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4ffffc78e7ccf 0x7b1b4ffffc78e7cc

def z846 : W := mkw 0x0b40e9006a400a08 0x00b40e9006a400a0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z847 : W := mkw 0x109446344186488c 0x8109446344186488 0x11b4ce70478e7001 0x511b4ce70478e700

def z848 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff00007ffffffb 0xf6fff00007ffffff

def z849 : W := mkw 0x5200ffb6cc921fde 0xc5200ffb6cc921fd 0x9000ffff80000ff4 0x09000ffff80000ff

def z850 : W := mkw 0x0940120026c00404 0x00940120026c0040 0x5fc01e007ff00009 0xf5fc01e007ff0000

def z851 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1bcde7e478ffcff 0x7b1bcde7e478ffcf

def z852 : W := mkw 0x0094142605045440 0x0009414260504544 0xb1b4de76478e7ccf 0x7b1b4de76478e7cc

def z853 : W := mkw 0xadff0049336de000 0x0adff0049336de00 0x6fff0009fffff00b 0xf6fff0009fffff00

def z854 : W := mkw 0x8200ad6d00000000 0x08200ad6d0000000 0x900fffff80000006 0x0900fffff8000000

def z855 : W := mkw 0x49405b8066d00d0e 0x049405b8066d00d0 0x5fc0df807ff00c0d 0xf5fc0df807ff00c0

def z856 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc8ff887ff18f3d 0xf5fc8ff887ff18f3

def z857 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x4ff700007ffe7009 0xf4ff700007ffe700

def z858 : W := mkw 0xadff0d6d336de000 0x0adff0d6d336de00 0xffff1ffffffff00b 0xfffff1ffffffff00

def z859 : W := mkw 0x4b40bb802ed00706 0x04b40bb802ed0070 0x5fc03f807ff00309 0xf5fc03f807ff0030

def z860 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc7ff87fff00f0d 0xf5fc7ff87fff00f0

def z861 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xdfc4ff867ff00f0f 0xfdfc4ff867ff00f0

def z862 : W := mkw 0x0200f2804c900f0c 0x00200f2804c900f0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z863 : W := mkw 0x8ffead6d01044000 0x08ffead6d0104400 0x9fffffff87807007 0xe9fffffff8780700

def z864 : W := mkw 0x8ffead6d32490000 0x08ffead6d3249000 0xffffffffffff800f 0xfffffffffffff800

def z865 : W := mkw 0x8ffead6d10090000 0x08ffead6d1009000 0xdfffffffb8018007 0xedfffffffb801800

def z866 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff00007ffffccf 0xfefff00007ffffcc

def z867 : W := mkw 0x4b40eb806ad00b0e 0x04b40eb806ad00b0 0x5fc0ef807ff00309 0xf5fc0ef807ff0030

def z868 : W := mkw 0x4b40fb906ed20f8e 0x04b40fb906ed20f8 0xdfc0fff07ff00fcd 0xfdfc0fff07ff00fc

def z869 : W := mkw 0x8ffead6d10090021 0x08ffead6d1009002 0x9fffffff80018037 0xe9fffffff8001803

def z870 : W := mkw 0x14bd047e912ff0f1 0xc14bd047e912ff0f 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z871 : W := mkw 0x4b40bb802ed00706 0x04b40bb802ed0070 0x1fc01f803ff00001 0x01fc01f803ff0000

def z872 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x11b0ce70478e7000 0x511b0ce70478e700

def z873 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xffc0ff807ff00fcf 0xfffc0ff807ff00fc

def z874 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xbfffffffc00e000f 0xfbfffffffc00e000

def z875 : W := mkw 0x04284010500b0888 0x004284010500b088 0xee38e078780f8ffe 0xfee38e078780f8ff

def z876 : W := mkw 0x24290000336de000 0x024290000336de00 0x6e0800007ffff008 0x96e0800007ffff00

def z877 : W := mkw 0x5b40fb926ed21fce 0x85b40fb926ed21fc 0x5fc0ff807ff00fcd 0xf5fc0ff807ff00fc

def z878 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fffdfff80000003 0x49fffdfff8000000

def z879 : W := mkw 0xcffead6d2a400202 0x0cffead6d2a40020 0x9fffffffb8000007 0xe9fffffffb800000

def z880 : W := mkw 0x10945636c5865cdc 0xc10945636c5865cd 0xb1b4de7fc78e7cff 0x7b1b4de7fc78e7cf

def z881 : W := mkw 0x4b40fb82eed01f5e 0x44b40fb82eed01f5 0xffc8ff8ffff18fff 0xfffc8ff8ffff18ff

def z882 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0df807ff00f09 0x55fc0df807ff00f0

def z883 : W := mkw 0x8628e959580b0aa9 0x08628e959580b0aa 0xee38e1f9f80f8ffe 0xfee38e1f9f80f8ff

def z884 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe04f218f8471fffa 0x8e04f218f8471fff

def z885 : W := mkw 0x109456b6c5965ddc 0xc109456b6c5965dd 0xb1b4de76478e7fff 0x7b1b4de76478e7ff

def z886 : W := mkw 0x4b40ab802ad00306 0x04b40ab802ad0030 0x5fc02f803bf00300 0x85fc02f803bf0030

def z887 : W := mkw 0x8b40ad6d00000000 0x08b40ad6d0000000 0x9fcfffff80000007 0xe9fcfffff8000000

def z888 : W := mkw 0xaf6ba9c9b279a110 0x4af6ba9c9b279a11 0x4e4b2189b8718330 0x84e4b2189b871833

def z889 : W := mkw 0xadff046d336de000 0x0adff046d336de00 0x6fff00707ffff00b 0xf6fff00707ffff00

def z890 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fcfffff80000005 0x89fcfffff8000000

def z891 : W := mkw 0x0094521045864c8c 0x00094521045864c8 0xb1b4de70478e7ccf 0x7b1b4de70478e7cc

def z892 : W := mkw 0x509456b64d965fce 0x8509456b64d965fc 0xb1b4de76478e7fcf 0x7b1b4de76478e7fc

def z893 : W := mkw 0xaffead6d334d4000 0x0affead6d334d400 0xfffffffffb8f800f 0xffffffffffb8f800

def z894 : W := mkw 0x000110828430b550 0x4000110828430b55 0xc04f318f8471fff5 0x8c04f318f8471fff

def z895 : W := mkw 0x000110828430b550 0x4000110828430b55 0xf1cfff8f8471ffff 0xef1cfff8f8471fff

def z896 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x0fff00007ffe7003 0xf0fff00007ffe700

def z897 : W := mkw 0x4b40bb8026d00506 0x04b40bb8026d0050 0x5fc0ff807ff0000d 0xf5fc0ff807ff0000

def z898 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x5fc0ee007ff00f0d 0xf5fc0ee007ff00f0

def z899 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x0fb000007ffe7000 0x50fb000007ffe700

def z900 : W := mkw 0x5200fffe4c921fef 0x85200fffe4c921fe 0x9000fffe00000ff4 0x09000fffe00000ff

def z901 : W := mkw 0x4b40fb82eed01f5e 0x44b40fb82eed01f5 0xdfcfff8ffff00fff 0xfdfcfff8ffff00ff

def z902 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xf1bcde76478ffccf 0xff1bcde76478ffcc

def z903 : W := mkw 0x30015292f7fffddc 0xc30015292f7fffdd 0x600000007ffffff8 0x1600000007ffffff

def z904 : W := mkw 0x24bf0000336de000 0x024bf0000336de00 0x6e3f00007ffff00a 0xf6e3f00007ffff00

def z905 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff20087ffff33b 0xf6fff20087ffff33

def z906 : W := mkw 0x4b40fbd86ed20faf 0x04b40fbd86ed20fa 0x5fc0fff07ff00f0d 0xf5fc0fff07ff00f0

def z907 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x1fc0ce007ff00001 0x51fc0ce007ff0000

def z908 : W := mkw 0xcb40fbc96ed00f0e 0x0cb40fbc96ed00f0 0x5fc0ff89fff00f0d 0xf5fc0ff89fff00f0

def z909 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0ce007ff00f09 0xf5fc0ce007ff00f0

def z910 : W := mkw 0x4b40fb906ed20faf 0x04b40fb906ed20fa 0x5fc0ff807ff00ffd 0xf5fc0ff807ff00ff

def z911 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x31b4de76478e700b 0x731b4de76478e700

def z912 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91c7dff780000005 0x091c7dff78000000

def z913 : W := mkw 0x5200fb924c921fce 0x85200fb924c921fc 0x1000ff8000000fc4 0x01000ff8000000fc

def z914 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x5fc0ff807ff0000d 0xf5fc0ff807ff0000

def z915 : W := mkw 0x40015292fefbbfff 0x440015292fefbbff 0x600000007ffffff8 0x1600000007ffffff

def z916 : W := mkw 0x8ffead6d08000200 0x08ffead6d0800020 0xdfffffffb8000307 0xedfffffffb800030

def z917 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b0de76478e7ccc 0x5b1b0de76478e7cc

def z918 : W := mkw 0x8ffead6d08000221 0x08ffead6d0800022 0x9fffffff80000337 0xe9fffffff8000033

def z919 : W := mkw 0x0094042401044000 0x0009404240104400 0x31b4ce70478e700b 0x731b4ce70478e700

def z920 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91ffffff80000007 0xe91ffffff8000000

def z921 : W := mkw 0xa9d71da7a774f550 0x4a9d71da7a774f55 0x11c71f8787f07001 0x011c71f8787f0700

def z922 : W := mkw 0x04bd0000112de000 0x004bd0000112de00 0x6fff00007ffff00b 0xf6fff00007ffff00

def z923 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9fbfffff80000006 0x49fbfffff8000000

def z924 : W := mkw 0x4b40fb82eed01f5e 0x44b40fb82eed01f5 0xffc4ff8ffff07fff 0xfffc4ff8ffff07ff

def z925 : W := mkw 0x4b40fb826ed01f4e 0x04b40fb826ed01f4 0xdfc0ff867ff00fcd 0xfdfc0ff867ff00fc

def z926 : W := mkw 0x2dfe0000334d4000 0x02dfe0000334d400 0x6ff400007ffe700b 0xf6ff400007ffe700

def z927 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff20087ffff00f 0xfefff20087ffff00

def z928 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xdfc0ff8ffff00f0d 0xfdfc0ff8ffff00f0

def z929 : W := mkw 0x4b40fb82eed01f5e 0x44b40fb82eed01f5 0x5fc0ff807ff00ffd 0xf5fc0ff807ff00ff

def z930 : W := mkw 0x8ffead6d22400000 0x08ffead6d2240000 0xdfffffffb8700007 0xedfffffffb870000

def z931 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6e7f00007ffff00a 0x96e7f00007ffff00

def z932 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee3cf07e780f8fff 0xfee3cf07e780f8ff

def z933 : W := mkw 0x8ffead6d10090000 0x08ffead6d1009000 0xfffffffff80f8fff 0xffffffffff80f8ff

def z934 : W := mkw 0x29410000336de000 0x029410000336de00 0x6f8000007ffff008 0x56f8000007ffff00

def z935 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe04f318f8071fff6 0x8e04f318f8071fff

def z936 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff2189fffff00b 0xf6fff2189fffff00

def z937 : W := mkw 0x8ffead6d10090000 0x08ffead6d1009000 0xbfffffff800f8007 0xebfffffff800f800

def z938 : W := mkw 0xaffead6d32490000 0x0affead6d3249000 0x9fffffffb8000007 0xe9fffffffb800000

def z939 : W := mkw 0xaffead6d334d4000 0x0affead6d334d400 0xdffffffffffe000f 0xfdffffffffffe000

def z940 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1bfde7fc78e7ccf 0x7b1bfde7fc78e7cc

def z941 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xf1ffffffc78fffff 0xff1ffffffc78ffff

def z942 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xffcfff8ffff18fff 0xfffcfff8ffff18ff

def z943 : W := mkw 0x4b40fb906ed20f8e 0x04b40fb906ed20f8 0x7fc0ff807ffe0fcd 0xf7fc0ff807ffe0fc

def z944 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fbf00007ffff00a 0x56fbf00007ffff00

def z945 : W := mkw 0x4b40fb006ec00e0e 0x04b40fb006ec00e0 0x5fc0de007ff00c0d 0xf5fc0de007ff00c0

def z946 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xae38e078780f8ff6 0x5ae38e078780f8ff

def z947 : W := mkw 0x109456b645965dcc 0x8109456b645965dc 0xf1fcfffe47ffffff 0xff1fcfffe47fffff

def z948 : W := mkw 0xa4bf046d112de000 0x0a4bf046d112de00 0x203f0070000ff002 0x0203f0070000ff00

def z949 : W := mkw 0x000110828430b550 0x4000110828430b55 0x604f318f8471fff9 0x8604f318f8471fff

def z950 : W := mkw 0x8ffead6d110d4000 0x08ffead6d110d400 0xffffffffff8ff00f 0xfffffffffff8ff00

def z951 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x5f80ce007ff00008 0x55f80ce007ff0000

def z952 : W := mkw 0x10944636418658cc 0x810944636418658c 0xb1b4de76438e70c7 0x7b1b4de76438e70c

def z953 : W := mkw 0xa4bf0425112de000 0x0a4bf0425112de00 0x203f0007800ff002 0x0203f0007800ff00

def z954 : W := mkw 0x8ffead6d22400000 0x08ffead6d2240000 0x9ffffffffb800007 0xf9ffffffffb80000

def z955 : W := mkw 0x49400b0022c00006 0x049400b0022c0000 0x5fc00e007ff00009 0xf5fc00e007ff0000

def z956 : W := mkw 0x8dfe0d6d00000000 0x08dfe0d6d0000000 0x91ffdfff80000007 0x691ffdfff8000000

def z957 : W := mkw 0x04284010580b0aa9 0x004284010580b0aa 0xee38c070780f8ffe 0xfee38c070780f8ff

def z958 : W := mkw 0x2dff0424336de000 0x02dff0424336de00 0x7fffce707ffff00b 0xf7fffce707ffff00

def z959 : W := mkw 0x8296ad6d00000000 0x08296ad6d0000000 0x9007ffff80000004 0x09007ffff8000000

def z960 : W := mkw 0x4b40eb806ad00b0e 0x04b40eb806ad00b0 0x5fc0ef807bf00f0c 0xf5fc0ef807bf00f0

def z961 : W := mkw 0x8bd6ad6d00000000 0x08bd6ad6d0000000 0x11c7dff780000001 0x011c7dff78000000

def z962 : W := mkw 0x8dfe0d2500000000 0x08dfe0d250000000 0x9fffdff780000007 0xe9fffdff78000000

def z963 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1ffde76478e7ccf 0xfb1ffde76478e7cc

def z964 : W := mkw 0xaf6ba9493a69a221 0x0af6ba9493a69a22 0x4e4b2189b8718330 0x84e4b2189b871833

def z965 : W := mkw 0x0628e258588b0aad 0x00628e258588b0aa 0xffb8ee787b8f8ffe 0xfffb8ee787b8f8ff

def z966 : W := mkw 0x2d690000336de000 0x02d690000336de00 0x6ff800007ffff00b 0xf6ff800007ffff00

def z967 : W := mkw 0x0940090022400000 0x0094009002240000 0x5fc01f807ff00009 0xf5fc01f807ff0000

def z968 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x7fc0ff807ff18ffd 0xf7fc0ff807ff18ff

def z969 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0x6e30e070780f8ffc 0xf6e30e070780f8ff

def z970 : W := mkw 0x109446344186488c 0x8109446344186488 0x31b0ce70478e7008 0x531b0ce70478e700

def z971 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee38c078780f8ffa 0x5ee38c078780f8ff

def z972 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x7fc8ff807ff18f0f 0xf7fc8ff807ff18f0

def z973 : W := mkw 0x0628a04810090000 0x00628a0481009000 0xee38e078780f8ffe 0xfee38e078780f8ff

def z974 : W := mkw 0xaf6ba9493269a000 0x0af6ba9493269a00 0x4e4b000038718000 0x84e4b00003871800

def z975 : W := mkw 0x4b40fb926ed21fce 0x04b40fb926ed21fc 0xfff4fff67ffe7fcf 0xffff4fff67ffe7fc

def z976 : W := mkw 0x29d70000336de000 0x029d70000336de00 0x6fc700007ffff009 0xf6fc700007ffff00

def z977 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xbfffffff80000ccf 0xebfffffff80000cc

def z978 : W := mkw 0x1094563445864c8c 0x81094563445864c8 0x31b4de70478e7c0f 0x731b4de70478e7c0

def z979 : W := mkw 0x0940420062c0080c 0x00940420062c0080 0x5fc0ce007ff00009 0xf5fc0ce007ff0000

def z980 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xffffffff8001800f 0xeffffffff8001800

def z981 : W := mkw 0x109456b6c5965ddc 0xc109456b6c5965dd 0xf1bcffffc78fffff 0xff1bcffffc78ffff

def z982 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4fe7e478e7fff 0x7b1b4fe7e478e7ff

def z983 : W := mkw 0x8200ad6d00000000 0x08200ad6d0000000 0x9047ffff80000005 0x09047ffff8000000

def z984 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee78e0787c7f8fff 0xfee78e0787c7f8ff

def z985 : W := mkw 0x4b40fbd86ed20faf 0x04b40fbd86ed20fa 0xffc8fff87ff18fff 0xfffc8fff87ff18ff

def z986 : W := mkw 0x109456b645965dcc 0x8109456b645965dc 0xf1b4de7647fe7fcf 0x7f1b4de7647fe7fc

def z987 : W := mkw 0x2dff0900336de000 0x02dff0900336de00 0x7fff1f807ffff00b 0xf7fff1f807ffff00

def z988 : W := mkw 0x8ffead6d01044000 0x08ffead6d0104400 0xbfffffff800e7007 0xebfffffff800e700

def z989 : W := mkw 0x862ae059580b0aa9 0x0862ae059580b0aa 0xee3be079f80f8ffe 0xfee3be079f80f8ff

def z990 : W := mkw 0x10944636418658cc 0x810944636418658c 0xb1b4ce76438e7cce 0x7b1b4ce76438e7cc

def z991 : W := mkw 0x10941636058654c4 0x810941636058654c 0xb1b4de76078e70c7 0x6b1b4de76078e70c

def z992 : W := mkw 0x0200e010580b0aa9 0x00200e010580b0aa 0xee30e070780f8ffe 0xfee30e070780f8ff

def z993 : W := mkw 0x4200f2806ed00f0e 0x04200f2806ed00f0 0x5f80fe007ff00f0d 0xf5f80fe007ff00f0

def z994 : W := mkw 0x2dff0048336de021 0x02dff0048336de02 0x6fff00087ffff03b 0xf6fff00087ffff03

def z995 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fcfff807ff00f0f 0xf5fcfff807ff00f0

def z996 : W := mkw 0x86bead6d00000000 0x086bead6d0000000 0x907fffff80000007 0xa907fffff8000000

def z997 : W := mkw 0x4b40fbd86ed20faf 0x04b40fbd86ed20fa 0xfff0fff87ffe0fff 0xffff0fff87ffe0ff

def z998 : W := mkw 0xadff0d25336de000 0x0adff0d25336de00 0xffff3f8ffffff00f 0xfffff3f8ffffff00

def z999 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6ffb00007ffff008 0xd6ffb00007ffff00

def z1000 : W := mkw 0x2d6b0000336de000 0x02d6b0000336de00 0x6e7b00007ffff00a 0xf6e7b00007ffff00

def z1001 : W := mkw 0x59d51fa6a7f4f556 0xc59d51fa6a7f4f55 0x11c71f8787f07001 0x011c71f8787f0700

def z1002 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xf1f4de7647fe7ccf 0xff1f4de7647fe7cc

def z1003 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xbfffffff800180f7 0xebfffffff800180f

def z1004 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6ff700007ffff009 0x56ff700007ffff00

def z1005 : W := mkw 0xef6ba9c93a79a302 0x0ef6ba9c93a79a30 0x4e4b2189b8718300 0x84e4b2189b871830

def z1006 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x31b4de76478e7cc9 0x531b4de76478e7cc

def z1007 : W := mkw 0xaffead6d110d4000 0x0affead6d110d400 0x9fffffff800e0007 0xe9fffffff800e000

def z1008 : W := mkw 0x000100828030b150 0x4000100828030b15 0xe04f218f8071fffe 0xae04f218f8071fff

def z1009 : W := mkw 0x50015292eff6ffde 0xc50015292eff6ffd 0x600000007ffffff8 0x1600000007ffffff

def z1010 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0ff803ff00f05 0x85fc0ff803ff00f0

def z1011 : W := mkw 0x6f6ba9c83a79a323 0x06f6ba9c83a79a32 0x4e4b218838718330 0x84e4b21883871833

def z1012 : W := mkw 0x86bead6d00000000 0x086bead6d0000000 0x9e3fffff80000006 0xe9e3fffff8000000

def z1013 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1fffdff780000003 0xe1fffdff78000000

def z1014 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x7fc4ff807ff07f0f 0xf7fc4ff807ff07f0

def z1015 : W := mkw 0x8b42ad6d00000000 0x08b42ad6d0000000 0x9043ffff80000004 0x09043ffff8000000

def z1016 : W := mkw 0x8ffead6d23444000 0x08ffead6d2344400 0xfffffffffffe700f 0xffffffffffffe700

def z1017 : W := mkw 0xa4bf047d112fe0a1 0x0a4bf047d112fe0a 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z1018 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x1fffffff80000001 0xc1fffffff8000000

def z1019 : W := mkw 0x04280058100b00a1 0x004280058100b00a 0xee382078780f8ffe 0xfee382078780f8ff

def z1020 : W := mkw 0x0dfc0000334d4000 0x00dfc0000334d400 0x6ffc00007ffff00b 0xf6ffc00007ffff00

def z1021 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xdff0fff07ff00f0f 0xfdff0fff07ff00f0

def z1022 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0df807ff00009 0xf5fc0df807ff0000

def z1023 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xdfffffff8470000f 0xedfffffff8470000

def z1024 : W := mkw 0x10944636418658cc 0x810944636418658c 0xb1b4ce76478e70cb 0x7b1b4ce76478e70c

def z1025 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4de76438e7cc6 0x5b1b4de76438e7cc

def z1026 : W := mkw 0x4200fbdacc921fff 0x44200fbdacc921ff 0x9000ffff80000ff4 0x09000ffff80000ff

def z1027 : W := mkw 0x39d716a6a7f4f554 0xc39d716a6a7f4f55 0x11c71f8787f07001 0x011c71f8787f0700

def z1028 : W := mkw 0x8ffead6d01044000 0x08ffead6d0104400 0x9fffffffc38e0007 0xf9fffffffc38e000

def z1029 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff000ffffff00b 0xfefff000ffffff00

def z1030 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xf1b4fe76478e7fcf 0xff1b4fe76478e7fc

def z1031 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x31b0de70478e7ccd 0x731b0de70478e7cc

def z1032 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x11b4de76478e7c0d 0x711b4de76478e7c0

def z1033 : W := mkw 0x8628ad6d00000000 0x08628ad6d0000000 0x9e7fffff80000007 0xe9e7fffff8000000

def z1034 : W := mkw 0xadff0901336de000 0x0adff0901336de00 0x6fff0181fffff00b 0xf6fff0181fffff00

def z1035 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0ef807ff00f08 0xd5fc0ef807ff00f0

def z1036 : W := mkw 0x4b40eb806ad00b0e 0x04b40eb806ad00b0 0x5fc0ff807bf00305 0xf5fc0ff807bf0030

def z1037 : W := mkw 0x4b40fb80eed00f1e 0x44b40fb80eed00f1 0x5fc0ff89fff00f3d 0xf5fc0ff89fff00f3

def z1038 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x11f7dff780000001 0x411f7dff78000000

def z1039 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee3ce0787c0fffff 0xfee3ce0787c0ffff

def z1040 : W := mkw 0x0094562445844c0c 0x00094562445844c0 0xb1b4de76478e7c0f 0x7b1b4de76478e7c0

def z1041 : W := mkw 0x109456b6c5965ddc 0xc109456b6c5965dd 0xb1ffffffc78e7fff 0xfb1ffffffc78e7ff

def z1042 : W := mkw 0x8ffead6d18090221 0x08ffead6d1809022 0x9fffffffb8000007 0xe9fffffffb800000

def z1043 : W := mkw 0x109456b6c5965ddc 0xc109456b6c5965dd 0xb1b4dff7c78e7ccf 0x7b1b4dff7c78e7cc

def z1044 : W := mkw 0x0dfe000023444000 0x00dfe00002344400 0x6fff00007ffe700b 0xf6fff00007ffe700

def z1045 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fb800007ffff00a 0xf6fb800007ffff00

def z1046 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x2fff00007ffff003 0x52fff00007ffff00

def z1047 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9ff7ffff80000005 0x49ff7ffff8000000

def z1048 : W := mkw 0x4b40fbc86ed00f0e 0x04b40fbc86ed00f0 0xdfc0fff87ff00f0d 0xfdfc0fff87ff00f0

def z1049 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x1fc0df807ff00c0d 0x71fc0df807ff00c0

def z1050 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0xdfc0ff887ff00ffd 0xfdfc0ff887ff00ff

def z1051 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fb400007ffff00b 0x76fb400007ffff00

def z1052 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee38f1fff80f8ffe 0xfee38f1fff80f8ff

def z1053 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff318fffffffff 0xfefff318ffffffff

def z1054 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5f80de007ff00f0d 0x75f80de007ff00f0

def z1055 : W := mkw 0x000100000020a000 0x0000100000020a00 0xe04f318f8471ffff 0xae04f318f8471fff

def z1056 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee38e078380f8ff6 0x8ee38e078380f8ff

def z1057 : W := mkw 0xd200ffff4c921fce 0x8d200ffff4c921fc 0x9000ffff80000fc4 0x09000ffff80000fc

def z1058 : W := mkw 0x0940000023444000 0x0094000002344400 0x6fc000007ffe7009 0xf6fc000007ffe700

def z1059 : W := mkw 0x2d6b0000336de000 0x02d6b0000336de00 0x6e4f00007ffff00b 0xb6e4f00007ffff00

def z1060 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefffc0707ffff00f 0xfefffc0707ffff00

def z1061 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fcf00007ffff009 0x96fcf00007ffff00

def z1062 : W := mkw 0x8f6aad6d00000000 0x08f6aad6d0000000 0x9e4fffff80000007 0xa9e4fffff8000000

def z1063 : W := mkw 0x4b40fb826ed01f4e 0x04b40fb826ed01f4 0x5fc4ff867ff07f0d 0xf5fc4ff867ff07f0

def z1064 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xffb8fe78780f8fff 0xfffb8fe78780f8ff

def z1065 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4de76478e70c3 0x5b1b4de76478e70c

def z1066 : W := mkw 0xadff0d25336de000 0x0adff0d25336de00 0x7fff0e007ffff00b 0xf7fff0e007ffff00

def z1067 : W := mkw 0x8f6aad6d00000000 0x08f6aad6d0000000 0x9e7bffff80000006 0xe9e7bffff8000000

def z1068 : W := mkw 0x000110828430b550 0x4000110828430b55 0xa04f318f8471fff7 0x0a04f318f8471fff

def z1069 : W := mkw 0x4b40eb006ac00a0e 0x04b40eb006ac00a0 0x5fc0ce007bf00000 0xd5fc0ce007bf0000

def z1070 : W := mkw 0xb4bf047f112ff0c0 0x8b4bf047f112ff0c 0xa03f007f800ff0c2 0x0a03f007f800ff0c

def z1071 : W := mkw 0x4b40eb806ad00b0e 0x04b40eb806ad00b0 0x1fc0cf807bf00000 0x51fc0cf807bf0000

def z1072 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee30e078780f8ffc 0x5ee30e078780f8ff

def z1073 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee30c070780f8ffe 0x7ee30c070780f8ff

def z1074 : W := mkw 0x000110828430b550 0x4000110828430b55 0xe1cf318fc7f1ffff 0xfe1cf318fc7f1fff

def z1075 : W := mkw 0x4b40eb806ad00b0e 0x04b40eb806ad00b0 0x5f80ce007bf00300 0x55f80ce007bf0030

def z1076 : W := mkw 0x109446344186488c 0x8109446344186488 0x31b4ce70438e7002 0x531b4ce70438e700

def z1077 : W := mkw 0x4b40fb826ed01f4e 0x04b40fb826ed01f4 0x7fc0ff807ff07fcd 0xf7fc0ff807ff07fc

def z1078 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x7fffde007ffff00f 0xf7fffde007ffff00

def z1079 : W := mkw 0x109456b6c5965ddc 0xc109456b6c5965dd 0xf1f4ffffc7fe7fff 0xff1f4ffffc7fe7ff

def z1080 : W := mkw 0xa4bf046f912df050 0x4a4bf046f912df05 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z1081 : W := mkw 0x0000042400000000 0x0000004240000000 0x904fffff80000007 0xa904fffff8000000

def z1082 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0x9e7fffff80000006 0x89e7fffff8000000

def z1083 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0x6fff20007fffff0f 0xf6fff20007fffff0

def z1084 : W := mkw 0x4b40fb906ed20f8e 0x04b40fb906ed20f8 0x5ff0fff07ffe0f0d 0xf5ff0fff07ffe0f0

def z1085 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5f80ff807ff00f0c 0x55f80ff807ff00f0

def z1086 : W := mkw 0x2dff0000336de000 0x02dff0000336de00 0xefff00087ffff0fb 0xfefff00087ffff0f

def z1087 : W := mkw 0x4b40fbc86ed00f2f 0x04b40fbc86ed00f2 0x5fc0ff887ff00f3d 0xf5fc0ff887ff00f3

def z1088 : W := mkw 0x000110828430b550 0x4000110828430b55 0xee4f318ffc71ffff 0xfee4f318ffc71fff

def z1089 : W := mkw 0x0d6900003269a000 0x00d6900003269a00 0x6fff00007ffff00b 0xf6fff00007ffff00

def z1090 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x7ff0ff807ffe0f0f 0xf7ff0ff807ffe0f0

def z1091 : W := mkw 0x49401b8026d00506 0x049401b8026d0050 0x5fc03f807ff00f0d 0xf5fc03f807ff00f0

def z1092 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc03f807ff00f09 0x95fc03f807ff00f0

def z1093 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0x91b4de76478e7007 0x791b4de76478e700

def z1094 : W := mkw 0x0200e01048020a88 0x00200e01048020a8 0xee38e078780f8ffe 0xfee38e078780f8ff

def z1095 : W := mkw 0x0940528066d00d0c 0x00940528066d00d0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z1096 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1b4ce76478e7cca 0x5b1b4ce76478e7cc

def z1097 : W := mkw 0x0628e058580b0aa9 0x00628e058580b0aa 0xee7fe078780f8fff 0xfee7fe078780f8ff

def z1098 : W := mkw 0x29d700002364e000 0x029d700002364e00 0x6ff700007ffe700b 0xf6ff700007ffe700

def z1099 : W := mkw 0x8bd6ad6d00000000 0x08bd6ad6d0000000 0x9fc7ffff80000005 0xe9fc7ffff8000000

def z1100 : W := mkw 0x1094563645865ccc 0x81094563645865cc 0xb1bcfe7e478e7ccf 0xfb1bcfe7e478e7cc

def z1101 : W := mkw 0x0000521244821ccc 0x00000521244821cc 0xb1b4de76478e7ccf 0x7b1b4de76478e7cc

def z1102 : W := mkw 0x2dff0424336de000 0x02dff0424336de00 0xefff00767ffff00b 0xfefff00767ffff00

def z1103 : W := mkw 0x1094162605845444 0x8109416260584544 0xb1b4de76478e700f 0x7b1b4de76478e700

def z1104 : W := mkw 0x4b40fb806ed00f0e 0x04b40fb806ed00f0 0x5fc0ff807ff00301 0xd5fc0ff807ff0030

def z1105 : W := mkw 0x0094042400000000 0x0009404240000000 0x91f7dff780000007 0x691f7dff78000000

def z1106 : W := mkw 0x8ffead6d00000000 0x08ffead6d0000000 0xbfffffff8400700f 0xebfffffff8400700

def z1107 : W := mkw 0x8bd6ad6d00000000 0x08bd6ad6d0000000 0x91f7ffff80000007 0x691f7ffff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z9]),(0,[z0,z1,z2,z3,z10,z4,z11])],[(0,[z0,z12,z1,z2,z13,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z14])],[(0,[z15,z0,z1,z2,z3,z4,z8]),(0,[z0,z16,z1,z2,z3,z4,z8]),(0,[z0,z17,z1,z2,z3,z4,z8]),(0,[z0,z18,z19,z2,z3,z4,z8]),(0,[z20,z0,z1,z2,z3,z4,z8]),(0,[z0,z21,z2,z3,z22,z4,z8]),(0,[z0,z1,z23,z2,z3,z11,z8])],[(0,[z0,z1,z2,z3,z4,z8,z24])],[(0,[z25,z0,z1,z2,z3,z26,z8]),(0,[z0,z1,z2,z27,z3,z4,z8]),(0,[z28,z0,z1,z29,z3,z4,z8])],[(0,[z30,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z31,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z32,z5]),(0,[z0,z1,z3,z33,z4,z34,z8]),(0,[z0,z1,z35,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z10,z4,z36])],[(1,[z0,z1,z37,z3,z4,z8]),(0,[z0,z1,z2,z3,z38,z4,z8]),(0,[z0,z1,z39,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z40,z4,z8]),(0,[z0,z1,z41,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z42,z36])],[(0,[z0,z1,z3,z4,z43,z8,z44]),(0,[z0,z45,z1,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z46,z47,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z48,z8]),(0,[z49,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z8,z50]),(0,[z25,z0,z1,z2,z3,z4,z51]),(0,[z0,z1,z2,z52,z3,z4,z8]),(0,[z0,z1,z2,z3,z53,z4,z8]),(0,[z0,z1,z2,z3,z4,z54,z8])],[(0,[z0,z1,z2,z3,z4,z8,z55])],[(0,[z0,z1,z2,z3,z4,z8,z56]),(0,[z0,z1,z23,z2,z3,z57,z8]),(0,[z0,z1,z2,z3,z4,z8,z58]),(0,[z0,z59,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z60,z8]),(0,[z61,z0,z1,z2,z62,z4,z8]),(0,[z0,z1,z2,z63,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z64]),(0,[z0,z1,z2,z3,z4,z65,z8]),(0,[z0,z1,z23,z2,z66,z4,z8])],[(0,[z0,z1,z2,z3,z4,z67,z8]),(0,[z68,z0,z1,z2,z3,z4,z8]),(0,[z0,z69,z1,z2,z3,z4,z8]),(0,[z0,z70,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z71,z8]),(0,[z0,z2,z3,z22,z4,z72,z8]),(0,[z0,z1,z2,z3,z73,z4,z8]),(0,[z0,z1,z2,z3,z74,z4,z8])],[(1,[z0,z1,z2,z3,z4,z50]),(0,[z0,z75,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z76,z8]),(0,[z0,z1,z2,z3,z4,z8,z77]),(0,[z78,z1,z2,z3,z79,z4,z8]),(0,[z0,z1,z2,z3,z4,z80,z8]),(0,[z81,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z82])],[(0,[z0,z83,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z84,z8]),(0,[z0,z1,z2,z3,z4,z85,z55]),(0,[z0,z1,z2,z3,z4,z8,z86]),(0,[z0,z1,z2,z3,z4,z8,z85]),(0,[z0,z87,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z11,z8,z36]),(0,[z0,z1,z88,z2,z3,z4,z8])]],
   [[(0,[z89,z0,z1,z2,z3,z4,z8]),(0,[z0,z90,z1,z2,z3,z4,z8]),(0,[z0,z1,z91,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z8,z92]),(0,[z0,z1,z2,z3,z8,z93,z42])],[(0,[z94,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z95,z8]),(0,[z0,z1,z2,z3,z4,z44,z42])],[(0,[z0,z1,z2,z3,z4,z5,z55]),(0,[z0,z96,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z71,z4,z8]),(0,[z0,z97,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z98,z8]),(0,[z0,z1,z99,z2,z3,z4,z8])],[(0,[z100,z0,z1,z2,z3,z4,z8]),(0,[z0,z12,z1,z47,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z36])],[(1,[z0,z1,z101,z3,z4,z8]),(0,[z0,z1,z101,z2,z3,z4,z8]),(1,[z0,z1,z2,z4,z8,z102])],[(0,[z103,z1,z2,z62,z3,z4,z8]),(0,[z0,z104,z12,z1,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z105,z8]),(0,[z0,z1,z2,z3,z4,z8,z42])]],
   [[(0,[z0,z1,z106,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z107])],[(0,[z108,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z109,z3,z4,z8]),(0,[z68,z0,z1,z2,z3,z110,z8]),(0,[z111,z0,z1,z2,z3,z4,z5]),(0,[z0,z104,z1,z2,z3,z4,z8]),(0,[z0,z1,z112,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z32,z8,z42]),(0,[z0,z1,z2,z3,z113,z4,z8])],[(0,[z114,z1,z46,z2,z3,z4,z8]),(0,[z0,z1,z115,z2,z3,z4,z8]),(0,[z0,z1,z2,z116,z3,z4,z8]),(0,[z0,z1,z117,z2,z3,z4,z8])],[(0,[z118,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z119,z4,z8]),(0,[z0,z1,z120,z2,z3,z4,z8]),(0,[z0,z1,z2,z47,z4,z8,z42]),(0,[z0,z1,z2,z3,z4,z121,z8]),(0,[z0,z1,z2,z122,z3,z4,z8])],[(0,[z123,z0,z1,z2,z3,z4,z8]),(0,[z124,z0,z1,z2,z3,z4,z8])],[(0,[z0,z125,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z126]),(0,[z0,z1,z2,z3,z4,z127,z8]),(0,[z0,z104,z1,z128,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z107]),(0,[z0,z129,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z130,z3,z4,z8]),(0,[z0,z1,z2,z3,z57,z72,z8]),(0,[z0,z1,z2,z3,z131,z4,z8])],[(0,[z0,z19,z1,z2,z3,z4,z8]),(0,[z0,z1,z132,z2,z133,z3,z8])]],
   [[(0,[z134,z0,z1,z2,z3,z4,z8]),(0,[z135,z0,z1,z23,z2,z3,z8])],[(0,[z25,z0,z1,z37,z3,z4,z8]),(0,[z78,z0,z1,z2,z3,z4,z8]),(0,[z0,z104,z1,z2,z47,z4,z8])],[(0,[z103,z0,z1,z2,z3,z136,z8]),(0,[z0,z1,z137,z2,z3,z4,z8]),(0,[z138,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z139])],[(0,[z0,z1,z140,z2,z3,z4,z8]),(1,[z0,z1,z27,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z141,z8]),(0,[z0,z1,z142,z2,z3,z4,z8])],[(0,[z143,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z79,z72,z8])],[(0,[z0,z144,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z11,z8,z102])],[(0,[z25,z0,z145,z2,z3,z4,z8]),(0,[z0,z1,z2,z146,z4,z8,z42]),(0,[z147,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z148,z4,z8]),(0,[z0,z18,z1,z2,z149,z4,z8]),(0,[z0,z1,z2,z133,z150,z4,z8]),(0,[z151,z0,z1,z2,z3,z4,z8])]],
   [[(0,[z152,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z153,z8]),(0,[z154,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z155,z8]),(0,[z0,z1,z2,z3,z22,z33,z8]),(0,[z156,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z33,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z157])],[(0,[z0,z1,z2,z158,z3,z4,z8]),(0,[z25,z0,z1,z2,z3,z4,z50]),(0,[z159,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z160,z4,z8]),(0,[z135,z0,z1,z2,z3,z33,z8]),(0,[z0,z1,z161,z2,z3,z4,z8]),(0,[z0,z1,z112,z3,z4,z43,z8]),(0,[z0,z1,z2,z3,z4,z162,z8])],[(0,[z163,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z164,z2,z3,z4,z8]),(1,[z0,z1,z2,z165,z4,z8]),(0,[z166,z0,z1,z2,z3,z4,z8]),(0,[z111,z0,z1,z2,z3,z4,z85])],[(0,[z0,z1,z2,z3,z3,z4,z8]),(0,[z167,z0,z1,z2,z3,z4,z8]),(0,[z0,z168,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z4,z169,z8]),(1,[z0,z1,z112,z3,z4,z43]),(0,[z0,z1,z170,z2,z3,z8,z42]),(0,[z0,z1,z2,z3,z4,z8,z171])],[(0,[z172,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z22,z79,z8]),(0,[z0,z1,z2,z173,z3,z4,z8]),(0,[z174,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z150,z4,z162,z8]),(0,[z0,z1,z2,z3,z4,z8,z175])],[(0,[z176,z1,z2,z3,z4,z6,z8]),(0,[z0,z1,z2,z3,z177,z4,z8]),(0,[z0,z1,z2,z3,z22,z34,z8]),(1,[z0,z1,z2,z178,z4,z8]),(0,[z0,z1,z2,z179,z3,z4,z8]),(0,[z0,z1,z23,z2,z3,z162,z8])],[(0,[z0,z1,z1,z2,z3,z4,z8]),(0,[z180,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z181,z3,z4,z8]),(0,[z135,z0,z1,z2,z3,z34,z8]),(0,[z0,z1,z182,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z183,z8]),(0,[z0,z1,z2,z3,z33,z72,z8]),(0,[z0,z1,z2,z3,z4,z32,z44]),(0,[z0,z1,z23,z184,z2,z3,z8])]],
   [[(0,[z185,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z186,z8]),(0,[z0,z1,z187,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z32,z43])],[(0,[z0,z1,z188,z2,z3,z4,z8]),(0,[z0,z1,z189,z2,z130,z3,z4]),(0,[z0,z1,z2,z3,z190,z4,z8]),(0,[z0,z1,z2,z3,z146,z4,z8]),(0,[z0,z1,z191,z2,z3,z4,z8]),(0,[z192,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z193,z3,z4,z8]),(0,[z111,z0,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z194,z3,z4,z8])],[(1,[z0,z1,z2,z195,z4,z8]),(0,[z0,z1,z2,z3,z196,z4,z8]),(0,[z0,z1,z2,z3,z4,z197,z8]),(0,[z0,z1,z2,z3,z4,z198,z8]),(0,[z0,z1,z2,z3,z199,z4,z8]),(1,[z0,z97,z1,z3,z4,z8])],[(0,[z200,z0,z1,z2,z3,z4,z8]),(1,[z114,z1,z46,z3,z4,z8]),(0,[z201,z78,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z11,z42])],[(0,[z0,z1,z2,z3,z202,z4,z8]),(0,[z0,z1,z2,z203,z3,z4,z8]),(0,[z0,z1,z2,z3,z204,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z205]),(0,[z0,z1,z206,z2,z3,z4,z8]),(0,[z0,z1,z2,z207,z3,z4,z8])],[(0,[z0,z1,z130,z3,z4,z34,z8]),(0,[z0,z1,z2,z208,z3,z4,z8]),(0,[z209,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z210,z3,z4,z8]),(1,[z0,z211,z2,z3,z72,z8]),(0,[z0,z1,z112,z2,z3,z4,z5])],[(0,[z0,z1,z2,z146,z148,z4,z8]),(0,[z0,z1,z2,z62,z4,z8,z42]),(0,[z0,z1,z212,z2,z3,z4,z8]),(0,[z213,z0,z1,z2,z3,z4,z8])]],
   [[(0,[z214,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z132,z130,z3,z4,z8]),(0,[z0,z1,z215,z2,z3,z4,z8]),(0,[z0,z104,z1,z3,z216,z4,z8])],[(0,[z0,z1,z2,z3,z4,z8,z217]),(0,[z0,z1,z2,z218,z3,z4,z8])],[(0,[z0,z219,z1,z220,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z205]),(0,[z0,z1,z2,z3,z221,z4,z8]),(0,[z0,z1,z2,z3,z4,z34,z8]),(1,[z0,z1,z2,z13,z4,z8]),(0,[z0,z1,z2,z222,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z8,z223]),(0,[z0,z1,z2,z3,z4,z8,z224]),(0,[z0,z1,z2,z225,z3,z4,z8]),(0,[z0,z1,z132,z2,z3,z33,z8]),(0,[z0,z1,z2,z3,z226,z4,z8]),(1,[z0,z1,z2,z3,z8,z93])],[(0,[z103,z0,z1,z2,z3,z227,z8]),(0,[z0,z18,z2,z149,z3,z4,z8]),(0,[z0,z1,z2,z66,z3,z4,z8])],[(0,[z68,z1,z2,z130,z3,z4,z8]),(0,[z0,z1,z23,z2,z3,z79,z8]),(0,[z0,z1,z2,z3,z4,z228,z8]),(0,[z0,z1,z2,z3,z4,z8,z229]),(0,[z230,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z66,z3,z4,z32])],[(0,[z0,z1,z231,z2,z3,z4,z8]),(0,[z0,z1,z2,z232,z3,z4,z8]),(0,[z233,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z234])],[(1,[z68,z1,z130,z3,z4,z8]),(0,[z0,z235,z1,z2,z3,z4,z8]),(0,[z0,z236,z1,z2,z3,z4,z8]),(0,[z0,z1,z237,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z238,z2,z3,z4,z8]),(0,[z0,z1,z2,z239,z3,z4,z8]),(0,[z0,z1,z2,z240,z3,z4,z8]),(0,[z0,z1,z132,z2,z3,z34,z8])],[(0,[z0,z1,z46,z220,z3,z4,z8]),(0,[z61,z0,z1,z2,z3,z4,z8]),(0,[z0,z241,z1,z2,z3,z4,z8]),(0,[z0,z242,z1,z2,z3,z4,z8])],[(0,[z243,z1,z2,z3,z4,z8,z55]),(0,[z0,z1,z2,z244,z3,z4,z8]),(0,[z135,z0,z1,z3,z4,z34,z8]),(0,[z0,z1,z132,z3,z33,z4,z8])],[(0,[z245,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z66,z146,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z246])],[(0,[z0,z1,z247,z2,z3,z4,z8]),(0,[z0,z1,z2,z66,z47,z4,z8])],[(0,[z0,z248,z1,z2,z3,z4,z8]),(0,[z114,z0,z1,z130,z3,z4,z8]),(0,[z0,z249,z1,z2,z3,z4,z8])],[(0,[z111,z0,z241,z2,z3,z4,z8]),(0,[z0,z250,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z251,z8])],[(0,[z252,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z62,z148,z4,z8]),(0,[z253,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z133,z3,z150,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z8,z254]),(0,[z0,z255,z1,z2,z3,z4,z8]),(0,[z61,z0,z1,z2,z146,z4,z8]),(0,[z0,z1,z256,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z257]),(0,[z0,z258,z1,z2,z3,z4,z8])],[(0,[z176,z0,z12,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z259,z8]),(0,[z0,z1,z2,z3,z260,z4,z8]),(0,[z261,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z262,z2,z4,z8,z42])],[(0,[z25,z263,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z66,z62,z4,z8])],[(1,[z0,z1,z173,z3,z4,z8]),(0,[z0,z1,z264,z2,z3,z4,z8])],[(1,[z243,z1,z2,z3,z4,z55]),(0,[z0,z19,z1,z2,z66,z4,z8])],[(0,[z0,z265,z1,z2,z3,z4,z8]),(0,[z78,z0,z1,z2,z3,z57,z8]),(0,[z28,z0,z1,z2,z3,z266,z8]),(0,[z0,z1,z267,z2,z3,z4,z8])],[(0,[z25,z0,z1,z2,z195,z4,z8]),(0,[z268,z0,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z136,z8]),(0,[z0,z1,z2,z269,z3,z4,z8]),(0,[z0,z1,z270,z2,z3,z4,z8]),(0,[z271,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z272,z8])],[(0,[z176,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z273,z4,z8]),(0,[z0,z1,z2,z3,z274,z4,z8])]],
   [[(0,[z176,z0,z1,z2,z3,z4,z32]),(0,[z0,z18,z1,z2,z3,z71,z8]),(0,[z0,z104,z1,z2,z3,z4,z107])],[(0,[z0,z1,z2,z3,z275,z4,z8]),(0,[z0,z1,z2,z3,z57,z8,z36]),(0,[z0,z1,z2,z178,z4,z5,z8])],[(0,[z0,z1,z2,z3,z4,z276,z8]),(0,[z0,z277,z1,z2,z3,z4,z8])],[(0,[z0,z1,z29,z130,z3,z4,z8]),(0,[z0,z1,z2,z3,z278,z4,z8]),(0,[z0,z1,z2,z3,z279,z4,z8])],[(0,[z0,z280,z1,z2,z3,z4,z8]),(0,[z0,z281,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z33,z57,z8]),(0,[z0,z282,z1,z2,z3,z4,z8])],[(0,[z283,z0,z1,z2,z3,z4,z8]),(0,[z114,z0,z1,z46,z3,z4,z8]),(0,[z0,z29,z2,z220,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z284,z8])],[(0,[z243,z0,z1,z2,z3,z285,z8]),(0,[z0,z219,z1,z2,z3,z4,z8]),(0,[z0,z18,z1,z2,z66,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z286])],[(0,[z0,z1,z2,z62,z3,z4,z287])]],
   [[(0,[z288,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z79,z8,z36]),(0,[z289,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z290,z3,z4,z8]),(0,[z0,z19,z1,z2,z3,z4,z291]),(0,[z0,z1,z2,z3,z292,z4,z8])],[(0,[z0,z1,z2,z293,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z32,z85]),(0,[z0,z1,z2,z3,z4,z8,z294])],[(0,[z295,z0,z1,z2,z3,z4,z8]),(1,[z0,z235,z2,z3,z4,z8]),(0,[z0,z296,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z297,z8]),(0,[z0,z1,z2,z3,z298,z4,z8]),(0,[z0,z1,z2,z3,z4,z32,z11])],[(0,[z0,z1,z2,z3,z4,z299,z8]),(0,[z0,z1,z2,z300,z3,z4,z8])],[(0,[z301,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z302,z8]),(0,[z0,z1,z2,z303,z3,z4,z8]),(0,[z304,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z128,z2,z150,z4,z8]),(1,[z0,z1,z132,z3,z33,z8])],[(0,[z0,z1,z37,z2,z3,z4,z8]),(0,[z0,z1,z46,z2,z3,z4,z8]),(0,[z0,z1,z2,z305,z3,z4,z8])],[(0,[z0,z241,z1,z2,z3,z4,z5]),(0,[z306,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z307,z3,z4,z8])],[(0,[z1,z46,z2,z130,z3,z4,z8]),(0,[z0,z1,z2,z3,z308,z4,z8]),(0,[z0,z1,z309,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z310,z4,z8]),(1,[z0,z219,z29,z3,z4,z8]),(0,[z0,z1,z311,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z312,z4,z8]),(0,[z0,z1,z313,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z32,z36])]],
   [[(0,[z314,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z315]),(0,[z0,z1,z316,z2,z3,z4,z8]),(0,[z0,z1,z2,z317,z3,z4,z8]),(0,[z318,z0,z1,z2,z3,z4,z8]),(0,[z0,z19,z1,z2,z149,z4,z8]),(0,[z0,z211,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z319,z3,z4,z8]),(0,[z0,z320,z1,z2,z3,z4,z8]),(0,[z0,z1,z112,z2,z3,z4,z44]),(0,[z0,z321,z1,z2,z3,z4,z8])],[(0,[z243,z0,z1,z112,z2,z3,z4])],[(0,[z0,z1,z2,z62,z3,z4,z322]),(0,[z0,z219,z1,z2,z3,z4,z323]),(0,[z0,z1,z2,z3,z324,z4,z8]),(0,[z0,z1,z2,z3,z4,z325,z8]),(0,[z0,z1,z112,z2,z3,z4,z43])],[(0,[z263,z0,z145,z2,z3,z4,z8]),(0,[z0,z1,z2,z326,z3,z4,z8]),(0,[z0,z1,z2,z3,z327,z4,z8]),(0,[z243,z0,z12,z1,z2,z3,z4]),(0,[z328,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z329,z8]),(0,[z0,z97,z1,z3,z4,z8,z42])],[(0,[z68,z0,z1,z130,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z330]),(0,[z0,z331,z1,z2,z3,z4,z8])],[(0,[z111,z0,z145,z2,z3,z4,z8]),(0,[z332,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z333,z2,z3,z4,z8]),(0,[z0,z334,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z335,z8])],[(0,[z0,z1,z2,z3,z336,z4,z8]),(0,[z0,z1,z2,z3,z4,z337,z8]),(0,[z0,z1,z2,z3,z4,z338,z8]),(0,[z0,z339,z1,z2,z3,z4,z8]),(0,[z0,z1,z340,z2,z3,z4,z8]),(0,[z0,z1,z341,z2,z3,z4,z8])],[(0,[z103,z61,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z342,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z343]),(0,[z0,z211,z1,z2,z3,z72,z8]),(1,[z0,z1,z2,z3,z4,z344]),(0,[z0,z1,z2,z345,z3,z4,z8])]],
   [[(1,[z0,z1,z2,z3,z227,z8]),(1,[z0,z1,z2,z3,z346,z8]),(0,[z0,z211,z21,z2,z3,z4,z8]),(0,[z0,z347,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z348,z8])],[(0,[z0,z1,z349,z2,z3,z4,z8]),(0,[z243,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z23,z128,z2,z4,z8]),(0,[z0,z1,z350,z2,z3,z4,z8])],[(0,[z243,z0,z1,z2,z63,z4,z8]),(0,[z243,z0,z1,z2,z3,z4,z32]),(1,[z0,z1,z184,z2,z3,z36])],[(0,[z0,z1,z2,z3,z351,z4,z8]),(0,[z0,z211,z1,z2,z3,z22,z8]),(0,[z0,z1,z2,z3,z4,z8,z352]),(0,[z0,z1,z2,z3,z4,z353,z8]),(0,[z0,z1,z2,z354,z3,z4,z8])],[(0,[z0,z355,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z356])],[(0,[z201,z1,z2,z3,z4,z57,z8]),(0,[z0,z1,z2,z3,z357,z4,z8])],[(0,[z0,z1,z130,z47,z3,z4,z8])],[(0,[z358,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z359,z8]),(0,[z0,z360,z1,z2,z3,z4,z8]),(0,[z0,z241,z1,z2,z3,z4,z85]),(0,[z0,z1,z361,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z362,z3,z4,z8]),(0,[z0,z104,z1,z130,z3,z4,z8]),(0,[z0,z1,z2,z363,z3,z4,z8])],[(0,[z0,z1,z364,z2,z3,z4,z8]),(0,[z365,z0,z1,z2,z3,z4,z8]),(0,[z366,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z367,z8])],[(0,[z0,z1,z2,z47,z3,z4,z8]),(0,[z0,z1,z2,z66,z3,z4,z42])],[(1,[z0,z1,z2,z3,z266,z8]),(0,[z368,z0,z1,z2,z3,z4,z8]),(0,[z369,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z93])],[(0,[z0,z1,z370,z2,z3,z4,z8]),(0,[z0,z371,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z372,z8]),(0,[z373,z0,z1,z2,z3,z4,z8])],[(0,[z0,z374,z1,z2,z3,z4,z8]),(0,[z0,z1,z375,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z57,z34,z8])],[(0,[z103,z0,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z322]),(0,[z0,z1,z2,z3,z4,z376,z8]),(0,[z0,z1,z377,z2,z3,z4,z8]),(0,[z378,z0,z1,z2,z3,z4,z8])]],
   [[(1,[z0,z1,z293,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z379]),(1,[z0,z19,z2,z148,z4,z8]),(0,[z0,z1,z350,z2,z4,z34,z8]),(0,[z0,z1,z2,z3,z4,z8,z380]),(0,[z0,z1,z2,z3,z4,z8,z381])],[(0,[z0,z1,z2,z3,z4,z323,z8]),(0,[z0,z1,z2,z382,z3,z4,z8])],[(0,[z383,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z384,z2,z3,z4,z8])],[(0,[z0,z1,z46,z3,z4,z8,z44]),(0,[z0,z1,z2,z3,z4,z385,z8]),(0,[z0,z1,z2,z3,z386,z4,z8])],[(0,[z0,z1,z2,z3,z4,z387,z8])],[(0,[z0,z1,z2,z388,z3,z4,z8]),(0,[z0,z1,z2,z3,z79,z34,z8]),(0,[z28,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z389,z2,z3,z4,z8])],[(0,[z103,z0,z1,z2,z146,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z390])],[(0,[z0,z1,z2,z391,z3,z4,z8]),(0,[z78,z0,z1,z2,z3,z79,z8]),(0,[z0,z1,z2,z3,z4,z392,z8]),(0,[z0,z1,z184,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z393,z8]),(0,[z394,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z128,z47,z3,z4,z8]),(0,[z0,z1,z47,z3,z4,z43,z8]),(0,[z0,z1,z2,z3,z4,z395,z8]),(0,[z0,z1,z2,z3,z396,z4,z8])],[(0,[z0,z255,z1,z2,z130,z3,z4]),(0,[z397,z0,z1,z2,z3,z4,z8]),(0,[z0,z398,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z228]),(0,[z399,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z400,z4,z8])],[(0,[z0,z1,z2,z3,z4,z401,z8]),(0,[z0,z1,z2,z3,z402,z4,z8]),(0,[z0,z1,z2,z3,z403,z4,z8]),(0,[z404,z0,z1,z2,z3,z4,z8])],[(0,[z0,z405,z1,z2,z3,z4,z8])],[(0,[z0,z1,z406,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z136,z4,z8]),(0,[z243,z0,z1,z2,z3,z327,z8]),(0,[z407,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z408,z2,z3,z4,z8]),(0,[z0,z1,z2,z149,z3,z4,z8]),(1,[z0,z1,z409,z2,z3,z8]),(0,[z0,z1,z2,z3,z410,z4,z8])],[(0,[z61,z1,z2,z3,z146,z4,z8]),(0,[z103,z0,z1,z2,z62,z4,z8]),(0,[z28,z0,z1,z2,z3,z346,z8]),(1,[z28,z0,z220,z3,z4,z8])],[(0,[z0,z1,z2,z3,z33,z79,z8]),(0,[z0,z1,z23,z2,z3,z150,z8])],[(1,[z0,z1,z2,z158,z4,z8]),(0,[z0,z411,z1,z2,z3,z4,z8]),(0,[z0,z412,z1,z2,z3,z4,z8]),(0,[z0,z413,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z169,z34,z8]),(0,[z0,z1,z23,z2,z3,z4,z414]),(0,[z0,z1,z2,z3,z4,z415,z8])]],
   [[(0,[z416,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z417,z3,z4,z8]),(0,[z0,z1,z2,z3,z418,z4,z8]),(0,[z0,z1,z23,z2,z4,z8,z42])],[(0,[z0,z1,z2,z3,z4,z419,z8]),(0,[z0,z1,z2,z133,z3,z57,z8]),(0,[z0,z104,z1,z23,z2,z4,z8]),(0,[z0,z1,z2,z3,z4,z420,z8]),(0,[z0,z1,z3,z4,z8,z421,z42])],[(0,[z176,z0,z1,z112,z2,z3,z4]),(0,[z422,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z112,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z4,z423,z8])],[(0,[z0,z1,z132,z46,z3,z4,z8]),(0,[z0,z1,z2,z149,z146,z4,z8]),(0,[z0,z1,z2,z3,z22,z4,z8]),(1,[z0,z1,z2,z4,z8,z286])],[(0,[z0,z1,z2,z424,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z425,z8]),(0,[z426,z0,z1,z2,z3,z4,z8]),(0,[z135,z0,z1,z2,z3,z4,z8])],[(0,[z25,z0,z238,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z427,z4,z8]),(0,[z428,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z62,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z414]),(0,[z0,z1,z2,z3,z4,z429,z8]),(0,[z0,z1,z2,z3,z10,z4,z8])],[(0,[z0,z430,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z79,z4,z57,z8]),(0,[z0,z1,z2,z3,z4,z431,z8])]],
   [[(0,[z432,z0,z1,z2,z3,z4,z8]),(0,[z433,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z434,z8]),(0,[z0,z1,z435,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z285,z8]),(0,[z436,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z128,z2,z216,z4,z8])],[(0,[z1,z2,z3,z4,z6,z8,z55]),(0,[z0,z1,z2,z3,z4,z344,z8])],[(0,[z0,z1,z2,z3,z4,z437,z8]),(0,[z0,z1,z2,z149,z62,z4,z8]),(0,[z0,z1,z438,z2,z3,z4,z8]),(0,[z243,z0,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z439,z3,z4,z8])],[(0,[z25,z0,z1,z293,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z440,z8]),(0,[z0,z1,z2,z3,z4,z8,z441]),(0,[z0,z1,z2,z3,z4,z442,z8]),(0,[z443,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z444,z8])],[(0,[z0,z1,z409,z2,z3,z216,z8]),(0,[z0,z1,z2,z3,z4,z43,z8]),(0,[z0,z1,z2,z3,z4,z8,z445]),(0,[z0,z1,z446,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z447,z8])],[(0,[z0,z1,z2,z448,z3,z4,z8])],[(0,[z449,z0,z1,z2,z3,z4,z8]),(0,[z0,z450,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z451,z4,z8]),(0,[z201,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z452]),(0,[z0,z453,z1,z2,z3,z4,z8])]],
   [[(0,[z103,z0,z1,z454,z3,z4,z8]),(0,[z0,z1,z2,z3,z266,z4,z8]),(0,[z0,z1,z2,z3,z455,z4,z8]),(0,[z0,z1,z2,z3,z4,z456,z8]),(0,[z0,z1,z2,z3,z4,z8,z457]),(0,[z458,z0,z1,z2,z3,z4,z8])],[(0,[z0,z459,z1,z2,z3,z4,z8]),(0,[z243,z0,z1,z101,z3,z4,z8]),(0,[z0,z1,z460,z2,z3,z4,z8]),(0,[z0,z1,z2,z461,z3,z4,z8])],[(1,[z61,z1,z2,z146,z4,z8]),(0,[z0,z219,z1,z29,z3,z4,z8]),(0,[z0,z1,z23,z2,z4,z162,z8])],[(0,[z0,z145,z2,z3,z4,z8,z85]),(0,[z0,z1,z2,z3,z4,z8,z462])],[(0,[z463,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z464,z2,z3,z4,z8]),(0,[z465,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z466,z4,z8]),(0,[z0,z467,z1,z2,z3,z4,z8]),(0,[z0,z1,z184,z2,z3,z10,z8]),(0,[z0,z1,z2,z3,z4,z468,z8])],[(0,[z0,z1,z2,z3,z4,z8,z469]),(0,[z0,z1,z2,z3,z4,z8,z470])],[(0,[z0,z1,z2,z3,z471,z4,z8]),(1,[z0,z1,z2,z3,z440,z8]),(0,[z0,z1,z2,z3,z472,z4,z8]),(0,[z0,z1,z2,z3,z473,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z8]),(0,[z0,z474,z1,z2,z3,z4,z8]),(0,[z475,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z102]),(1,[z0,z1,z2,z207,z4,z8])],[(0,[z0,z1,z2,z3,z4,z8,z476]),(0,[z0,z477,z1,z2,z3,z4,z8]),(0,[z243,z0,z1,z2,z3,z4,z42]),(0,[z478,z0,z1,z2,z3,z4,z8]),(1,[z0,z18,z2,z149,z4,z8]),(0,[z0,z1,z2,z3,z4,z479,z8]),(0,[z0,z1,z2,z3,z480,z4,z8]),(0,[z0,z481,z1,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z227,z8]),(0,[z0,z1,z2,z3,z4,z346,z8]),(0,[z0,z104,z1,z2,z150,z4,z8]),(0,[z0,z1,z409,z2,z3,z4,z8]),(0,[z0,z1,z2,z133,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z414,z8]),(0,[z0,z1,z262,z2,z3,z4,z8])],[(1,[z0,z241,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z4,z482,z8]),(0,[z0,z1,z262,z2,z3,z4,z32])],[(0,[z25,z0,z1,z2,z158,z4,z8]),(0,[z0,z1,z2,z3,z483,z4,z8]),(0,[z0,z484,z1,z2,z3,z4,z8])],[(1,[z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z485,z4,z8])],[(0,[z0,z1,z2,z3,z4,z8,z486]),(0,[z28,z0,z1,z220,z3,z4,z8]),(0,[z0,z1,z2,z3,z487,z4,z8]),(0,[z0,z1,z2,z488,z3,z4,z8]),(1,[z0,z1,z23,z2,z162,z8]),(0,[z0,z1,z489,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z490,z4,z8]),(0,[z0,z491,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z72,z34,z8]),(0,[z492,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z493,z4,z8]),(0,[z0,z494,z1,z2,z3,z4,z8]),(0,[z0,z1,z23,z132,z2,z3,z8]),(0,[z0,z1,z2,z3,z495,z4,z8])],[(0,[z0,z496,z1,z2,z3,z4,z8]),(0,[z0,z1,z29,z46,z3,z4,z8]),(0,[z0,z1,z2,z497,z3,z4,z8]),(0,[z0,z498,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z499,z4,z8])],[(0,[z0,z1,z130,z220,z3,z4,z8]),(0,[z0,z1,z2,z133,z3,z72,z8]),(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z500,z4,z8]),(1,[z0,z1,z2,z133,z150,z8])]],
   [[(0,[z501,z0,z1,z2,z3,z4,z8]),(0,[z103,z0,z1,z502,z3,z4,z8]),(1,[z176,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z503,z4,z8])],[(1,[z0,z1,z2,z3,z504,z8]),(0,[z0,z12,z1,z112,z3,z4,z8])],[(0,[z505,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z287]),(0,[z0,z506,z1,z2,z3,z4,z8]),(0,[z243,z0,z507,z2,z3,z4,z8]),(0,[z0,z219,z1,z2,z3,z4,z205]),(0,[z0,z1,z2,z508,z3,z4,z8])],[(0,[z114,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z509,z4,z8]),(0,[z0,z1,z2,z3,z510,z4,z8]),(0,[z0,z1,z2,z220,z3,z4,z8]),(0,[z0,z1,z2,z133,z3,z22,z8]),(0,[z0,z1,z511,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z322,z8]),(0,[z0,z1,z2,z3,z512,z4,z8])],[(0,[z0,z1,z2,z513,z3,z4,z8]),(0,[z0,z1,z514,z2,z3,z4,z8]),(0,[z0,z12,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z515,z8]),(0,[z0,z1,z516,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z517,z4,z8])],[(1,[z0,z1,z2,z3,z4,z287]),(0,[z0,z1,z518,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z519,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z520,z8]),(0,[z0,z521,z1,z2,z3,z4,z8]),(0,[z0,z522,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z5,z8,z286]),(0,[z0,z1,z523,z2,z3,z4,z8])],[(0,[z68,z114,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z524,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z525,z8]),(0,[z0,z1,z2,z526,z3,z4,z8]),(0,[z0,z12,z1,z2,z3,z4,z44]),(0,[z0,z527,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z10,z11,z8])],[(0,[z0,z238,z2,z3,z4,z8,z85]),(0,[z0,z1,z2,z3,z528,z4,z8]),(0,[z0,z1,z507,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z165,z4,z8]),(0,[z28,z0,z219,z2,z3,z4,z8]),(0,[z0,z1,z2,z529,z3,z4,z8]),(0,[z0,z1,z530,z2,z3,z4,z8])],[(0,[z0,z1,z112,z130,z3,z4,z8]),(0,[z531,z0,z1,z2,z3,z4,z8]),(0,[z0,z532,z1,z2,z3,z4,z8]),(0,[z0,z12,z1,z2,z179,z4,z8]),(0,[z0,z12,z1,z2,z3,z4,z43])],[(0,[z0,z533,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z534])],[(0,[z0,z1,z2,z502,z3,z4,z8]),(0,[z535,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z536,z3,z4,z8]),(0,[z0,z1,z2,z537,z3,z4,z8]),(0,[z0,z538,z1,z2,z3,z4,z8])],[(0,[z68,z0,z1,z46,z3,z4,z8]),(0,[z0,z1,z2,z3,z22,z57,z8])]],
   [[(0,[z0,z539,z1,z2,z3,z4,z8]),(0,[z0,z1,z540,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z541,z8]),(0,[z0,z1,z2,z542,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z543])],[(0,[z0,z1,z544,z2,z3,z4,z8]),(1,[z0,z255,z1,z2,z3,z4]),(0,[z545,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z546,z8]),(0,[z0,z1,z2,z547,z3,z4,z8]),(0,[z111,z0,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z534]),(0,[z0,z1,z184,z2,z3,z8,z36])],[(0,[z0,z1,z2,z3,z10,z57,z8]),(0,[z548,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z549]),(0,[z0,z1,z2,z3,z4,z8,z550])],[(0,[z0,z1,z2,z3,z195,z4,z8]),(0,[z176,z0,z1,z2,z3,z4,z55]),(1,[z0,z1,z350,z2,z4,z8]),(0,[z551,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z552,z4,z8]),(0,[z0,z1,z2,z216,z4,z8,z42]),(0,[z0,z1,z553,z2,z3,z4,z8])],[(0,[z0,z554,z1,z2,z3,z4,z8]),(0,[z0,z1,z184,z2,z133,z3,z8])],[(0,[z25,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z555,z3,z4,z8]),(1,[z0,z1,z2,z3,z327,z8]),(0,[z0,z1,z556,z2,z3,z4,z8])],[(0,[z557,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z558,z8]),(0,[z0,z1,z2,z3,z559,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z560])]],
   [[(0,[z0,z561,z1,z2,z3,z4,z8])],[(0,[z0,z562,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z563,z4,z8]),(0,[z0,z564,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z565,z8]),(0,[z243,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z4,z8]),(1,[z0,z1,z3,z4,z8,z421])],[(0,[z0,z1,z2,z3,z26,z4,z8]),(0,[z0,z104,z1,z46,z3,z4,z8]),(0,[z0,z1,z112,z46,z3,z4,z8]),(0,[z201,z0,z1,z2,z3,z57,z8]),(0,[z0,z1,z2,z566,z3,z4,z8]),(0,[z0,z1,z2,z133,z3,z11,z8]),(0,[z0,z1,z2,z66,z150,z4,z8])],[(1,[z0,z1,z454,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z57,z8])],[(0,[z68,z0,z1,z2,z3,z440,z8]),(0,[z0,z1,z2,z207,z4,z11,z8])],[(0,[z263,z145,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z567]),(0,[z0,z1,z2,z568,z3,z4,z8]),(0,[z0,z1,z569,z2,z3,z4,z8]),(0,[z0,z570,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z2,z3,z4,z8]),(0,[z0,z1,z2,z571,z3,z4,z8])]],
   [[(0,[z0,z1,z572,z2,z3,z4,z8]),(0,[z0,z1,z573,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z285,z8]),(0,[z176,z0,z1,z2,z3,z4,z42]),(0,[z0,z19,z1,z2,z4,z8,z42]),(0,[z0,z1,z574,z2,z3,z4,z8]),(1,[z0,z1,z170,z2,z3,z8])],[(0,[z263,z0,z238,z2,z3,z4,z8]),(0,[z0,z1,z2,z575,z3,z4,z8]),(0,[z0,z2,z3,z4,z5,z8,z85])],[(0,[z576,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z577,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z578,z8]),(0,[z0,z12,z1,z2,z3,z4,z5]),(0,[z0,z1,z579,z2,z3,z4,z8]),(1,[z135,z0,z1,z3,z34,z8]),(0,[z135,z0,z1,z2,z133,z3,z8]),(0,[z0,z1,z2,z3,z4,z43,z42]),(0,[z580,z0,z1,z2,z3,z4,z8])],[(0,[z111,z0,z238,z2,z3,z4,z8]),(0,[z581,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z582,z2,z3,z4,z8]),(0,[z0,z583,z1,z2,z3,z4,z8]),(0,[z0,z12,z1,z3,z4,z8,z44])],[(0,[z0,z1,z2,z3,z4,z6,z8]),(0,[z0,z1,z2,z3,z4,z584,z8]),(0,[z0,z1,z585,z2,z3,z4,z8])],[(0,[z25,z1,z238,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z586]),(0,[z587,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z262,z2,z66,z4,z8])],[(0,[z0,z1,z2,z3,z110,z4,z8]),(0,[z0,z1,z2,z3,z4,z588,z8]),(0,[z243,z0,z1,z173,z3,z4,z8]),(0,[z0,z1,z2,z3,z589,z4,z8]),(0,[z0,z1,z2,z590,z3,z4,z8])],[(1,[z25,z238,z2,z3,z4,z8]),(0,[z0,z591,z1,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z592,z3,z4,z8]),(1,[z0,z1,z189,z2,z3,z4]),(0,[z0,z1,z46,z3,z4,z34,z8]),(0,[z0,z593,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z594,z8]),(0,[z0,z1,z2,z3,z595,z4,z8])],[(0,[z0,z211,z2,z3,z4,z72,z8]),(1,[z0,z1,z2,z66,z4,z32]),(0,[z0,z1,z596,z2,z3,z4,z8])],[(0,[z243,z176,z1,z2,z3,z4,z8]),(0,[z0,z18,z1,z2,z4,z8,z42]),(0,[z0,z1,z47,z3,z216,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z597]),(0,[z0,z1,z598,z2,z3,z4,z8])],[(0,[z0,z1,z2,z599,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z600]),(0,[z601,z0,z1,z2,z3,z4,z8]),(1,[z111,z0,z2,z3,z4,z5]),(0,[z602,z0,z1,z2,z3,z4,z8])],[(1,[z0,z1,z502,z3,z4,z8]),(0,[z201,z0,z1,z27,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z603,z8]),(0,[z0,z104,z1,z2,z216,z4,z8])],[(1,[z0,z1,z2,z3,z67,z8]),(0,[z0,z19,z2,z3,z148,z4,z8]),(0,[z0,z1,z2,z178,z3,z4,z8]),(0,[z0,z1,z128,z2,z3,z4,z8])],[(0,[z604,z0,z1,z2,z3,z4,z8]),(0,[z605,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z262,z2,z3,z4,z42])],[(0,[z606,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z607,z8]),(0,[z0,z1,z2,z3,z4,z8,z291]),(0,[z0,z1,z2,z608,z3,z4,z8]),(0,[z0,z1,z2,z150,z4,z8,z42])]],
   [[(1,[z201,z1,z2,z3,z57,z8]),(0,[z0,z19,z1,z2,z148,z4,z8]),(0,[z0,z1,z609,z2,z3,z4,z8])],[(0,[z0,z610,z1,z2,z3,z4,z8]),(0,[z201,z0,z1,z375,z3,z4,z8]),(0,[z0,z1,z2,z611,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z85,z42])],[(0,[z0,z1,z2,z3,z4,z612,z8]),(0,[z0,z1,z2,z3,z4,z613,z8]),(0,[z0,z1,z2,z3,z614,z4,z8]),(0,[z0,z1,z2,z3,z615,z4,z8])],[(1,[z263,z145,z2,z3,z4,z8]),(0,[z616,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z4,z8]),(0,[z0,z1,z2,z3,z79,z4,z8]),(0,[z0,z12,z1,z2,z3,z4,z85])],[(0,[z0,z1,z2,z3,z4,z617,z8]),(0,[z0,z1,z2,z3,z4,z618,z8]),(1,[z0,z1,z2,z3,z4,z291]),(0,[z0,z619,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z620,z3,z4,z8])],[(0,[z243,z0,z235,z2,z3,z4,z8]),(0,[z621,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z5,z42]),(0,[z0,z1,z622,z2,z3,z4,z8]),(0,[z0,z104,z1,z2,z3,z4,z344]),(0,[z0,z1,z2,z623,z3,z4,z8]),(0,[z0,z1,z128,z2,z47,z4,z8]),(0,[z0,z1,z2,z3,z4,z624,z8])],[(0,[z625,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z626,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z500,z216,z8])],[(0,[z0,z627,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z628,z4,z8]),(0,[z0,z241,z2,z3,z4,z8,z85]),(0,[z0,z1,z23,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z629,z8])],[(0,[z145,z1,z238,z2,z3,z4,z8]),(0,[z0,z1,z130,z3,z4,z8,z44]),(0,[z0,z1,z2,z630,z3,z4,z8]),(1,[z78,z1,z2,z3,z79,z8]),(0,[z0,z219,z29,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z504,z8]),(0,[z0,z1,z132,z2,z3,z4,z8])],[(0,[z631,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z632,z2,z3,z4,z8]),(0,[z0,z18,z1,z2,z148,z4,z8]),(0,[z0,z1,z2,z3,z4,z72,z8]),(1,[z0,z1,z2,z3,z500,z8])],[(0,[z0,z1,z2,z3,z4,z633,z8]),(1,[z0,z104,z1,z216,z4,z8]),(0,[z634,z0,z1,z2,z3,z4,z8])],[(1,[z0,z507,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z635])],[(0,[z636,z0,z1,z2,z3,z4,z8]),(0,[z637,z0,z1,z2,z3,z4,z8]),(1,[z0,z1,z375,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z638]),(0,[z0,z1,z2,z3,z4,z8,z44])],[(0,[z0,z1,z2,z3,z639,z4,z8]),(0,[z0,z18,z1,z2,z3,z4,z8]),(0,[z0,z1,z23,z2,z3,z72,z8]),(0,[z0,z1,z2,z3,z640,z4,z8]),(0,[z0,z104,z1,z3,z4,z43,z8]),(0,[z0,z1,z2,z3,z216,z4,z8]),(0,[z0,z1,z2,z3,z4,z641,z8]),(0,[z0,z1,z2,z3,z4,z8,z421])],[(0,[z642,z0,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z63,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z643]),(0,[z0,z1,z2,z3,z644,z4,z8])]],
   [[(0,[z0,z1,z2,z3,z645,z4,z8]),(0,[z0,z646,z1,z2,z3,z4,z8]),(0,[z0,z21,z1,z2,z3,z4,z8]),(1,[z0,z12,z1,z3,z4,z44]),(0,[z0,z1,z2,z3,z4,z647,z8]),(0,[z0,z1,z2,z3,z4,z32,z8])],[(1,[z0,z1,z2,z3,z26,z8]),(0,[z0,z1,z2,z648,z3,z4,z8]),(0,[z0,z649,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z51,z8]),(0,[z0,z1,z23,z2,z3,z22,z8]),(0,[z0,z1,z2,z650,z3,z4,z8])],[(0,[z0,z651,z1,z2,z3,z4,z8]),(0,[z176,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z652,z8]),(0,[z135,z0,z1,z132,z3,z4,z8])],[(0,[z0,z1,z2,z3,z10,z79,z8]),(0,[z0,z653,z1,z2,z3,z4,z8]),(0,[z0,z18,z1,z2,z3,z504,z8]),(1,[z0,z1,z2,z179,z4,z8])],[(0,[z0,z1,z2,z654,z3,z4,z8]),(0,[z0,z655,z1,z2,z3,z4,z8]),(0,[z656,z0,z1,z2,z3,z4,z8]),(0,[z657,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z658,z4,z8])],[(0,[z0,z0,z1,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z51]),(0,[z0,z1,z2,z3,z4,z659,z8]),(0,[z660,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z661,z8]),(0,[z0,z1,z2,z3,z662,z4,z8]),(0,[z0,z1,z2,z133,z3,z162,z8])],[(0,[z0,z663,z1,z2,z3,z4,z8]),(0,[z0,z1,z664,z2,z3,z4,z8]),(0,[z0,z1,z665,z2,z3,z4,z8]),(0,[z0,z21,z1,z2,z3,z72,z8]),(0,[z0,z1,z666,z2,z3,z4,z8]),(0,[z0,z1,z170,z2,z3,z4,z8])]],
   [[(0,[z25,z0,z1,z2,z3,z67,z8]),(0,[z0,z1,z667,z2,z3,z4,z8]),(0,[z243,z0,z1,z2,z165,z4,z8]),(1,[z0,z1,z262,z2,z4,z42])],[(0,[z0,z1,z454,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z668]),(0,[z0,z669,z1,z2,z3,z4,z8]),(0,[z0,z1,z184,z2,z3,z4,z11])],[(1,[z0,z1,z2,z3,z110,z8]),(1,[z0,z1,z2,z3,z4,z323]),(1,[z0,z1,z128,z47,z4,z8]),(0,[z0,z670,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z671,z4,z8]),(0,[z0,z1,z2,z3,z672,z4,z8]),(0,[z0,z21,z1,z2,z3,z22,z8])],[(0,[z0,z673,z1,z2,z3,z4,z8]),(0,[z1,z2,z62,z3,z146,z4,z8]),(0,[z0,z1,z2,z3,z4,z674,z8]),(0,[z0,z1,z2,z675,z3,z4,z8])],[(0,[z201,z0,z1,z2,z3,z79,z8]),(0,[z0,z1,z2,z3,z4,z676,z8]),(0,[z0,z1,z2,z3,z150,z4,z8]),(0,[z0,z1,z23,z2,z3,z4,z534])],[(0,[z0,z677,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z169,z8]),(0,[z0,z1,z678,z2,z3,z4,z8]),(0,[z0,z1,z184,z2,z3,z4,z36])],[(0,[z0,z1,z2,z679,z3,z4,z8]),(0,[z0,z1,z2,z66,z216,z4,z8])]],
   [[(0,[z0,z680,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z681,z3,z4,z8]),(0,[z0,z1,z682,z2,z3,z4,z8])],[(0,[z0,z1,z189,z2,z3,z4,z8]),(0,[z0,z1,z2,z683,z3,z4,z8]),(1,[z0,z21,z2,z3,z22,z8]),(0,[z684,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z23,z2,z133,z4,z8]),(0,[z0,z1,z2,z66,z4,z32,z8])],[(0,[z263,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z685,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z686,z8]),(0,[z0,z1,z2,z3,z4,z687,z8]),(0,[z0,z1,z2,z3,z4,z6,z85]),(0,[z28,z0,z2,z220,z3,z4,z8]),(0,[z0,z1,z688,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z689,z8])],[(0,[z0,z690,z1,z2,z3,z4,z8]),(0,[z0,z1,z691,z2,z3,z4,z8]),(0,[z0,z1,z29,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z692,z8])],[(0,[z0,z145,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z693,z3,z4,z8]),(0,[z0,z1,z694,z2,z3,z4,z8]),(0,[z0,z19,z1,z2,z3,z4,z228]),(0,[z0,z1,z2,z3,z4,z8,z695]),(0,[z0,z1,z696,z2,z3,z4,z8])],[(0,[z697,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z133,z3,z79,z8]),(0,[z0,z1,z2,z3,z4,z698,z8]),(0,[z0,z1,z2,z3,z4,z699,z8]),(0,[z0,z1,z2,z700,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z11,z8])],[(0,[z0,z1,z701,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z702,z8]),(0,[z0,z1,z703,z2,z3,z4,z8]),(0,[z0,z2,z149,z3,z148,z4,z8]),(0,[z0,z1,z2,z3,z4,z8,z704]),(0,[z705,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z706,z4,z8])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z4,z8]),(1,[z0,z2,z3,z4,z708]),(0,[z0,z1,z2,z3,z4,z709]),(0,[z0,z1,z23,z2,z658,z8])],[(0,[z81,z1,z130,z3,z4,z8]),(0,[z0,z1,z2,z710,z4,z8]),(0,[z0,z1,z2,z3,z4,z711]),(0,[z0,z1,z2,z3,z4,z107]),(1,[z0,z1,z3,z4,z712]),(0,[z0,z1,z2,z3,z4,z713])],[(0,[z0,z714,z2,z3,z4,z8])],[(0,[z0,z507,z112,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z291]),(0,[z0,z1,z184,z2,z3,z715])],[(0,[z0,z238,z2,z3,z4,z50]),(0,[z0,z1,z716,z3,z4,z8]),(0,[z243,z1,z2,z3,z4,z335]),(0,[z0,z1,z717,z2,z3,z8]),(0,[z0,z1,z2,z3,z715,z36])],[(0,[z0,z1,z718,z3,z4,z8]),(0,[z0,z719,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z708,z8]),(0,[z0,z720,z2,z3,z4,z8])],[(0,[z0,z1,z721,z2,z3,z4]),(0,[z0,z1,z722,z2,z3,z8])],[(0,[z0,z1,z664,z47,z4,z8]),(0,[z0,z1,z27,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z2,z3,z724,z8]),(0,[z0,z1,z2,z725,z4,z8])]],
   [[(0,[z78,z1,z2,z3,z79,z8]),(0,[z0,z321,z1,z23,z2,z8])],[(0,[z0,z1,z2,z726,z4,z8]),(0,[z0,z1,z2,z47,z4,z107])],[(0,[z0,z1,z727,z2,z3,z8]),(0,[z0,z104,z1,z216,z4,z8])],[(0,[z0,z507,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z728]),(0,[z0,z1,z729,z2,z13,z8])],[(0,[z0,z1,z375,z3,z4,z8]),(0,[z0,z1,z2,z730,z4,z8]),(0,[z0,z507,z2,z3,z4,z32]),(0,[z0,z507,z2,z63,z4,z8]),(0,[z176,z0,z97,z1,z3,z4]),(0,[z0,z1,z731,z3,z4,z8]),(0,[z0,z1,z47,z13,z4,z8])],[(0,[z0,z1,z2,z3,z11,z14])],[(0,[z0,z1,z2,z732,z4,z8])],[(0,[z0,z1,z2,z3,z733,z8]),(0,[z0,z734,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z735,z8]),(0,[z0,z12,z1,z3,z4,z44]),(0,[z0,z1,z112,z3,z4,z43]),(0,[z0,z1,z736,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z3,z26,z8]),(0,[z68,z1,z737,z3,z4,z8]),(0,[z0,z2,z3,z738,z4,z8]),(0,[z0,z739,z2,z3,z4,z8])],[(0,[z145,z714,z2,z3,z4,z8]),(0,[z0,z1,z740,z3,z4,z8]),(0,[z0,z1,z3,z4,z43,z107]),(0,[z0,z1,z409,z128,z2,z8]),(0,[z0,z1,z2,z3,z4,z741])],[(0,[z0,z1,z2,z4,z228,z42]),(0,[z0,z1,z2,z178,z4,z32]),(0,[z0,z104,z1,z742,z4,z8]),(0,[z0,z1,z743,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z744]),(0,[z0,z1,z2,z3,z745,z8]),(0,[z0,z69,z2,z3,z72,z8])],[],[(0,[z0,z1,z2,z3,z4,z51]),(0,[z0,z1,z101,z3,z327,z8]),(0,[z0,z1,z2,z3,z746,z8]),(0,[z0,z1,z2,z3,z4,z708]),(0,[z0,z12,z1,z3,z4,z712])],[(0,[z0,z1,z2,z747,z4,z8]),(0,[z25,z238,z37,z3,z4,z8]),(0,[z0,z1,z2,z748,z4,z8]),(0,[z0,z1,z749,z3,z4,z8])],[(0,[z0,z1,z750,z2,z4,z8]),(0,[z0,z97,z1,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z712])]],
   [[(0,[z0,z1,z2,z3,z26,z51]),(0,[z684,z238,z2,z3,z4,z8]),(0,[z0,z1,z3,z4,z751,z8]),(0,[z114,z1,z46,z3,z4,z8])],[(0,[z0,z129,z2,z3,z72,z8]),(0,[z0,z1,z2,z4,z8,z752])],[(0,[z0,z1,z2,z3,z4,z753]),(0,[z0,z1,z2,z754,z4,z8]),(0,[z0,z2,z149,z755,z4,z8]),(0,[z0,z211,z2,z3,z72,z8])],[(0,[z0,z12,z1,z3,z4,z668])],[(0,[z0,z1,z37,z3,z67,z8]),(0,[z0,z1,z130,z3,z440,z8]),(0,[z0,z1,z173,z3,z285,z8]),(0,[z0,z1,z2,z3,z756,z8])],[(0,[z428,z1,z2,z3,z79,z8]),(0,[z0,z757,z220,z3,z4,z8]),(0,[z0,z1,z758,z3,z4,z8])],[(0,[z25,z238,z2,z3,z4,z50]),(0,[z68,z1,z130,z3,z440,z8]),(0,[z0,z1,z2,z3,z4,z205]),(0,[z0,z1,z759,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z760]),(0,[z0,z104,z1,z700,z4,z8]),(0,[z0,z1,z170,z2,z3,z11])],[(0,[z0,z1,z2,z761,z4,z8]),(0,[z0,z762,z2,z3,z4,z8]),(0,[z68,z255,z1,z130,z3,z4]),(0,[z0,z97,z1,z47,z4,z8])]],
   [[(0,[z0,z1,z763,z2,z3,z4]),(0,[z436,z1,z2,z146,z4,z8]),(0,[z0,z764,z2,z3,z4,z8]),(1,[z0,z757,z3,z4,z8]),(0,[z0,z21,z2,z3,z22,z8]),(0,[z0,z765,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z766,z8]),(0,[z0,z1,z2,z3,z767,z8])],[(0,[z0,z1,z2,z3,z768,z8]),(0,[z0,z1,z2,z3,z4,z769]),(0,[z0,z1,z2,z3,z770,z8]),(0,[z0,z1,z2,z771,z4,z8]),(0,[z0,z1,z772,z3,z4,z8])],[(0,[z0,z1,z170,z2,z3,z36])],[(0,[z0,z1,z773,z3,z4,z8])],[(0,[z0,z1,z2,z774,z4,z8]),(0,[z176,z0,z1,z2,z13,z4]),(0,[z0,z1,z2,z4,z323,z775]),(0,[z0,z211,z2,z3,z776,z8])],[(0,[z458,z1,z2,z3,z79,z8]),(0,[z0,z507,z2,z3,z327,z8]),(0,[z0,z1,z2,z3,z4,z777])],[(0,[z0,z1,z2,z778,z4,z8]),(0,[z0,z21,z2,z3,z776,z8]),(0,[z0,z1,z3,z33,z779,z8])]],
   [[(0,[z111,z0,z2,z3,z4,z708]),(0,[z135,z0,z1,z350,z2,z8])],[(0,[z0,z1,z2,z780,z162,z8])],[(0,[z0,z1,z2,z3,z781,z8]),(0,[z0,z1,z101,z3,z285,z8]),(0,[z0,z1,z2,z3,z782,z8]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z1,z784,z2,z3,z4])],[(0,[z0,z255,z1,z3,z4,z44])],[(0,[z0,z1,z46,z3,z440,z8]),(0,[z0,z1,z2,z3,z785,z8])],[(0,[z0,z1,z786,z3,z4,z8]),(0,[z0,z1,z2,z3,z787,z8]),(0,[z0,z1,z788,z3,z4,z8])],[(0,[z0,z1,z2,z66,z4,z713])],[(0,[z0,z1,z173,z3,z4,z8]),(1,[z0,z1,z2,z780,z8])]],
   [[(0,[z0,z1,z37,z3,z26,z8]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z0,z1,z173,z3,z4,z32]),(0,[z0,z1,z2,z3,z790,z8]),(0,[z0,z791,z2,z3,z4,z8])],[],[(0,[z0,z1,z792,z3,z4,z8]),(0,[z213,z1,z2,z3,z57,z8]),(0,[z0,z1,z2,z178,z4,z228]),(0,[z0,z1,z2,z793,z4,z8])],[(0,[z0,z1,z2,z3,z4,z794]),(0,[z0,z1,z27,z3,z57,z8]),(0,[z0,z1,z23,z2,z603,z8]),(0,[z0,z2,z3,z4,z708,z85])],[(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z132,z3,z204,z8]),(0,[z0,z507,z2,z3,z4,z55]),(0,[z0,z97,z1,z3,z4,z5]),(0,[z0,z1,z3,z742,z4,z8]),(0,[z0,z1,z2,z66,z4,z676])],[(0,[z0,z1,z2,z3,z4,z50]),(0,[z0,z1,z37,z3,z4,z51]),(0,[z0,z1,z796,z3,z4,z8]),(0,[z0,z12,z1,z173,z3,z4]),(0,[z0,z1,z757,z3,z4,z8])],[(0,[z0,z1,z797,z3,z4,z8]),(0,[z68,z1,z189,z130,z3,z4]),(0,[z138,z1,z46,z3,z4,z8])],[(0,[z1,z2,z798,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z799]),(0,[z0,z1,z2,z800,z13,z8]),(0,[z0,z1,z2,z8,z93,z102])]],
   [[(0,[z0,z1,z112,z3,z4,z141]),(0,[z0,z1,z47,z742,z4,z8])],[(0,[z28,z0,z220,z3,z266,z8]),(0,[z0,z801,z1,z3,z4,z8]),(0,[z0,z2,z3,z22,z776,z8]),(0,[z0,z1,z2,z133,z427,z8])],[(0,[z0,z1,z2,z3,z802,z8]),(0,[z0,z1,z2,z3,z803,z8]),(0,[z1,z46,z737,z3,z4,z8]),(0,[z0,z1,z2,z3,z804,z8]),(0,[z0,z19,z2,z148,z4,z228]),(0,[z0,z1,z2,z800,z3,z8])],[(0,[z0,z1,z2,z3,z4,z805]),(0,[z0,z507,z101,z3,z4,z8]),(0,[z0,z1,z2,z3,z8,z806])],[(0,[z0,z83,z2,z3,z4,z85]),(0,[z201,z1,z27,z3,z57,z8]),(0,[z0,z18,z2,z755,z4,z8])],[(0,[z0,z1,z2,z3,z4,z807]),(0,[z0,z1,z2,z4,z8,z102])],[(0,[z0,z235,z2,z3,z4,z8]),(0,[z0,z808,z2,z3,z4,z8]),(0,[z1,z2,z798,z146,z4,z8]),(0,[z580,z1,z2,z3,z57,z8]),(0,[z0,z1,z2,z3,z79,z534]),(0,[z0,z1,z101,z63,z4,z8]),(0,[z0,z1,z2,z165,z285,z8]),(0,[z0,z1,z2,z809,z4,z8])],[(0,[z0,z1,z810,z2,z3,z4]),(0,[z1,z2,z3,z4,z8,z811])]],
   [[(0,[z0,z1,z293,z158,z4,z8]),(0,[z0,z1,z2,z3,z812,z8]),(0,[z0,z1,z2,z3,z4,z813]),(0,[z0,z1,z814,z3,z4,z8]),(0,[z0,z1,z350,z2,z79,z8]),(0,[z0,z1,z23,z2,z8,z102])],[(0,[z0,z1,z2,z3,z4,z815]),(0,[z1,z2,z3,z79,z816,z8]),(0,[z0,z1,z191,z3,z33,z8]),(0,[z0,z507,z2,z3,z4,z42]),(0,[z111,z0,z2,z178,z4,z5]),(0,[z0,z104,z1,z216,z4,z107])],[(0,[z1,z714,z2,z3,z4,z8]),(0,[z0,z1,z817,z2,z3,z4]),(0,[z0,z1,z2,z3,z818,z8]),(0,[z0,z819,z2,z3,z4,z8]),(0,[z0,z12,z1,z3,z4,z107])],[(0,[z25,z238,z2,z195,z4,z8]),(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z219,z29,z3,z4,z8])],[(0,[z0,z1,z2,z63,z4,z42]),(0,[z0,z1,z2,z3,z821,z8]),(0,[z0,z1,z2,z822,z4,z8])],[(1,[z1,z2,z3,z816,z8]),(0,[z0,z1,z2,z3,z823,z8])],[(0,[z0,z2,z3,z4,z776,z8])],[(0,[z0,z1,z2,z3,z67,z51]),(0,[z0,z1,z2,z824,z4,z8]),(0,[z0,z1,z2,z4,z8,z825])]],
   [[(0,[z0,z1,z2,z826,z4,z8]),(0,[z0,z1,z2,z827,z4,z8]),(0,[z828,z1,z2,z3,z4,z8]),(0,[z0,z1,z3,z4,z8,z829]),(0,[z135,z0,z1,z350,z34,z8])],[],[(0,[z0,z1,z173,z3,z327,z8]),(0,[z0,z1,z2,z4,z8,z775]),(0,[z1,z2,z3,z4,z8,z830])],[(0,[z714,z238,z2,z3,z4,z8]),(0,[z0,z1,z2,z831,z4,z8]),(0,[z0,z90,z2,z3,z4,z85]),(0,[z135,z0,z1,z3,z779,z8])],[],[(0,[z0,z1,z2,z3,z4,z832])],[(0,[z0,z1,z2,z833,z4,z8]),(0,[z834,z1,z2,z3,z4,z8]),(0,[z0,z1,z184,z2,z3,z36])],[(0,[z0,z1,z2,z4,z8,z835])]],
   [[(0,[z0,z836,z2,z3,z4,z8]),(0,[z0,z1,z2,z133,z490,z8]),(0,[z0,z1,z837,z3,z4,z8]),(0,[z0,z1,z553,z3,z4,z43]),(0,[z0,z1,z170,z3,z8,z421])],[(0,[z0,z1,z838,z2,z3,z4]),(0,[z0,z255,z1,z173,z3,z4]),(0,[z0,z1,z2,z165,z4,z8]),(0,[z0,z1,z839,z2,z3,z8]),(0,[z0,z1,z729,z2,z3,z8])],[(0,[z0,z1,z2,z4,z169,z8])],[(0,[z0,z1,z454,z3,z136,z8])],[(0,[z0,z1,z2,z3,z4,z840]),(0,[z0,z1,z2,z3,z816,z8]),(0,[z0,z1,z2,z178,z4,z8])],[(0,[z0,z1,z37,z3,z4,z50]),(0,[z0,z1,z841,z2,z3,z4]),(0,[z842,z1,z2,z3,z4,z8]),(0,[z0,z104,z1,z409,z216,z8]),(0,[z0,z1,z2,z3,z843,z8])],[(0,[z0,z1,z2,z3,z4,z844]),(0,[z0,z1,z845,z3,z4,z8]),(0,[z0,z1,z309,z2,z3,z36]),(0,[z0,z1,z846,z2,z3,z8]),(0,[z0,z1,z847,z3,z4,z8]),(0,[z0,z2,z3,z776,z72,z8]),(0,[z0,z481,z2,z3,z4,z5]),(0,[z0,z1,z112,z3,z4,z712])],[(0,[z0,z1,z2,z848,z4,z8]),(0,[z0,z1,z2,z3,z266,z8])]],
   [[(0,[z0,z1,z2,z4,z849,z8]),(0,[z0,z1,z850,z2,z3,z8]),(0,[z0,z12,z1,z179,z4,z44])],[(0,[z0,z1,z851,z3,z4,z8]),(0,[z0,z235,z2,z3,z327,z8])],[(0,[z0,z1,z2,z195,z4,z8])],[(0,[z0,z1,z2,z3,z4,z322]),(0,[z0,z852,z1,z3,z4,z8]),(0,[z0,z1,z2,z4,z8,z853])],[(0,[z0,z1,z293,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z854]),(0,[z0,z1,z2,z3,z855,z8]),(0,[z0,z19,z2,z148,z4,z8])],[(0,[z0,z1,z2,z3,z856,z8]),(0,[z0,z1,z2,z195,z26,z8]),(0,[z0,z1,z2,z857,z4,z8]),(0,[z201,z1,z2,z3,z816,z8]),(0,[z0,z1,z2,z4,z8,z858])],[(0,[z0,z97,z1,z3,z4,z44])],[(0,[z25,z714,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z859,z8]),(0,[z0,z1,z2,z542,z4,z42])]],
   [[(0,[z0,z1,z2,z3,z860,z8]),(0,[z0,z1,z2,z3,z861,z8]),(0,[z124,z1,z2,z62,z4,z8]),(0,[z243,z1,z2,z3,z285,z55]),(0,[z0,z1,z47,z4,z8,z294]),(0,[z0,z97,z1,z3,z4,z43])],[(0,[z156,z1,z130,z3,z4,z8]),(0,[z0,z1,z2,z66,z71,z8]),(0,[z0,z1,z2,z13,z4,z8])],[(0,[z0,z862,z1,z2,z3,z8]),(0,[z0,z255,z1,z47,z3,z4]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z1,z2,z3,z8,z93])],[(0,[z0,z1,z502,z3,z136,z8]),(0,[z0,z1,z2,z3,z4,z864])],[(0,[z0,z507,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z865])],[(0,[z0,z1,z173,z3,z4,z42]),(0,[z0,z1,z2,z13,z4,z44])],[(0,[z0,z1,z2,z866,z4,z8]),(0,[z68,z1,z130,z3,z4,z8]),(0,[z0,z1,z2,z3,z867,z8]),(0,[z0,z1,z2,z3,z868,z8]),(0,[z0,z1,z2,z3,z4,z869])],[(0,[z0,z1,z2,z3,z67,z50]),(0,[z0,z1,z2,z870,z3,z8]),(0,[z0,z1,z2,z13,z4,z43])]],
   [[(0,[z0,z1,z2,z3,z871,z8]),(0,[z328,z1,z130,z3,z4,z8]),(0,[z657,z1,z2,z146,z4,z8]),(0,[z0,z1,z872,z3,z4,z8]),(0,[z0,z1,z23,z2,z54,z8])],[(0,[z0,z1,z2,z3,z873,z8]),(0,[z0,z1,z2,z3,z4,z874])],[(0,[z0,z875,z2,z3,z4,z8]),(0,[z0,z219,z757,z3,z4,z8])],[(0,[z0,z1,z2,z158,z4,z8]),(0,[z0,z255,z1,z2,z774,z4]),(0,[z0,z1,z2,z876,z4,z8]),(0,[z0,z1,z23,z99,z2,z8]),(0,[z0,z1,z2,z3,z877,z8])],[(0,[z0,z1,z2,z3,z4,z878]),(0,[z111,z0,z2,z3,z4,z299]),(0,[z0,z1,z2,z3,z4,z879]),(0,[z0,z1,z880,z3,z4,z8]),(0,[z0,z1,z2,z165,z327,z8]),(0,[z0,z1,z2,z3,z881,z8])],[(0,[z0,z1,z2,z3,z882,z8]),(0,[z1,z2,z3,z4,z6,z811]),(0,[z0,z2,z3,z4,z883,z8]),(0,[z0,z1,z2,z207,z4,z414])],[(0,[z0,z235,z2,z3,z285,z8]),(0,[z884,z1,z2,z3,z4,z8])],[(0,[z0,z1,z885,z3,z4,z8]),(0,[z0,z1,z2,z4,z780,z8])]],
   [[(0,[z0,z507,z173,z3,z4,z8])],[(0,[z0,z1,z2,z3,z886,z8]),(0,[z0,z1,z2,z3,z4,z887]),(0,[z28,z0,z220,z3,z346,z8]),(1,[z0,z1,z2,z4,z713])],[(0,[z68,z1,z130,z3,z110,z8]),(0,[z0,z1,z2,z3,z4,z414]),(0,[z0,z1,z23,z2,z780,z8])],[(0,[z0,z1,z3,z4,z8,z888]),(0,[z0,z1,z2,z4,z8,z889]),(0,[z243,z1,z2,z3,z4,z55]),(0,[z0,z1,z173,z63,z4,z8]),(0,[z0,z1,z2,z3,z4,z890]),(0,[z0,z891,z1,z3,z4,z8]),(0,[z0,z1,z23,z2,z162,z414]),(0,[z0,z1,z3,z4,z892,z8]),(0,[z0,z97,z1,z170,z3,z8])],[(0,[z0,z1,z2,z3,z4,z893]),(0,[z243,z1,z2,z63,z4,z55]),(0,[z894,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z8,z713])],[(0,[z0,z1,z2,z3,z136,z8]),(0,[z0,z1,z2,z4,z414,z42])],[(0,[z0,z1,z112,z173,z3,z4]),(0,[z895,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z8,z715])],[(0,[z0,z1,z2,z896,z4,z8]),(0,[z154,z1,z130,z3,z4,z8]),(0,[z0,z1,z2,z876,z4,z323]),(0,[z0,z1,z2,z3,z897,z8]),(1,[z0,z1,z742,z4,z8])]],
   [[(0,[z0,z1,z2,z3,z898,z8]),(0,[z0,z1,z2,z899,z4,z8])],[(0,[z0,z562,z2,z148,z4,z8]),(0,[z0,z1,z2,z4,z900,z8]),(0,[z0,z1,z2,z3,z901,z8])],[(0,[z0,z1,z37,z195,z4,z8]),(0,[z0,z1,z902,z3,z4,z8]),(0,[z0,z1,z2,z3,z903,z4]),(0,[z0,z1,z2,z904,z4,z8])],[(0,[z0,z1,z2,z905,z4,z8]),(0,[z0,z1,z2,z3,z26,z50]),(0,[z0,z1,z2,z3,z906,z8]),(0,[z407,z1,z46,z3,z4,z8]),(0,[z0,z355,z2,z3,z22,z8]),(0,[z0,z1,z2,z3,z907,z8]),(0,[z0,z1,z2,z3,z8,z908])],[(0,[z0,z1,z2,z3,z909,z8]),(0,[z0,z12,z507,z2,z3,z4])],[(0,[z0,z1,z2,z3,z910,z8])],[(0,[z0,z1,z2,z13,z4,z5])],[(0,[z0,z1,z911,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z912]),(0,[z0,z1,z2,z4,z913,z8])]],
   [[(0,[z0,z1,z2,z3,z914,z8]),(1,[z1,z2,z3,z4,z811])],[(0,[z0,z1,z2,z3,z915,z4]),(0,[z0,z1,z2,z4,z322,z42]),(0,[z0,z1,z101,z165,z4,z8])],[(0,[z0,z1,z2,z3,z440,z8]),(0,[z0,z235,z2,z63,z4,z8]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z0,z1,z2,z207,z4,z8])],[(0,[z0,z104,z1,z308,z4,z8]),(0,[z0,z18,z2,z149,z4,z8]),(0,[z0,z1,z132,z3,z33,z8]),(0,[z0,z1,z2,z207,z4,z32])],[(0,[z0,z1,z917,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z918])],[(0,[z0,z919,z1,z3,z4,z8]),(0,[z0,z241,z2,z3,z4,z85]),(0,[z135,z0,z1,z700,z3,z8])],[(0,[z0,z1,z2,z3,z4,z920]),(0,[z0,z2,z3,z4,z8,z921]),(0,[z0,z371,z2,z3,z4,z5])],[]],
   [[(0,[z25,z238,z293,z3,z4,z8]),(0,[z0,z922,z1,z2,z4,z8]),(0,[z0,z1,z2,z3,z4,z923]),(0,[z0,z97,z1,z3,z4,z85]),(0,[z0,z1,z2,z3,z924,z8]),(0,[z0,z1,z23,z2,z162,z8])],[(0,[z0,z1,z2,z3,z925,z8]),(0,[z0,z1,z2,z926,z4,z8]),(0,[z0,z18,z2,z149,z504,z8]),(0,[z0,z1,z2,z150,z780,z8])],[(0,[z0,z1,z2,z927,z4,z8]),(0,[z0,z1,z2,z3,z928,z8]),(0,[z1,z2,z3,z4,z811,z55]),(0,[z0,z1,z2,z178,z4,z42]),(0,[z0,z1,z3,z779,z34,z8])],[(0,[z0,z2,z757,z3,z4,z8]),(0,[z111,z0,z2,z4,z5,z286]),(0,[z0,z104,z1,z216,z4,z344]),(0,[z0,z1,z128,z4,z647,z8]),(0,[z0,z1,z2,z133,z150,z8])],[(0,[z0,z1,z2,z195,z67,z8]),(0,[z1,z737,z130,z3,z4,z8]),(0,[z61,z1,z2,z798,z4,z8]),(0,[z0,z1,z2,z3,z929,z8]),(0,[z465,z1,z2,z3,z79,z8]),(0,[z0,z1,z2,z3,z4,z930]),(0,[z0,z1,z2,z931,z4,z8])],[(0,[z0,z932,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z1,z2,z742,z4,z8]),(0,[z0,z1,z262,z2,z93,z42])],[(0,[z0,z1,z293,z3,z67,z8]),(0,[z263,z714,z2,z3,z4,z8]),(0,[z243,z1,z2,z3,z327,z55]),(0,[z0,z1,z112,z547,z3,z4]),(0,[z0,z2,z3,z4,z5,z708]),(0,[z0,z1,z2,z3,z4,z344]),(0,[z0,z1,z2,z4,z692,z42])],[(0,[z0,z1,z2,z3,z227,z8]),(0,[z0,z1,z2,z934,z4,z8]),(0,[z0,z1,z2,z3,z4,z811]),(0,[z0,z1,z2,z3,z346,z8]),(0,[z0,z334,z2,z3,z22,z8]),(0,[z0,z1,z2,z13,z4,z85]),(0,[z935,z1,z2,z3,z4,z8])]],
   [[(0,[z0,z1,z2,z936,z4,z8]),(0,[z0,z1,z2,z3,z4,z937])],[(0,[z0,z1,z2,z3,z4,z938]),(0,[z0,z1,z2,z133,z640,z8]),(0,[z0,z97,z1,z3,z4,z107]),(0,[z0,z1,z128,z742,z4,z8])],[(0,[z0,z255,z1,z112,z3,z4]),(0,[z0,z1,z2,z3,z4,z939]),(0,[z0,z1,z940,z3,z4,z8]),(0,[z0,z507,z2,z165,z4,z8]),(0,[z0,z219,z29,z3,z4,z323]),(0,[z0,z1,z941,z3,z4,z8]),(0,[z0,z1,z2,z3,z942,z8])],[(0,[z0,z1,z2,z3,z4,z287]),(0,[z0,z1,z2,z3,z943,z8]),(0,[z0,z1,z23,z2,z11,z42])],[(0,[z0,z1,z2,z944,z4,z8]),(0,[z0,z1,z514,z3,z33,z8])],[(0,[z176,z1,z569,z2,z3,z4])],[(0,[z0,z104,z255,z1,z3,z4]),(0,[z0,z1,z2,z3,z945,z8]),(0,[z0,z946,z2,z3,z4,z8]),(0,[z0,z1,z947,z3,z4,z8]),(0,[z0,z1,z3,z4,z43,z470])],[(0,[z25,z238,z2,z158,z4,z8]),(0,[z0,z1,z511,z2,z4,z42])]],
   [[(0,[z176,z1,z2,z3,z4,z24]),(0,[z0,z1,z2,z3,z8,z948])],[],[],[(0,[z0,z1,z130,z3,z4,z107]),(0,[z949,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z950]),(0,[z0,z1,z2,z3,z951,z8])],[(0,[z0,z1,z2,z798,z4,z8]),(0,[z0,z1,z952,z3,z4,z8]),(0,[z0,z1,z2,z8,z953,z286])],[(0,[z0,z1,z2,z158,z67,z8]),(0,[z0,z19,z2,z755,z4,z8])],[(0,[z0,z145,z2,z3,z4,z50]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z23,z2,z162,z534])],[(0,[z0,z1,z2,z3,z955,z8]),(0,[z0,z1,z2,z63,z4,z322]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z1,z350,z2,z4,z8]),(0,[z0,z957,z2,z3,z4,z8]),(0,[z0,z1,z2,z66,z4,z414])]],
   [[(0,[z0,z1,z2,z958,z4,z8]),(0,[z0,z1,z2,z3,z4,z959])],[(0,[z0,z1,z2,z3,z960,z8]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z4,z962])],[(0,[z0,z1,z293,z3,z26,z8]),(0,[z366,z1,z2,z3,z79,z8]),(0,[z0,z609,z2,z3,z4,z85]),(0,[z0,z241,z2,z3,z4,z708])],[(0,[z0,z1,z963,z3,z4,z8]),(0,[z243,z1,z101,z3,z4,z55]),(0,[z0,z1,z3,z4,z8,z964]),(0,[z0,z1,z170,z262,z2,z42])],[(0,[z1,z2,z737,z3,z4,z8]),(0,[z0,z965,z2,z3,z4,z8]),(0,[z0,z1,z2,z966,z4,z8]),(0,[z0,z1,z967,z2,z3,z8])],[(0,[z0,z1,z2,z195,z4,z51]),(0,[z0,z1,z2,z3,z968,z8]),(0,[z0,z969,z2,z3,z4,z8]),(0,[z0,z669,z2,z3,z4,z85]),(0,[z0,z1,z970,z3,z4,z8])],[(0,[z0,z971,z2,z3,z4,z8]),(0,[z0,z1,z350,z2,z72,z8]),(0,[z0,z1,z112,z3,z4,z197]),(0,[z0,z12,z1,z13,z4,z44])],[(0,[z0,z1,z293,z3,z4,z51]),(0,[z0,z1,z2,z3,z972,z8]),(0,[z0,z973,z2,z3,z4,z8]),(0,[z0,z1,z3,z4,z8,z974]),(0,[z0,z1,z2,z133,z8,z102])]],
   [[(0,[z0,z1,z2,z3,z975,z8]),(0,[z0,z1,z454,z3,z4,z8]),(0,[z0,z1,z27,z3,z79,z8]),(0,[z0,z1,z2,z3,z4,z228]),(0,[z0,z1,z2,z976,z4,z8])],[(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z978,z3,z4,z8]),(0,[z0,z1,z91,z2,z4,z42])],[(0,[z0,z1,z979,z2,z3,z8])],[(0,[z0,z1,z2,z3,z4,z980]),(0,[z0,z1,z46,z3,z4,z107]),(0,[z0,z1,z2,z71,z8,z42]),(0,[z0,z1,z981,z3,z4,z8]),(0,[z0,z1,z409,z2,z3,z8])],[(0,[z0,z1,z982,z3,z4,z8]),(0,[z89,z1,z2,z3,z57,z8]),(0,[z28,z0,z220,z3,z4,z8]),(0,[z0,z1,z170,z2,z3,z8])],[(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z374,z29,z3,z4,z8]),(0,[z0,z984,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z985,z8]),(0,[z0,z1,z986,z3,z4,z8]),(0,[z0,z1,z2,z987,z4,z8]),(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z2,z3,z4,z989,z8])],[(0,[z0,z1,z990,z3,z4,z8]),(0,[z621,z0,z1,z3,z34,z8]),(0,[z0,z97,z1,z13,z4,z8]),(0,[z0,z1,z2,z4,z713,z42])],[(1,[z0,z2,z755,z4,z8]),(0,[z0,z1,z2,z222,z4,z32])]],
   [[(0,[z0,z1,z454,z3,z227,z8]),(0,[z0,z1,z991,z3,z4,z8]),(1,[z0,z1,z3,z779,z8])],[(0,[z0,z1,z2,z158,z26,z8]),(0,[z0,z235,z101,z3,z4,z8]),(0,[z0,z1,z350,z132,z2,z8]),(0,[z0,z992,z2,z3,z4,z8])],[(0,[z114,z1,z737,z3,z4,z8]),(0,[z0,z1,z2,z4,z8,z286])],[(0,[z25,z238,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z993,z8]),(0,[z0,z1,z2,z994,z4,z8]),(0,[z0,z1,z2,z3,z4,z715])],[(0,[z0,z1,z189,z2,z3,z4]),(0,[z0,z1,z2,z3,z995,z8]),(0,[z0,z1,z2,z3,z4,z996]),(0,[z243,z507,z2,z3,z4,z55]),(0,[z0,z1,z23,z2,z4,z107])],[(0,[z684,z1,z2,z3,z4,z55])],[(0,[z0,z1,z2,z158,z4,z51]),(0,[z0,z1,z173,z165,z4,z8]),(0,[z0,z1,z2,z3,z997,z8])],[(0,[z0,z1,z2,z3,z285,z8]),(0,[z111,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z8,z953]),(0,[z0,z538,z1,z3,z34,z8])]],
   [[(0,[z0,z1,z502,z3,z4,z8]),(0,[z0,z1,z2,z3,z285,z32])],[(0,[z0,z1,z2,z4,z8,z998]),(0,[z0,z1,z2,z999,z4,z8]),(0,[z0,z1,z2,z1000,z4,z8])],[(0,[z0,z2,z3,z4,z1001,z8])],[(0,[z0,z1,z1002,z3,z4,z8])],[(1,[z1,z737,z3,z4,z8]),(0,[z0,z1,z2,z216,z4,z107])],[(0,[z616,z0,z220,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z2,z1004,z4,z8]),(0,[z531,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z8,z1005]),(0,[z0,z1,z2,z4,z32,z713])],[(0,[z263,z145,z2,z3,z4,z8]),(0,[z0,z1,z1006,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z1007]),(0,[z0,z104,z1,z500,z216,z8]),(0,[z0,z1,z2,z3,z780,z8])]],
   [[(0,[z0,z1,z502,z3,z227,z8]),(0,[z0,z29,z757,z3,z4,z8]),(0,[z1008,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z11,z534])],[(0,[z61,z1,z2,z146,z4,z8])],[(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z1,z2,z3,z1010,z8]),(0,[z0,z1,z3,z4,z1011,z8]),(0,[z0,z1,z2,z3,z4,z1012]),(0,[z0,z1,z170,z2,z3,z534])],[(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z1,z2,z3,z1014,z8]),(0,[z0,z1,z2,z3,z4,z1015]),(0,[z0,z1,z409,z2,z8,z42]),(0,[z0,z1,z2,z3,z4,z1016]),(0,[z0,z1,z262,z4,z421,z42])],[(0,[z0,z1,z2,z755,z4,z8]),(0,[z0,z1,z2,z3,z8,z1017])],[(0,[z0,z1,z2,z3,z4,z1018]),(0,[z0,z1,z2,z195,z4,z50]),(0,[z0,z1019,z2,z3,z4,z8]),(0,[z0,z235,z2,z165,z4,z8]),(0,[z0,z1,z1020,z2,z4,z8]),(0,[z0,z1,z2,z150,z65,z8])],[(0,[z0,z496,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z1021,z8]),(0,[z0,z1,z2,z3,z500,z8]),(0,[z0,z1,z2,z3,z779,z8])],[(0,[z0,z1,z293,z3,z4,z50]),(0,[z0,z1,z2,z3,z1022,z8]),(1,[z0,z2,z3,z776,z8])]],
   [[],[(0,[z0,z1,z2,z3,z4,z1023]),(0,[z0,z1,z1024,z3,z4,z8]),(0,[z0,z1,z2,z3,z57,z534])],[(0,[z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z1025,z3,z4,z8]),(0,[z0,z1,z2,z513,z4,z42])],[(0,[z0,z1,z2,z1026,z4,z8]),(0,[z0,z1,z737,z3,z4,z8]),(0,[z0,z1,z2,z63,z4,z8]),(0,[z0,z1,z2,z66,z4,z322]),(0,[z0,z1,z350,z2,z57,z8]),(0,[z0,z1,z2,z150,z4,z107]),(0,[z0,z1,z132,z3,z298,z8])],[(0,[z0,z2,z3,z1027,z4,z8]),(0,[z0,z1,z2,z3,z4,z1028]),(0,[z0,z1,z2,z1029,z4,z8]),(0,[z0,z1,z2,z63,z4,z32]),(0,[z243,z1,z2,z3,z4,z811])],[(0,[z0,z1,z1030,z3,z4,z8]),(0,[z0,z1,z1031,z3,z4,z8])],[(0,[z0,z1,z37,z158,z4,z8])],[(0,[z0,z1,z1032,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z176,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z8,z1034]),(0,[z0,z18,z2,z4,z8,z543])]],
   [[(0,[z0,z1,z2,z3,z1035,z8]),(0,[z0,z1,z2,z3,z1036,z8]),(0,[z0,z1,z2,z3,z1037,z8]),(0,[z0,z1,z2,z3,z504,z8]),(0,[z0,z1,z2,z179,z4,z8]),(0,[z0,z97,z1,z23,z4,z8]),(0,[z0,z1,z23,z2,z367,z8])],[(0,[z0,z1,z2,z3,z4,z1038]),(0,[z261,z1,z46,z3,z4,z8]),(0,[z0,z1,z47,z4,z43,z42])],[(0,[z0,z1039,z2,z3,z4,z8]),(0,[z0,z2,z755,z148,z4,z8]),(0,[z0,z670,z2,z3,z72,z8]),(0,[z0,z97,z1,z216,z4,z8]),(0,[z0,z1,z666,z2,z4,z42]),(0,[z0,z1,z23,z2,z8,z93]),(0,[z0,z1040,z1,z3,z4,z8])],[(0,[z100,z0,z1,z3,z34,z8]),(0,[z0,z405,z2,z3,z4,z85])],[(0,[z0,z1,z206,z47,z4,z8]),(0,[z0,z1,z262,z2,z4,z42]),(0,[z0,z1,z1041,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z1042]),(0,[z0,z1,z2,z66,z4,z228]),(0,[z0,z1,z742,z216,z4,z8]),(0,[z0,z1,z262,z2,z4,z713])],[(0,[z0,z1,z2,z158,z4,z50]),(0,[z0,z1,z1043,z3,z4,z8]),(0,[z0,z1,z2,z3,z110,z8]),(0,[z0,z1,z2,z3,z4,z323]),(0,[z0,z2,z755,z3,z4,z8]),(0,[z0,z1,z128,z47,z4,z8]),(0,[z0,z1,z696,z2,z4,z42]),(0,[z0,z1,z1044,z2,z4,z8])],[(0,[z0,z1,z2,z1045,z4,z8])]],
   [[(0,[z0,z1,z2,z1046,z4,z8]),(0,[z243,z1,z173,z3,z4,z55]),(0,[z0,z19,z2,z148,z4,z291])],[(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z1,z3,z4,z712,z44]),(0,[z0,z1,z2,z133,z780,z8])],[(0,[z0,z219,z29,z3,z4,z205]),(0,[z0,z1,z2,z3,z1048,z8]),(0,[z135,z0,z1,z169,z34,z8]),(0,[z0,z1,z3,z4,z779,z8])],[(0,[z0,z1,z2,z3,z1049,z8]),(0,[z0,z1,z350,z2,z4,z1016])],[(0,[z0,z1,z2,z3,z1050,z8]),(0,[z0,z1,z350,z130,z4,z8]),(0,[z0,z1,z2,z1051,z4,z8]),(0,[z1,z2,z3,z816,z57,z8]),(0,[z0,z1,z2,z3,z776,z8])],[(0,[z0,z1052,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z48,z42])],[(0,[z0,z1,z2,z1053,z4,z8])],[(0,[z0,z1,z2,z3,z1054,z8])]],
   [[(0,[z0,z255,z1,z2,z3,z4]),(0,[z243,z0,z97,z1,z3,z4]),(0,[z1055,z1,z2,z3,z4,z8]),(0,[z0,z1056,z2,z3,z4,z8]),(0,[z0,z1,z2,z4,z8,z1057]),(0,[z0,z1,z1058,z2,z4,z8]),(0,[z0,z1,z2,z3,z4,z534])],[(0,[z0,z1,z2,z1059,z4,z8]),(0,[z0,z1,z2,z1060,z4,z8]),(0,[z0,z1,z2,z1061,z4,z8]),(0,[z0,z97,z1,z150,z4,z8])],[(0,[z0,z1,z2,z3,z4,z1062]),(0,[z0,z1,z389,z2,z4,z42]),(0,[z0,z1,z132,z3,z779,z8])],[(0,[z0,z1,z2,z3,z1063,z8]),(0,[z0,z1,z350,z46,z4,z8]),(0,[z0,z104,z1,z409,z2,z8]),(0,[z0,z1064,z2,z3,z4,z8]),(0,[z0,z1,z3,z8,z93,z421])],[(0,[z0,z1,z3,z4,z43,z712])],[(0,[z0,z1,z1065,z3,z4,z8]),(0,[z25,z238,z2,z3,z67,z8]),(0,[z0,z1,z2,z4,z8,z1066]),(0,[z0,z1,z2,z3,z327,z8]),(0,[z0,z1,z2,z3,z4,z1067]),(0,[z1068,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z1069,z8])],[(0,[z0,z235,z173,z3,z4,z8]),(0,[z0,z1,z2,z63,z327,z8]),(0,[z0,z19,z2,z590,z4,z8]),(0,[z0,z104,z1,z13,z4,z8]),(0,[z0,z1,z2,z3,z8,z1070]),(0,[z0,z1,z350,z2,z4,z741])],[(0,[z243,z235,z2,z3,z4,z55]),(0,[z0,z1,z2,z3,z1071,z8])]],
   [[(0,[z0,z1072,z2,z3,z4,z8])],[(0,[z0,z1073,z2,z3,z4,z8]),(0,[z318,z0,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z8,z421]),(0,[z0,z1,z2,z150,z8,z93])],[(0,[z0,z1,z37,z3,z4,z8]),(0,[z230,z1,z46,z3,z4,z8]),(0,[z0,z1,z115,z2,z4,z42])],[(0,[z1074,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z1075,z8]),(0,[z0,z1,z1076,z3,z4,z8])],[(0,[z0,z1,z293,z195,z4,z8]),(0,[z0,z1,z2,z3,z1077,z8]),(0,[z288,z0,z1,z3,z34,z8]),(0,[z0,z250,z2,z3,z22,z8]),(0,[z0,z1,z2,z1078,z4,z8]),(0,[z0,z1,z1079,z3,z4,z8])],[(0,[z0,z1,z2,z3,z8,z1080]),(0,[z0,z1,z2,z3,z285,z42]),(0,[z0,z18,z2,z149,z71,z8]),(0,[z0,z1,z350,z2,z22,z8]),(0,[z1081,z0,z1,z2,z3,z4]),(0,[z0,z1,z184,z2,z3,z534])],[(0,[z0,z1,z3,z4,z8,z712])],[(0,[z0,z1,z2,z3,z4,z1082])]],
   [[(0,[z0,z1,z2,z1083,z4,z8]),(0,[z0,z1,z2,z3,z1084,z8]),(0,[z0,z1,z2,z3,z1085,z8]),(0,[z28,z0,z757,z3,z4,z8])],[(0,[z0,z1,z2,z1086,z4,z8]),(0,[z306,z145,z2,z3,z4,z8]),(0,[z78,z1,z2,z3,z816,z8]),(0,[z0,z1,z2,z3,z1087,z8]),(0,[z0,z1,z2,z3,z71,z8]),(0,[z1088,z1,z2,z3,z4,z8]),(0,[z135,z0,z1,z3,z34,z8])],[(0,[z0,z1,z23,z2,z442,z8]),(0,[z0,z97,z1,z3,z8,z93])],[(1,[z714,z2,z3,z4,z8]),(0,[z0,z1,z1089,z2,z4,z8]),(0,[z631,z0,z1,z3,z34,z8]),(0,[z0,z1,z2,z3,z1090,z8]),(0,[z0,z97,z1,z262,z4,z42])],[(0,[z0,z1,z2,z3,z1091,z8]),(0,[z0,z1,z2,z3,z1092,z8])],[(0,[z0,z1,z1093,z3,z4,z8]),(0,[z0,z1094,z2,z3,z4,z8]),(0,[z0,z1,z409,z2,z66,z8])],[],[(0,[z0,z1,z1095,z2,z3,z8]),(0,[z0,z1,z1096,z3,z4,z8])]],
   [[(0,[z0,z1097,z2,z3,z4,z8]),(0,[z0,z507,z2,z3,z285,z8]),(0,[z176,z1,z2,z3,z4,z811]),(0,[z0,z1,z2,z1098,z4,z8]),(0,[z0,z1,z2,z3,z4,z1099]),(0,[z0,z1,z2,z66,z4,z32])],[(0,[z25,z238,z2,z3,z26,z8]),(0,[z0,z1,z1100,z3,z4,z8]),(0,[z243,z59,z1,z2,z3,z4]),(0,[z243,z0,z1,z2,z13,z4])],[(0,[z0,z1,z101,z3,z4,z8]),(0,[z0,z255,z1,z2,z778,z4]),(0,[z328,z1,z2,z3,z57,z8]),(0,[z243,z1,z2,z165,z4,z55])],[(0,[z1101,z0,z1,z3,z4,z8]),(0,[z0,z1,z2,z63,z285,z8]),(0,[z0,z1,z967,z2,z8,z286]),(0,[z0,z1,z2,z207,z4,z42])],[(0,[z0,z1,z2,z3,z67,z8]),(0,[z0,z1,z2,z1102,z4,z8])],[(0,[z0,z539,z2,z149,z4,z8]),(0,[z0,z1,z23,z2,z410,z8])],[(0,[z25,z238,z2,z3,z4,z51]),(0,[z201,z1,z375,z3,z57,z8]),(0,[z1,z2,z3,z4,z816,z8]),(0,[z0,z1,z1103,z3,z4,z8])],[(0,[z0,z1,z2,z3,z1104,z8]),(0,[z0,z1105,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1106]),(0,[z201,z1,z2,z3,z57,z8]),(0,[z0,z1,z2,z3,z4,z1107])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 548) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 548).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1072)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [548, 524] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 168).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 168).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [168, 88] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_40529

theorem PEqualNP.Outside.L_meta_40529 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276658336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276658336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40529.solve