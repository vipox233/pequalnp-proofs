import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36348

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01000045413163c0#64 ++ 0x001000045413163c#64 ++ 0xbec520cfc37367cf#64 ++ 0x7bec520cfc37367c#64 : BitVec 256),
   (0x1200431304148552#64 ++ 0x0120043130414855#64 ++ 0x7dcac7330c9c87fe#64 ++ 0xf7dcac7330c9c87f#64 : BitVec 256),
   (0x2413082c10e028a4#64 ++ 0x52413082c10e028a#64 ++ 0xebb3183c30e0f8fd#64 ++ 0xeebb3183c30e0f8f#64 : BitVec 256),
   (0x582c15c02f00d608#64 ++ 0x8582c15c02f00d60#64 ++ 0xe7bc1fc03f00ff0b#64 ++ 0xde7bc1fc03f00ff0#64 : BitVec 256),
   (0x603fa0003aca0000#64 ++ 0xe603fa0003aca000#64 ++ 0x1fffe0003fff0007#64 ++ 0xc1fffe0003fff000#64 : BitVec 256),
   (0x803ffeba80000000#64 ++ 0xf803ffeba8000000#64 ++ 0xffbfffffc0000000#64 ++ 0x3ffbfffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0100004441216280 0x0010000444121628 0x0000000003636001 0x0000000000363600

def z1 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec520cfc37367cf 0x7bec520cfc37367c

def z2 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcac7330c9c87fe 0xf7dcac7330c9c87f

def z3 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb3183c30e0f8fd 0xeebb3183c30e0f8f

def z4 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fc03f00ff0b 0xde7bc1fc03f00ff0

def z5 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z6 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z7 : W := mkw 0x603fb4803aca0000 0xe603fb4803aca000 0xffffffc03fff0007 0xdffffffc03fff000

def z8 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x144ce0000f1f0002 0x0144ce0000f1f000

def z9 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x004000003fff0007 0xc004000003fff000

def z10 : W := mkw 0x6413082c3aea28a4 0x56413082c3aea28a 0xebf3183c3ffff8ff 0xeebf3183c3ffff8f

def z11 : W := mkw 0x582c15c42f20f688 0x8582c15c42f20f68 0xefbd1fcc3f60ffcf 0xfefbd1fcc3f60ffc

def z12 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x013ac0003c8c0000 0x8013ac0003c8c000

def z13 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffffffffffff0007 0xfffffffffffff000

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe8520cfc0000000 0x3be8520cfc000000

def z15 : W := mkw 0x813ffeffc13163c0 0xf813ffeffc13163c 0xffffffffc37367cf 0x7ffffffffc37367c

def z16 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0xf7bcffc3c0000000 0x1f7bcffc3c000000

def z17 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe0001fc00000ff08 0x1e0001fc00000ff0

def z18 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x0803003c00e000f4 0x20803003c00e000f

def z19 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0xe7bc18003f00f80b 0xce7bc18003f00f80

def z20 : W := mkw 0x7c13096c3fe0feac 0x57c13096c3fe0fea 0xebb3183c3fe0ffff 0xeebb3183c3fe0fff

def z21 : W := mkw 0x2513086c51e16aa4 0x52513086c51e16aa 0xebb738fcf3e3f8fd 0xeebb738fcf3e3f8f

def z22 : W := mkw 0xd83fffbaae009408 0xfd83fffbaae00940 0xffbffffffc009800 0xbffbffffffc00980

def z23 : W := mkw 0x0200421300140152 0x0020042130014015 0x3cc2c033009c07fe 0x73cc2c033009c07f

def z24 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe0001fffc0000000 0x3e0001fffc000000

def z25 : W := mkw 0x580001402f00d608 0x0580001402f00d60 0xa68400c03f00ff0b 0xda68400c03f00ff0

def z26 : W := mkw 0x1200431304148552 0x0120043130414855 0x1448c7030c1c0702 0x11448c7030c1c070

def z27 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x8231180c30607801 0x08231180c3060780

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3b018003000f809 0xce3b018003000f80

def z29 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbffffff000f809 0xfffbffffff000f80

def z30 : W := mkw 0x613fa0457bfb63c0 0xe613fa0457bfb63c 0xbfffe0cfffff67cf 0xfbfffe0cfffff67c

def z31 : W := mkw 0x922cf79384148552 0xa922cf7938414855 0x7dcee7f3cc9c87fe 0xf7dcee7f3cc9c87f

def z32 : W := mkw 0x403fa0002a000000 0xe403fa0002a00000 0x1fbfe0003f000003 0xc1fbfe0003f00000

def z33 : W := mkw 0x0000004001004200 0x0000000400100420 0xa68400c00300670b 0x5a68400c00300670

def z34 : W := mkw 0x592c15c56f31f7c8 0x8592c15c56f31f7c 0xfffd3fcfff73ffcf 0xffffd3fcfff73ffc

def z35 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x8231180c30e0f8fd 0xc8231180c30e0f8f

def z36 : W := mkw 0x0000000100100140 0x0000000010010014 0x3cc00003001007ce 0x73cc00003001007c

def z37 : W := mkw 0x0000421200000000 0x0000042120000000 0xff8fe7ffc0000000 0x3ff8fe7ffc000000

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x010ac0000c8c0000 0x8010ac0000c8c000

def z39 : W := mkw 0x002c14c001004200 0x8002c14c00100420 0xe7bc1fc00300670b 0x5e7bc1fc00300670

def z40 : W := mkw 0x1000010004008400 0x0100001000400840 0x658807000c00870a 0xd658807000c00870

def z41 : W := mkw 0x1200431304148552 0x0120043130414855 0x1dcac7030c9c0706 0xd1dcac7030c9c070

def z42 : W := mkw 0x0000421200000000 0x0000042120000000 0x7d8ac733008080fc 0xf7d8ac733008080f

def z43 : W := mkw 0xa43ffebe90e028a4 0xfa43ffebe90e028a 0xffbfffffc0e000f4 0x3ffbfffffc0e000f

def z44 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x4933183c30e098f4 0xa4933183c30e098f

def z45 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfff7383c33f3f8ff 0xefff7383c33f3f8f

def z46 : W := mkw 0x5a2c57d32f14d75a 0x85a2c57d32f14d75 0x144cc7c30f1c0702 0x1144cc7c30f1c070

def z47 : W := mkw 0x5a2c57d32f14d75a 0x85a2c57d32f14d75 0xfffedff33f9cffff 0xffffedff33f9cfff

def z48 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfffbd83c3cfcf8ff 0xefffbd83c3cfcf8f

def z49 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x040c00000f000002 0x0040c00000f00000

def z50 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xffbffffff0e00005 0xfffbffffff0e0000

def z51 : W := mkw 0x8013a82880000000 0x78013a8288000000 0x0001200cc0000000 0x00001200cc000000

def z52 : W := mkw 0x1000010104108540 0x0100001010410854 0x7dc807030c1087ce 0xf7dc807030c1087c

def z53 : W := mkw 0x0000421300100140 0x0000042130010014 0x7dcac733001007ce 0x77dcac733001007c

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dcac0000c9c0006 0xc1dcac0000c9c000

def z55 : W := mkw 0x1200431304148552 0x0120043130414855 0x60000733000087f8 0x360000733000087f

def z56 : W := mkw 0x01000045413163c0 0x001000045413163c 0x1c4520cfc37307c6 0x31c4520cfc37307c

def z57 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xfffff8003ffff80f 0xcfffff8003ffff80

def z58 : W := mkw 0x16004b3f0434adf6 0x116004b3f0434adf 0xfdcadf3f0c9cfffe 0xffdcadf3f0c9cfff

def z59 : W := mkw 0x1200431304148552 0x0120043130414855 0x69820733008087fc 0xf69820733008087f

def z60 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0xffcfe7ffcfffe7ff 0xfffcfe7ffcfffe7f

def z61 : W := mkw 0x5a2c57d22f04d61a 0x85a2c57d22f04d61 0xe7bedff03f8cff3b 0xde7bedff03f8cff3

def z62 : W := mkw 0x2413082810c00824 0x52413082810c0082 0x4132183030809830 0x8413218303080983

def z63 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0x5ffff8303fff9837 0xc5ffff8303fff983

def z64 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xfffd3fc03f73ff0f 0xdfffd3fc03f73ff0

def z65 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0x823418c033007801 0x0823418c03300780

def z66 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x040c07c00f000702 0x1040c07c00f00070

def z67 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x0235200000000000 0x0023520000000000

def z68 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0xbe8de7cfc0000000 0x3be8de7cfc000000

def z69 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x0235200033630001 0x0023520003363000

def z70 : W := mkw 0x1200431204048412 0x0120043120404841 0x410ac7300c8c8030 0x8410ac7300c8c803

def z71 : W := mkw 0x923fffbb84148552 0xf923fffbb8414855 0xffffffffcc9c87fe 0xfffffffffcc9c87f

def z72 : W := mkw 0x0100004141114340 0x0010000414111434 0x144420c3c3130702 0x1144420c3c313070

def z73 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x07bc00003f000003 0xc07bc00003f00000

def z74 : W := mkw 0x2513082d50f129e4 0x52513082d50f129e 0x1843203fc0f300f4 0x21843203fc0f300f

def z75 : W := mkw 0xb63fffbf94f4adf6 0xfb63fffbf94f4adf 0xfffffffffcfcffff 0xffffffffffcfcfff

def z76 : W := mkw 0x723fe3133ede8552 0xe723fe3133ede855 0x7fffe7333fff87ff 0xf7fffe7333fff87f

def z77 : W := mkw 0x1200010104148552 0x0120001010414855 0x004000000c9c87fe 0xc004000000c9c87f

def z78 : W := mkw 0xe03fbca8baca0000 0xfe03fbca8baca000 0x9ffff8ccffff0007 0xc9ffff8ccffff000

def z79 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0bb3000030e00005 0xc0bb3000030e0000

def z80 : W := mkw 0x643fa82c3aea28a4 0xf643fa82c3aea28a 0xfffff83c3ffff8ff 0xefffff83c3ffff8f

def z81 : W := mkw 0x783fb5c03fcad608 0xe783fb5c03fcad60 0xffffffc03fffff0f 0xdffffffc03fffff0

def z82 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0x0000000030e0f8fd 0xc0000000030e0f8f

def z83 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0x140ce7c3c0000000 0x1140ce7c3c000000

def z84 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1843e00000ff0004 0x01843e00000ff000

def z85 : W := mkw 0x0000421200000000 0x0000042120000000 0x7dcac7330c9c0006 0xf7dcac7330c9c000

def z86 : W := mkw 0x0000421200000000 0x0000042120000000 0x7d8ac73300000000 0x37d8ac7330000000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0xa280000000006009 0x4a28000000000600

def z88 : W := mkw 0x002c000000000000 0x8002c00000000000 0x07bc000000000000 0x007bc00000000000

def z89 : W := mkw 0x2413a82c10ea28a4 0x72413a82c10ea28a 0xfbf3f83c30fff8fd 0xefbf3f83c30fff8f

def z90 : W := mkw 0x802c5eba80000000 0x9802c5eba8000000 0xe7bc1fffc0000000 0x3e7bc1fffc000000

def z91 : W := mkw 0x002c148000000000 0x8002c14800000000 0xe7bc1fc000000000 0x1e7bc1fc00000000

def z92 : W := mkw 0xd83ffffaaf00d608 0xfd83ffffaaf00d60 0xffbfffffcf000702 0x3ffbfffffcf00070

def z93 : W := mkw 0x2113a04551fb63c0 0x62113a04551fb63c 0xbec7e0cfc3ff67cf 0x7bec7e0cfc3ff67c

def z94 : W := mkw 0x0000000400202080 0x0000000040020208 0xaa81000c006060cd 0x6aa81000c006060c

def z95 : W := mkw 0x2513086d51f16be4 0x52513086d51f16be 0xfff738fff3f3ffff 0xffff738fff3f3fff

def z96 : W := mkw 0x01000005403121c0 0x001000005403121c 0x1841200fc07300c4 0x21841200fc07300c

def z97 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0x41381f003c009800 0x841381f003c00980

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000008080fc 0xc00000000008080f

def z99 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x553efff3c0000000 0x1553efff3c000000

def z100 : W := mkw 0x1200431304148552 0x0120043130414855 0xfffadf333c9cffff 0xffffadf333c9cfff

def z101 : W := mkw 0x003f1ca800000000 0xd003f1ca80000000 0xefbf1ffc00000000 0x3efbf1ffc0000000

def z102 : W := mkw 0x01000005403121c0 0x001000005403121c 0xbac1200fc07360cd 0x6bac1200fc07360c

def z103 : W := mkw 0x01000045413163c0 0x001000045413163c 0xffc720ffc3f3e7ff 0xfffc720ffc3f3e7f

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x69820030008080fc 0xe69820030008080f

def z105 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xefbe1ff03f80ffff 0xfefbe1ff03f80fff

def z106 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x8a33183c30e078f5 0x28a33183c30e078f

def z107 : W := mkw 0x01000045413163c0 0x001000045413163c 0x00400000037367cf 0x400400000037367c

def z108 : W := mkw 0x580001402f00d608 0x0580001402f00d60 0x000000003f00ff0b 0xc000000003f00ff0

def z109 : W := mkw 0x36134b3f14f4adf6 0x536134b3f14f4adf 0xfffbdf3f3cfcffff 0xffffbdf3f3cfcfff

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ec5200003730007 0x41ec520000373000

def z111 : W := mkw 0x1200431304148552 0x0120043130414855 0x414ac7300c9c87fe 0xc414ac7300c9c87f

def z112 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x0234000033000001 0x0023400003300000

def z113 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0x823538ccc0000000 0x0823538ccc000000

def z114 : W := mkw 0x7c3f1dec3fe0feac 0xd7c3f1dec3fe0fea 0xefbf1ffc3fe0ffff 0xfefbf1ffc3fe0fff

def z115 : W := mkw 0xa03ffeba90ca0000 0xfa03ffeba90ca000 0xffffffffc0ff0004 0x3ffffffffc0ff000

def z116 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fbfe00000000000 0x01fbfe0000000000

def z117 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0x0008c70000000000 0x00008c7000000000

def z118 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbffffff3630001 0x3ffbffffff363000

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0xebb218303080f8fd 0xeebb218303080f8f

def z120 : W := mkw 0x783f15c03fc0d608 0xc783f15c03fc0d60 0xefbf1fc03fe0ff0f 0xdefbf1fc03fe0ff0

def z121 : W := mkw 0x002ca00000000000 0xa002ca0000000000 0x140ce00000000000 0x0140ce0000000000

def z122 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xc33c1fc03f00f801 0x8c33c1fc03f00f80

def z123 : W := mkw 0x1200431304148552 0x0120043130414855 0x610ac7330c8c87f8 0xb610ac7330c8c87f

def z124 : W := mkw 0x1200431304148552 0x0120043130414855 0x7448c7330c1c87fa 0x37448c7330c1c87f

def z125 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb3183c00000000 0x2ebb3183c0000000

def z126 : W := mkw 0x7c3f1dac3ee0bcac 0xd7c3f1dac3ee0bca 0xebbb1f3c3ce0f8fd 0xeebbb1f3c3ce0f8f

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x004000000c9c0006 0xc004000000c9c000

def z128 : W := mkw 0x643fa82c3aea28a4 0xf643fa82c3aea28a 0x8235380c33637801 0x08235380c3363780

def z129 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x863c1fc03f007f03 0x1863c1fc03f007f0

def z130 : W := mkw 0x0000000100100140 0x0000000010010014 0xbec520cfc01007ce 0x7bec520cfc01007c

def z131 : W := mkw 0x0000082800000000 0x1000008280000000 0xe000183c00000000 0x2e000183c0000000

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000cfc0000000 0x3a00000cfc000000

def z133 : W := mkw 0x412ca0456b3b63c0 0xa412ca0456b3b63c 0xbecde0cfcf7f67cf 0x7becde0cfcf7f67c

def z134 : W := mkw 0x812cf6d7c13163c0 0xa812cf6d7c13163c 0xbecde7cfc37367cf 0x7becde7cfc37367c

def z135 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xc333183c30e0f831 0x8c333183c30e0f83

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fcfe0000fff0007 0xc1fcfe0000fff000

def z137 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbfcfe0cfcfff67cf 0xfbfcfe0cfcfff67c

def z138 : W := mkw 0x0100004441216280 0x0010000444121628 0x820520ccc3636001 0x0820520ccc363600

def z139 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x593bff3fc0000000 0x2593bff3fc000000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e85200000000000 0x01e8520000000000

def z141 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x9a37f8ffc0000000 0x29a37f8ffc000000

def z142 : W := mkw 0x1a0057d30514d75a 0x01a0057d30514d75 0xe0001ff30000fff8 0x3e0001ff30000fff

def z143 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe803183c00e0f8fc 0x2e803183c00e0f8f

def z144 : W := mkw 0x0100004141114340 0x0010000414111434 0xb6c420c3c313670b 0x5b6c420c3c313670

def z145 : W := mkw 0x6013a0003aca0000 0x66013a0003aca000 0x1843e0003fff0007 0xc1843e0003fff000

def z146 : W := mkw 0x582c01402f00d608 0x8582c01402f00d60 0x07bc00003f00ff0b 0xc07bc00003f00ff0

def z147 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0x7d8ee7f3c0000000 0x37d8ee7f3c000000

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x0205200003630001 0x0020520000363000

def z149 : W := mkw 0x26134a3f10f429f6 0x526134a3f10f429f 0x1843c03f00fc00f4 0x21843c03f00fc00f

def z150 : W := mkw 0x1200431304148552 0x0120043130414855 0x1c4ac7330c9c07f6 0x31c4ac7330c9c07f

def z151 : W := mkw 0x1000010004008400 0x0100001000400840 0x6d8a07300c8087fe 0xf6d8a07300c8087f

def z152 : W := mkw 0x8013ea3a80000000 0x78013ea3a8000000 0x1803e03fc0000000 0x21803e03fc000000

def z153 : W := mkw 0xa43ffebe90e028a4 0xfa43ffebe90e028a 0xffbffffff0e0f8fd 0xfffbffffff0e0f8f

def z154 : W := mkw 0xf23fffbbbede8552 0xff23fffbbbede855 0xffffffffffff87ff 0xfffffffffffff87f

def z155 : W := mkw 0x1000010004008400 0x0100001000400840 0x6000070000008708 0x1600007000000870

def z156 : W := mkw 0x0200421300140152 0x0020042130014015 0x1842c033009c00f4 0x21842c033009c00f

def z157 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe2353fffc0000000 0x3e2353fffc000000

def z158 : W := mkw 0x522ce3132e1e8552 0xa522ce3132e1e855 0x7dcee7330f9f87fe 0xf7dcee7330f9f87f

def z159 : W := mkw 0xe03fea3abaca0000 0xfe03fea3abaca000 0x1fffe03fffff0007 0xe1fffe03fffff000

def z160 : W := mkw 0x933fffffc535e7d2 0xf933fffffc535e7d 0xffffffffcfffe7ff 0xfffffffffcfffe7f

def z161 : W := mkw 0x580001402f00d608 0x0580001402f00d60 0x658807003f00ff0b 0xd658807003f00ff0

def z162 : W := mkw 0x8000e21280000000 0x28000e2128000000 0x1000e003c0000000 0x01000e003c000000

def z163 : W := mkw 0xa53ffeffd1f16be4 0xfa53ffeffd1f16be 0xfffffffff3f3ffff 0xffffffffff3f3fff

def z164 : W := mkw 0xe03ff692baca0000 0xee03ff692baca000 0x1fffe7c3ffff0007 0xd1fffe7c3ffff000

def z165 : W := mkw 0x653fa86d7bfb6be4 0xf653fa86d7bfb6be 0xfffff8ffffffffff 0xffffff8fffffffff

def z166 : W := mkw 0x923fffbb84148552 0xf923fffbb8414855 0xffbfffffc00087f8 0x3ffbfffffc00087f

def z167 : W := mkw 0x2513086d51f16be4 0x52513086d51f16be 0xbec720ffc3f367ff 0x7bec720ffc3f367f

def z168 : W := mkw 0x0013082800000000 0x5001308280000000 0xffb738ffc0000000 0x3ffb738ffc000000

def z169 : W := mkw 0x5a2c57932e14955a 0x85a2c57932e14955 0x7dfadf333c9c9ffe 0xf7dfadf333c9c9ff

def z170 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x017ac0003fff0007 0xc017ac0003fff000

def z171 : W := mkw 0x0100004141114340 0x0010000414111434 0x3cc420c3c31307ce 0x73cc420c3c31307c

def z172 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0x8000180c00007800 0x08000180c0000780

def z173 : W := mkw 0x36134b3f14f4adf6 0x536134b3f14f4adf 0xebb31f3f30e0fffd 0xfebb31f3f30e0fff

def z174 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xfd8adfffc0000000 0x3fd8adfffc000000

def z175 : W := mkw 0x582c57d22f00d608 0x8582c57d22f00d60 0xffbedff33f00ff0b 0xfffbedff33f00ff0

def z176 : W := mkw 0x1200431204048412 0x0120043120404841 0x0008c7000c0c0000 0x00008c7000c0c000

def z177 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x197be0003cff0004 0x8197be0003cff000

def z178 : W := mkw 0xfc3ffffebfe0feac 0xffc3ffffebfe0fea 0xffbfffffffe0ffff 0xfffbfffffffe0fff

def z179 : W := mkw 0x400000002a000000 0x0400000002a00000 0x000000003f000003 0xc000000003f00000

def z180 : W := mkw 0x0100004141114340 0x0010000414111434 0x000000c3c0000700 0x1000000c3c000070

def z181 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xe000183c0000f8f8 0x2e000183c0000f8f

def z182 : W := mkw 0x590001456f31f7c8 0x0590001456f31f7c 0x004000003f73ffcf 0xc004000003f73ffc

def z183 : W := mkw 0xe13ffefffbfb63c0 0xfe13ffefffbfb63c 0xffffffffffff67cf 0xfffffffffffff67c

def z184 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x413adf3000000000 0x0413adf300000000

def z185 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc08080fc 0xfffbfffffc08080f

def z186 : W := mkw 0xa413ea3e90e028a4 0x7a413ea3e90e028a 0xfbb3f83ff0e0f8fd 0xefbb3f83ff0e0f8f

def z187 : W := mkw 0x8013feba80000000 0x78013feba8000000 0xf803ffffc0000000 0x3f803ffffc000000

def z188 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0xe3b81f003c00f809 0xce3b81f003c00f80

def z189 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xfe853fffc0000000 0x3fe853fffc000000

def z190 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x144ce0003fff0007 0xc144ce0003fff000

def z191 : W := mkw 0x720043133ede8552 0x0720043133ede855 0x7dcac7333fff87ff 0xf7dcac7333fff87f

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x4102003000808030 0x8410200300080803

def z193 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0xffbffffff0809830 0xbffbffffff080983

def z194 : W := mkw 0x0000000000000000 0x0000000000000000 0x1841200000730004 0x0184120000073000

def z195 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x7dbadf3300000000 0x37dbadf330000000

def z196 : W := mkw 0x1800158004009408 0x0180015800400940 0x40001f0000009800 0x040001f000000980

def z197 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe5881fc00c00ff0a 0xde5881fc00c00ff0

def z198 : W := mkw 0x04000004002028a4 0x004000004002028a 0x000000000000f8f8 0x0000000000000f8f

def z199 : W := mkw 0x2500004551f16be4 0x02500004551f16be 0xbec520cff3f3ffff 0xfbec520cff3f3fff

def z200 : W := mkw 0x8113ea3fc03121c0 0x78113ea3fc03121c 0x1843e03fc07300c4 0x21843e03fc07300c

def z201 : W := mkw 0x01000045413163c0 0x001000045413163c 0xfff538cff373ffcf 0xffff538cff373ffc

def z202 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0xf40cffffc0000000 0x3f40cffffc000000

def z203 : W := mkw 0x7c2c15c43fe0feac 0x87c2c15c43fe0fea 0xe7bc1fc03fe0ffff 0xde7bc1fc03fe0fff

def z204 : W := mkw 0x733fe3577fffe7d2 0xe733fe3577fffe7d 0xffffe7ffffffe7ff 0xfffffe7ffffffe7f

def z205 : W := mkw 0x2513086d51f16be4 0x52513086d51f16be 0xbef538cff3737fcf 0x7bef538cff3737fc

def z206 : W := mkw 0x0000148000000000 0x0000014800000000 0xe0001fc000000000 0x1e0001fc00000000

def z207 : W := mkw 0x0000000400202080 0x0000000040020208 0x8201000c00606001 0x08201000c0060600

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x1842c000009c0004 0x01842c000009c000

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0x1448c0000c1c0002 0x01448c0000c1c000

def z210 : W := mkw 0x80135eba80000000 0x580135eba8000000 0xebb31fffc0000000 0x3ebb31fffc000000

def z211 : W := mkw 0x2013082810c00000 0x52013082810c0000 0xebb3183c30e00005 0xeebb3183c30e0000

def z212 : W := mkw 0x803ffebb80100140 0xf803ffebb8010014 0xffffffffc01007ce 0x7ffffffffc01007c

def z213 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x41381f003f00ff0b 0xc41381f003f00ff0

def z214 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x7fffe0303fff80ff 0xe7fffe0303fff80f

def z215 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe3b1180c3060f809 0xce3b1180c3060f80

def z216 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0x413ad8303c8c9830 0x8413ad8303c8c983

def z217 : W := mkw 0x1200431304148552 0x0120043130414855 0x604007330c9c87fe 0xf604007330c9c87f

def z218 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x0002c000008c0000 0x00002c000008c000

def z219 : W := mkw 0x923fffbb84148552 0xf923fffbb8414855 0x7dfadf330c9c87fe 0xf7dfadf330c9c87f

def z220 : W := mkw 0x923fffbb84148552 0xf923fffbb8414855 0xffffffffcc1c0702 0x3ffffffffcc1c070

def z221 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffcc9c0006 0xfffffffffcc9c000

def z222 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x6bb3003030e080fd 0xe6bb3003030e080f

def z223 : W := mkw 0x643fa82c3aea28a4 0xf643fa82c3aea28a 0x1fffe03c3fff00f7 0xe1fffe03c3fff00f

def z224 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x0030000030000000 0x0003000003000000

def z225 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x1ecde0000f7f0007 0x41ecde0000f7f000

def z226 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa00000cfc00067c8 0x3a00000cfc00067c

def z227 : W := mkw 0x24134a3e10e028a4 0x524134a3e10e028a 0xffbbdf3f30e0f8fd 0xfffbbdf3f30e0f8f

def z228 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0x000007c000000700 0x1000007c00000070

def z229 : W := mkw 0xf83ffffabfcad608 0xff83ffffabfcad60 0xffffffffffffff0f 0xfffffffffffffff0

def z230 : W := mkw 0x36134b3b14d48d76 0x536134b3b14d48d7 0x7dfadf333c9c9ffe 0xf7dfadf333c9c9ff

def z231 : W := mkw 0x0013082c00202080 0x50013082c0020208 0xebb3183c006060cd 0x6ebb3183c006060c

def z232 : W := mkw 0x763feb3f3efeadf6 0xf763feb3f3efeadf 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z233 : W := mkw 0xd83fbde8af00d608 0xfd83fbde8af00d60 0xe7bd3fccff00ff0b 0xde7bd3fccff00ff0

def z234 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb3183c3000f809 0xeebb3183c3000f80

def z235 : W := mkw 0x2413a82c10ea28a4 0x72413a82c10ea28a 0x1843e03c00ff00f4 0x21843e03c00ff00f

def z236 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x040c07c03f00ff0b 0xd040c07c03f00ff0

def z237 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0xe00007ffc000e7f8 0x3e00007ffc000e7f

def z238 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe2341fc03300ff09 0x1e2341fc03300ff0

def z239 : W := mkw 0x402c14802a000000 0x8402c14802a00000 0xe7bc1fc03f000003 0xde7bc1fc03f00000

def z240 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x033fe0003fef0001 0x8033fe0003fef000

def z241 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0x004000000fffe7ff 0xc004000000fffe7f

def z242 : W := mkw 0x1200431304148552 0x0120043130414855 0xffcfe7ffcc9c87fe 0xfffcfe7ffcc9c87f

def z243 : W := mkw 0x3213e31314de8552 0x63213e31314de855 0x7dcbe7330cff87fe 0xf7dcbe7330cff87f

def z244 : W := mkw 0x2413086c11e06aa4 0x52413086c11e06aa 0xefb718fc33e0ffff 0xfefb718fc33e0fff

def z245 : W := mkw 0x1200431204048412 0x0120043120404841 0x5dcac7300c9c8036 0xc5dcac7300c9c803

def z246 : W := mkw 0x1200010104148552 0x0120001010414855 0x69c200300c9c87fe 0xe69c200300c9c87f

def z247 : W := mkw 0x2413082810c00824 0x52413082810c0082 0xe3b218303080f839 0xce3b218303080f83

def z248 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffc3730007 0x7ffffffffc373000

def z249 : W := mkw 0x0000a000000a0000 0x20000a000000a000 0x1040e000001f0000 0x01040e000001f000

def z250 : W := mkw 0x2400000010c00824 0x02400000010c0082 0x0000000030809830 0x8000000003080983

def z251 : W := mkw 0xd93fffffef31f7c8 0xfd93fffffef31f7c 0xffffffffff73ffcf 0xfffffffffff73ffc

def z252 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe00003730007 0x41fffe0000373000

def z253 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1c4fe0000fff0006 0x01c4fe0000fff000

def z254 : W := mkw 0x1200431304148552 0x0120043130414855 0x75c8c7030c1c870a 0xd75c8c7030c1c870

def z255 : W := mkw 0x683fb4c03bca5208 0xe683fb4c03bca520 0x823538c033637801 0x0823538c03363780

def z256 : W := mkw 0x01000045413163c0 0x001000045413163c 0x1ec52000037367cf 0x41ec52000037367c

def z257 : W := mkw 0x5a0001412f14d75a 0x05a0001412f14d75 0x004000003f9cffff 0xc004000003f9cfff

def z258 : W := mkw 0x723fe3123ece8412 0xe723fe3123ece841 0x413ac7303c8c8030 0x8413ac7303c8c803

def z259 : W := mkw 0x003fe21200000000 0xe003fe2120000000 0x7fbfe73300000000 0x37fbfe7330000000

def z260 : W := mkw 0x01000045413163c0 0x001000045413163c 0xaa8100cfc06067cd 0x7aa8100cfc06067c

def z261 : W := mkw 0x2413082d10f029e4 0x52413082d10f029e 0xfff3183f30f0ffff 0xffff3183f30f0fff

def z262 : W := mkw 0xc02cf692aa0a0000 0xac02cf692aa0a000 0x144ce7c3cf1f0002 0x1144ce7c3cf1f000

def z263 : W := mkw 0x01000045413163c0 0x001000045413163c 0x964520cfc3736703 0x1964520cfc373670

def z264 : W := mkw 0x0000000400202080 0x0000000040020208 0xeb83003c00e0e0fd 0xeeb83003c00e0e0f

def z265 : W := mkw 0x0000000400202080 0x0000000040020208 0xa000000c000060c8 0x2a000000c000060c

def z266 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xffb738fff0e0f8fd 0xfffb738fff0e0f8f

def z267 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb3183c30607801 0x2ebb3183c3060780

def z268 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0x0000000000e000f4 0x00000000000e000f

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x7dcac0300c9c80fe 0xe7dcac0300c9c80f

def z270 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xe3b0183c3000f8f9 0xee3b0183c3000f8f

def z271 : W := mkw 0xd83ffffaaf00d608 0xfd83ffffaaf00d60 0xe7bedff03f00ff0b 0xde7bedff03f00ff0

def z272 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe231183c3060f8f9 0x2e231183c3060f8f

def z273 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x027520003fff0007 0xc027520003fff000

def z274 : W := mkw 0x0100004441216280 0x0010000444121628 0xbe8520cfc3636001 0x3be8520cfc363600

def z275 : W := mkw 0x522c43132e148552 0x8522c43132e14855 0x7ffec7333f9c87ff 0xf7ffec7333f9c87f

def z276 : W := mkw 0xe03fbca8baca0000 0xfe03fbca8baca000 0x823538ccf3630001 0x0823538ccf363000

def z277 : W := mkw 0x8000569280000000 0x0800056928000000 0x000007c3c0000000 0x1000007c3c000000

def z278 : W := mkw 0x603fa0043aea2080 0xe603fa0043aea208 0xbfffe00c3fff60cf 0xebfffe00c3fff60c

def z279 : W := mkw 0x0000004001004200 0x0000000400100420 0x040400c003000702 0x1040400c00300070

def z280 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0231000030600001 0x0023100003060000

def z281 : W := mkw 0x01004257413163c0 0x001004257413163c 0xffcfe7ffc37367cf 0x7ffcfe7ffc37367c

def z282 : W := mkw 0x180001400500d608 0x0180001400500d60 0x000000000000ff08 0x0000000000000ff0

def z283 : W := mkw 0xd83ffffaaf00d608 0xfd83ffffaaf00d60 0xffbfffffff00ff0b 0xfffbfffffff00ff0

def z284 : W := mkw 0x0000000100100140 0x0000000010010014 0x3dcac0030c9c07ce 0xf3dcac0030c9c07c

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x0982000000800004 0xc098200000080000

def z286 : W := mkw 0x923fffba84048412 0xf923fffba8404841 0x413adf300c8c8030 0x8413adf300c8c803

def z287 : W := mkw 0xe43ffebebaea28a4 0xfe43ffebebaea28a 0xfffffffffffff8ff 0xffffffffffffff8f

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x058800000c000002 0xc058800000c00000

def z289 : W := mkw 0x002c148000000000 0x8002c14800000000 0x040c07c000000000 0x1040c07c00000000

def z290 : W := mkw 0x0500086d41316be4 0x10500086d41316be 0xfec538ffc373ffff 0x7fec538ffc373fff

def z291 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0x413adf3030809830 0x8413adf303080983

def z292 : W := mkw 0x80005eba80000000 0x180005eba8000000 0x40001f3000000000 0x040001f300000000

def z293 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xffbd3fcfff00ff0b 0xfffbd3fcfff00ff0

def z294 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0x7dcac7330fffe7ff 0xf7dcac7330fffe7f

def z295 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe3b01fc03000ff09 0xde3b01fc03000ff0

def z296 : W := mkw 0x813ffefbc1114340 0xf813ffefbc111434 0xffffffffc3130702 0x3ffffffffc313070

def z297 : W := mkw 0x1200431304148552 0x0120043130414855 0x7842c733009c87fc 0x37842c733009c87f

def z298 : W := mkw 0x1200431304148552 0x0120043130414855 0x1448c7030c9c87fe 0xd1448c7030c9c87f

def z299 : W := mkw 0x2213e21310de0152 0x62213e21310de015 0x1843e03300ff00f4 0x21843e03300ff00f

def z300 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x1dcac0003fff0007 0xc1dcac0003fff000

def z301 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0x413adf303c8c0000 0x8413adf303c8c000

def z302 : W := mkw 0x01000045413163c0 0x001000045413163c 0x00000000000067c8 0x000000000000067c

def z303 : W := mkw 0x26134a3f10f429f6 0x526134a3f10f429f 0xfbf3d83f30fcf8fd 0xefbf3d83f30fcf8f

def z304 : W := mkw 0x0200421300140152 0x0020042130014015 0x00000033000000f0 0x200000033000000f

def z305 : W := mkw 0x480000402b005208 0x0480000402b00520 0x0000000033007801 0x0000000003300780

def z306 : W := mkw 0x3600431714f4adf6 0x03600431714f4adf 0x7dcac7333cfcffff 0xf7dcac7333cfcfff

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z308 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x4132183030e0f8fd 0xc4132183030e0f8f

def z309 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x167de0003f7f0003 0x0167de0003f7f000

def z310 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x1c0fe7ffc0000000 0x31c0fe7ffc000000

def z311 : W := mkw 0x01000045413163c0 0x001000045413163c 0xb44420cfc31367ca 0x3b44420cfc31367c

def z312 : W := mkw 0x613fa0447beb6280 0xe613fa0447beb628 0x823520ccf3636001 0x0823520ccf363600

def z313 : W := mkw 0x2413082810c00824 0x52413082810c0082 0x4bb3183030e09835 0xc4bb3183030e0983

def z314 : W := mkw 0x403fa0002a0a0000 0xe403fa0002a0a000 0x1fffe0000f1f0002 0x01fffe0000f1f000

def z315 : W := mkw 0x782c15c03fcad608 0x8782c15c03fcad60 0xe7fc1fc03fffff0f 0xde7fc1fc03fffff0

def z316 : W := mkw 0x1200431204048412 0x0120043120404841 0x698ac7300c8c80fc 0xe698ac7300c8c80f

def z317 : W := mkw 0x1200431204048412 0x0120043120404841 0x658ac7300c8c873a 0xd658ac7300c8c873

def z318 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x013800003c000000 0x8013800003c00000

def z319 : W := mkw 0x1200010104148552 0x0120001010414855 0x1dcac0000c9c87fe 0xc1dcac0000c9c87f

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0x4130180030009800 0x8413018003000980

def z321 : W := mkw 0x802cb48080000000 0xa802cb4808000000 0x000420c0c0000000 0x0000420c0c000000

def z322 : W := mkw 0x1c001dec0520feac 0x11c001dec0520fea 0xe0001ffc0000fff8 0x3e0001ffc0000fff

def z323 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x07bc07c03f000703 0xd07bc07c03f00070

def z324 : W := mkw 0x120043170434a5d2 0x0120043170434a5d 0xffcbc73f0cfce7ff 0xfffcbc73f0cfce7f

def z325 : W := mkw 0x492c14c46b217288 0x8492c14c46b21728 0x823538ccf3637801 0x0823538ccf363780

def z326 : W := mkw 0x2413000410e028a4 0x42413000410e028a 0x0bb3000030e0f8fd 0xc0bb3000030e0f8f

def z327 : W := mkw 0x0000004001004200 0x0000000400100420 0x820400c003006001 0x0820400c00300600

def z328 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0xbeb538cfc0000000 0x3beb538cfc000000

def z329 : W := mkw 0x5a2c57922e04941a 0x85a2c57922e04941 0x413adf303c8c9830 0x8413adf303c8c983

def z330 : W := mkw 0x03004257413563d2 0x003004257413563d 0xbec7e0ffc3ff67ff 0x7bec7e0ffc3ff67f

def z331 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x0000000033630001 0x0000000003363000

def z332 : W := mkw 0x01000005403121c0 0x001000005403121c 0x00400000007300c4 0x000400000007300c

def z333 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xea81183c0060f8fd 0x6ea81183c0060f8f

def z334 : W := mkw 0x813ffebfc03121c0 0xf813ffebfc03121c 0xffffffffc07300c4 0x3ffffffffc07300c

def z335 : W := mkw 0x7a3ff7d33fded75a 0xe7a3ff7d33fded75 0xfffffff33fffffff 0xffffffff33ffffff

def z336 : W := mkw 0x92005fbb84148552 0x192005fbb8414855 0xe0001fffc00087f8 0x3e0001fffc00087f

def z337 : W := mkw 0x1200010104148552 0x0120001010414855 0x3cc000030c9c87fe 0xf3cc000030c9c87f

def z338 : W := mkw 0x01000045413163c0 0x001000045413163c 0x9a4520cfc37360c5 0x29a4520cfc37360c

def z339 : W := mkw 0x0000004401206280 0x0000000440120628 0xae8500cc036067cf 0x7ae8500cc036067c

def z340 : W := mkw 0x130043534515c752 0x0130043534515c75 0x7dcee7f3cf9f87fe 0xf7dcee7f3cf9f87f

def z341 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1dcbe0000cff0006 0xc1dcbe0000cff000

def z342 : W := mkw 0x8213ea3b80140152 0x78213ea3b8014015 0x1843e03fc09c00f4 0x21843e03fc09c00f

def z343 : W := mkw 0x3213431314d48552 0x43213431314d4855 0x7ffbc7333cfc87ff 0xf7ffbc7333cfc87f

def z344 : W := mkw 0xa4135ebe90e028a4 0x5a4135ebe90e028a 0xebb31ffff0e0f8fd 0xfebb31ffff0e0f8f

def z345 : W := mkw 0x0000000100100140 0x0000000010010014 0x1440000300100702 0x1144000030010070

def z346 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xc33ffffcc0000000 0x0c33ffffcc000000

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x140420c3c0000000 0x1140420c3c000000

def z348 : W := mkw 0x643fa82c3aea28a4 0xf643fa82c3aea28a 0x9ffff80c3fff7807 0xc9ffff80c3fff780

def z349 : W := mkw 0xa013ea3a90ca0000 0x7a013ea3a90ca000 0x1843e03fc0ff0004 0x21843e03fc0ff000

def z350 : W := mkw 0x610000457bfb63c0 0x0610000457bfb63c 0xbec520cfffff67cf 0xfbec520cfffff67c

def z351 : W := mkw 0x0200000100140152 0x0020000010014015 0x00400000009c00f4 0x000400000009c00f

def z352 : W := mkw 0x0200421300140152 0x0020042130014015 0x7dcac733009c00f4 0x37dcac733009c00f

def z353 : W := mkw 0x803ffefa81004200 0xf803ffefa8100420 0xffbfffffc300670b 0x7ffbfffffc300670

def z354 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0xbecde7cfcf7f67cf 0x7becde7cfcf7f67c

def z355 : W := mkw 0x110001454531e7c0 0x0110001454531e7c 0xffcd27cfcf73e7cf 0xfffcd27cfcf73e7c

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c80000300000000 0x33c8000030000000

def z357 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe13adfffc0000000 0x3e13adfffc000000

def z358 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0xe7bc1fc033007801 0x1e7bc1fc03300780

def z359 : W := mkw 0x2113004551f163c0 0x42113004551f163c 0xbff720cff3f367cf 0xfbff720cff3f367c

def z360 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa20520cfc36367c9 0x3a20520cfc36367c

def z361 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d8ac00000000000 0x01d8ac0000000000

def z362 : W := mkw 0x720001013ede8552 0x0720001013ede855 0x004000003fff87ff 0xc004000003fff87f

def z363 : W := mkw 0x582cb5c02f0ad608 0xa582cb5c02f0ad60 0x144ce7c00f1f0702 0x1144ce7c00f1f070

def z364 : W := mkw 0x0000421200000000 0x0000042120000000 0x1802c03300000000 0x21802c0330000000

def z365 : W := mkw 0x0000000100100140 0x0000000010010014 0x3ec52003037307cf 0x73ec52003037307c

def z366 : W := mkw 0xd83fffbaae009408 0xfd83fffbaae00940 0x413adf303c009800 0x8413adf303c00980

def z367 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0x0030180000000000 0x0003018000000000

def z368 : W := mkw 0x723fe3123ece8412 0xe723fe3123ece841 0x5fffe7303fff8037 0xc5fffe7303fff803

def z369 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x000000003c8c0000 0x8000000003c8c000

def z370 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xbfffe0cfffff0007 0xfbfffe0cfffff000

def z371 : W := mkw 0x590001456f31f7c8 0x0590001456f31f7c 0xbec520cfff73ffcf 0xfbec520cfff73ffc

def z372 : W := mkw 0x16004b3f0434adf6 0x116004b3f0434adf 0xe0001f3f0000fff8 0x3e0001f3f0000fff

def z373 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffbfffffff000003 0xfffbfffffff00000

def z374 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe6841fc00300ff0b 0x5e6841fc00300ff0

def z375 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0x0000003c000000f0 0x20000003c000000f

def z376 : W := mkw 0x610000457bfb63c0 0x0610000457bfb63c 0x004000003fff67cf 0xc004000003fff67c

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x0684000003000003 0x4068400000300000

def z378 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x5fbfff3000000000 0x05fbfff300000000

def z379 : W := mkw 0x623fe2133ade0152 0xe623fe2133ade015 0x1fffe0333fff00f7 0xe1fffe0333fff00f

def z380 : W := mkw 0x080014c001005208 0x0080014c00100520 0x800018c000007800 0x0800018c00000780

def z381 : W := mkw 0x36134b3f14f4adf6 0x536134b3f14f4adf 0x7dcbc73f0cfc87fe 0xf7dcbc73f0cfc87f

def z382 : W := mkw 0x0000000400202080 0x0000000040020208 0xebb1180c3060f8cd 0xeebb1180c3060f8c

def z383 : W := mkw 0x7c3f1dec3fe0feac 0xd7c3f1dec3fe0fea 0xe7bd1fcc3f60ff0b 0xde7bd1fcc3f60ff0

def z384 : W := mkw 0x402c00402b004200 0x8402c00402b00420 0xa7bc00c03f00670b 0xda7bc00c03f00670

def z385 : W := mkw 0x01000005403121c0 0x001000005403121c 0x1ec5200fc37300c7 0x61ec5200fc37300c

def z386 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x157ee0003f9f0002 0x8157ee0003f9f000

def z387 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe7bedff000000000 0x1e7bedff00000000

def z388 : W := mkw 0x130043534515c752 0x0130043534515c75 0x144ce7c3cf1f0702 0x1144ce7c3cf1f070

def z389 : W := mkw 0x0000000100100140 0x0000000010010014 0x7dc20033009087fe 0xf7dc20033009087f

def z390 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0xaa81000c30e0f8fd 0xeaa81000c30e0f8f

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x08020030008000f4 0x208020030008000f

def z392 : W := mkw 0x5b2c57d76f35f7da 0x85b2c57d76f35f7d 0xffffffffffffffff 0xffffffffffffffff

def z393 : W := mkw 0x03004217403521d2 0x003004217403521d 0x1843e03fc0ff00f4 0x21843e03fc0ff00f

def z394 : W := mkw 0x0000000400202080 0x0000000040020208 0x00000000006060cd 0x400000000006060c

def z395 : W := mkw 0x7d3f1ded7ff1ffec 0xd7d3f1ded7ff1ffe 0xffff3ffffff3ffff 0xfffff3ffffff3fff

def z396 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0x87bc18c03f007803 0xc87bc18c03f00780

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000003000f809 0xc000000003000f80

def z398 : W := mkw 0x601300003aca0000 0x4601300003aca000 0x0bf300003fff0007 0xc0bf300003fff000

def z399 : W := mkw 0x0100000440212080 0x0010000044021208 0x0001200cc0630000 0x00001200cc063000

def z400 : W := mkw 0xc03ffebaaa0a0000 0xfc03ffebaaa0a000 0xffffffffcf1f0002 0x3ffffffffcf1f000

def z401 : W := mkw 0x01000045413163c0 0x001000045413163c 0x1841200fc37367cf 0x61841200fc37367c

def z402 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0x000807000c000000 0x0000807000c00000

def z403 : W := mkw 0x80004a3a80000000 0x180004a3a8000000 0x0000003fc0000000 0x20000003fc000000

def z404 : W := mkw 0x98005ffa8500d608 0x198005ffa8500d60 0xe0001fffc000ff08 0x3e0001fffc000ff0

def z405 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x0bbbc0003cec0005 0xc0bbbc0003cec000

def z406 : W := mkw 0xa43ffebe90e028a4 0xfa43ffebe90e028a 0xffbffffff0607801 0x3ffbffffff060780

def z407 : W := mkw 0x182c15c00500d608 0x8182c15c00500d60 0xe7bc1fc00000ff08 0x1e7bc1fc00000ff0

def z408 : W := mkw 0x00000005003021c0 0x000000005003021c 0xbec1000f007067cf 0x7bec1000f007067c

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0000000100006 0x41cc000000010000

def z410 : W := mkw 0x400000002a0a0000 0x0400000002a0a000 0x004000000f1f0002 0x0004000000f1f000

def z411 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x07bec0003f8c0003 0xc07bec0003f8c000

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000003730007 0x4004000000373000

def z413 : W := mkw 0x80001ca880000000 0x180001ca88000000 0x800018ccc0000000 0x0800018ccc000000

def z414 : W := mkw 0x12134b3b04148552 0x512134b3b0414855 0xfffbdf3f0c9c87fe 0xffffbdf3f0c9c87f

def z415 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xebbbdf3c00000000 0x2ebbbdf3c0000000

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x6588070000000000 0x1658807000000000

def z417 : W := mkw 0x1000010004008400 0x0100001000400840 0x000000000c00870a 0xc000000000c00870

def z418 : W := mkw 0x582cb5c02f0ad608 0xa582cb5c02f0ad60 0xf7fcffc03f1fff0b 0xdf7fcffc03f1fff0

def z419 : W := mkw 0x1000431204008400 0x0100043120400840 0x7d8ac7330c00870a 0xf7d8ac7330c00870

def z420 : W := mkw 0x81005effc13163c0 0x181005effc13163c 0xfec53fffc37367cf 0x7fec53fffc37367c

def z421 : W := mkw 0x0000000100100140 0x0000000010010014 0x18400003001000c4 0x218400003001000c

def z422 : W := mkw 0x0000421200000000 0x0000042120000000 0x6000073300000000 0x3600007330000000

def z423 : W := mkw 0x0013082800000000 0x5001308280000000 0x0803003c00000000 0x20803003c0000000

def z424 : W := mkw 0x0000421200000000 0x0000042120000000 0x410ac73000000000 0x0410ac7300000000

def z425 : W := mkw 0x603fe2123aca0000 0xe603fe2123aca000 0x7fffe7333fff0007 0xf7fffe7333fff000

def z426 : W := mkw 0x783fb5803eca9408 0xe783fb5803eca940 0x5fffff003fff9807 0xc5fffff003fff980

def z427 : W := mkw 0x1200431304148552 0x0120043130414855 0x7fcfe7330fff87ff 0xf7fcfe7330fff87f

def z428 : W := mkw 0x592c15c56f31f7c8 0x8592c15c56f31f7c 0xe7bc1fcfff00ffcb 0xfe7bc1fcfff00ffc

def z429 : W := mkw 0x0013082800000000 0x5001308280000000 0x8231180c00000000 0x08231180c0000000

def z430 : W := mkw 0x6c3f1cec3be07aac 0xd6c3f1cec3be07aa 0xebb718fc33e0f8fd 0xeebb718fc33e0f8f

def z431 : W := mkw 0x7c3f1da83ec09c2c 0xd7c3f1da83ec09c2 0x413a1f303c809830 0x8413a1f303c80983

def z432 : W := mkw 0x412c00456b3163c0 0x8412c00456b3163c 0xbffd20cfff7367cf 0xfbffd20cfff7367c

def z433 : W := mkw 0x01000005403121c0 0x001000005403121c 0x0000000fc00000c0 0x20000000fc00000c

def z434 : W := mkw 0x01000045413163c0 0x001000045413163c 0x144420c3c37367cf 0x5144420c3c37367c

def z435 : W := mkw 0x813ffeffc13163c0 0xf813ffeffc13163c 0xffbfffffc00067c8 0x3ffbfffffc00067c

def z436 : W := mkw 0xa43ffebe90e028a4 0xfa43ffebe90e028a 0xebbbdf3c30e0f8fd 0xeebbbdf3c30e0f8f

def z437 : W := mkw 0x2013000010c00000 0x42013000010c0000 0xebb3180030e0f80d 0xcebb3180030e0f80

def z438 : W := mkw 0x723fa1013ede8552 0xe723fa1013ede855 0x1fffe0003fff87ff 0xc1fffe0003fff87f

def z439 : W := mkw 0x203fa00010c00000 0xe203fa00010c0000 0x1fbfe00030e00005 0xc1fbfe00030e0000

def z440 : W := mkw 0x01000045413163c0 0x001000045413163c 0x3cc00003037367cf 0x73cc00003037367c

def z441 : W := mkw 0x683fb4c03bca5208 0xe683fb4c03bca520 0x9ffff8c03fff7807 0xc9ffff8c03fff780

def z442 : W := mkw 0x922cf79384148552 0xa922cf7938414855 0x144ce7c3cc1c0702 0x1144ce7c3cc1c070

def z443 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x1dcee0000f9f0006 0xc1dcee0000f9f000

def z444 : W := mkw 0xa43fbcac90e028a4 0xfa43fbcac90e028a 0x823538ccf0607801 0x0823538ccf060780

def z445 : W := mkw 0x903fffba84008400 0xf903fffba8400840 0xffbfffffcc00870a 0xfffbfffffcc00870

def z446 : W := mkw 0x813fbcedc13163c0 0xf813fbcedc13163c 0xbef538cfc37367cf 0x7bef538cfc37367c

def z447 : W := mkw 0x5c2c1dec2f20feac 0x95c2c1dec2f20fea 0xe7bc1ffc3f00fffb 0xfe7bc1ffc3f00fff

def z448 : W := mkw 0x592c15c16f11d748 0x8592c15c16f11d74 0xf7fc3fc3ff13ff0b 0xdf7fc3fc3ff13ff0

def z449 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe40c1fc00f00ff0a 0x1e40c1fc00f00ff0

def z450 : W := mkw 0x613fa0457bfb63c0 0xe613fa0457bfb63c 0x1fffe0003fff67cf 0xc1fffe0003fff67c

def z451 : W := mkw 0x813ffefec1216280 0xf813ffefec121628 0xffbfffffc3636001 0x3ffbfffffc363600

def z452 : W := mkw 0x793fb5c57ffbf7c8 0xe793fb5c57ffbf7c 0xffffffcfffffffcf 0xfffffffcfffffffc

def z453 : W := mkw 0x5a2c57d32f14d75a 0x85a2c57d32f14d75 0x7dcec7f30f9c87fe 0xf7dcec7f30f9c87f

def z454 : W := mkw 0x1000010004008400 0x0100001000400840 0x7dcac7000c9c870e 0xd7dcac7000c9c870

def z455 : W := mkw 0x583fb5c02f00d608 0xe583fb5c02f00d60 0xffbfffc03f00ff0b 0xdffbfffc03f00ff0

def z456 : W := mkw 0x92005fbb84148552 0x192005fbb8414855 0xfdcadfffcc9c87fe 0xffdcadfffcc9c87f

def z457 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xa68c07c00f00670b 0x5a68c07c00f00670

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x6180000000008008 0xc618000000000800

def z459 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x0bb3003c30e000f5 0xe0bb3003c30e000f

def z460 : W := mkw 0x823ffebb80140152 0xf823ffebb8014015 0xffffffffc09c00f4 0x3ffffffffc09c00f

def z461 : W := mkw 0x5a2c15c12f14d75a 0x85a2c15c12f14d75 0xe7fc1fc03f9cffff 0xde7fc1fc03f9cfff

def z462 : W := mkw 0x1200010104148552 0x0120001010414855 0x00000000000087f8 0x000000000000087f

def z463 : W := mkw 0x783fb5c03fcad608 0xe783fb5c03fcad60 0xe7bd3fc03f63ff0b 0xde7bd3fc03f63ff0

def z464 : W := mkw 0x613fa0457bfb63c0 0xe613fa0457bfb63c 0xbef520cff37367cf 0x7bef520cff37367c

def z465 : W := mkw 0x580001402f00d608 0x0580001402f00d60 0xe3b018003f00ff0b 0xce3b018003f00ff0

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa81000c00000000 0x2aa81000c0000000

def z467 : W := mkw 0x2513086d51f16be4 0x52513086d51f16be 0xebf3183c33f3ffff 0xeebf3183c33f3fff

def z468 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0xfffff83c3fff0007 0xefffff83c3fff000

def z469 : W := mkw 0x0000004001004200 0x0000000400100420 0xbec520c00373670f 0x5bec520c00373670

def z470 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x013ac00000000000 0x0013ac0000000000

def z471 : W := mkw 0x1200431304148552 0x0120043130414855 0x3cc8c7030c1c07ce 0x73cc8c7030c1c07c

def z472 : W := mkw 0x0000000000000000 0x0000000000000000 0x1801200fc0000000 0x21801200fc000000

def z473 : W := mkw 0x803fea3a80000000 0xf803fea3a8000000 0x1fbfe03fc0000000 0x21fbfe03fc000000

def z474 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe132183c3080f8f8 0xae132183c3080f8f

def z475 : W := mkw 0x640000043aea28a4 0x0640000043aea28a 0x004000003ffff8ff 0xc004000003ffff8f

def z476 : W := mkw 0x703fa1003eca8400 0xe703fa1003eca840 0x7fffe7003fff870f 0xd7fffe7003fff870

def z477 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xe982183c0080f8fc 0xee982183c0080f8f

def z478 : W := mkw 0x7c0001443fe0feac 0x07c0001443fe0fea 0x000000003fe0ffff 0xc000000003fe0fff

def z479 : W := mkw 0x1200431304148552 0x0120043130414855 0x0000070300000700 0x1000007030000070

def z480 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xfffedfc03f9cff0f 0xdfffedfc03f9cff0

def z481 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x453c1fc03f009f02 0x9453c1fc03f009f0

def z482 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x6983003c00e080fc 0xe6983003c00e080f

def z483 : W := mkw 0x580001402f00d608 0x0580001402f00d60 0x000000000f000702 0x0000000000f00070

def z484 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbe8520cfc00067c8 0x3be8520cfc00067c

def z485 : W := mkw 0x0013000000000000 0x4001300000000000 0x0bb3000000000000 0x00bb300000000000

def z486 : W := mkw 0x643f082c3ae028a4 0xd643f082c3ae028a 0xefbf183c3fe0f8ff 0xeefbf183c3fe0f8f

def z487 : W := mkw 0x613fa0057afb21c0 0xe613fa0057afb21c 0x1fffe00fffff00c7 0xe1fffe00fffff00c

def z488 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0x9fbff8ccc0000000 0x09fbff8ccc000000

def z489 : W := mkw 0x783fb5803eca9408 0xe783fb5803eca940 0x413adf003c8c9800 0x8413adf003c8c980

def z490 : W := mkw 0x603fa0013ada0140 0xe603fa0013ada014 0x3fffe0033fff07cf 0xf3fffe0033fff07c

def z491 : W := mkw 0x613fa0447beb6280 0xe613fa0447beb628 0x9fffe0ccffff6007 0xc9fffe0ccffff600

def z492 : W := mkw 0x002c148000000000 0x8002c14800000000 0x41381f0000000000 0x041381f000000000

def z493 : W := mkw 0x0100004441216280 0x0010000444121628 0x9ec520ccc3736007 0x49ec520ccc373600

def z494 : W := mkw 0x0100004041014200 0x0010000404101420 0x000420c0c3030000 0x0000420c0c303000

def z495 : W := mkw 0x0100004141114340 0x0010000414111434 0x0040000003130702 0x0004000000313070

def z496 : W := mkw 0x603fa0403bca4200 0xe603fa0403bca420 0xbfffe0c03fff670f 0xdbfffe0c03fff670

def z497 : W := mkw 0x190015c54531f7c8 0x0190015c54531f7c 0xe0001fcfc000ffc8 0x3e0001fcfc000ffc

def z498 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1ec7e00003ff0007 0x41ec7e00003ff000

def z499 : W := mkw 0x813fbcecc1216280 0xf813fbcecc121628 0x823538ccc3636001 0x0823538ccc363600

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00018000000f808 0x0e00018000000f80

def z501 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x1ffd20003f730007 0xc1ffd20003f73000

def z502 : W := mkw 0x812cf6d3c1114340 0xa812cf6d3c111434 0x144ce7c3c3130702 0x1144ce7c3c313070

def z503 : W := mkw 0x592c15c56f31f7c8 0x8592c15c56f31f7c 0xe7fc1fc03f73ffcf 0xde7fc1fc03f73ffc

def z504 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0xe7bd3fccc0000000 0x1e7bd3fccc000000

def z505 : W := mkw 0x102c158004008400 0x8102c15800400840 0xe7bc1fc00c00870a 0xde7bc1fc00c00870

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0xa68400c000000000 0x1a68400c00000000

def z507 : W := mkw 0x1000010004008400 0x0100001000400840 0xe7b81f003c00ff0b 0xde7b81f003c00ff0

def z508 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0xfec527ffc373e7ff 0x7fec527ffc373e7f

def z509 : W := mkw 0x0013a00000000000 0x60013a0000000000 0x1803e00000000000 0x01803e0000000000

def z510 : W := mkw 0xd82cf7d2af00d608 0xad82cf7d2af00d60 0x140ce7c3cf000702 0x1140ce7c3cf00070

def z511 : W := mkw 0xd82c5ffaaf00d608 0x9d82c5ffaaf00d60 0xe7bc1fffff00ff0b 0xfe7bc1fffff00ff0

def z512 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xaa83003c00e060fd 0x6aa83003c00e060f

def z513 : W := mkw 0x843ffebe802028a4 0xf843ffebe802028a 0xffbfffffc000f8f8 0x3ffbfffffc000f8f

def z514 : W := mkw 0x01000005403121c0 0x001000005403121c 0xbec520cfc07300c4 0x3bec520cfc07300c

def z515 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x658c07c00f00870a 0xd658c07c00f00870

def z516 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x823418c03f00ff0b 0xc823418c03f00ff0

def z517 : W := mkw 0x1200431304148552 0x0120043130414855 0x1842c0330c9c87fe 0xe1842c0330c9c87f

def z518 : W := mkw 0x203fa00010ca0000 0xe203fa00010ca000 0x1fffe00000ff0004 0x01fffe00000ff000

def z519 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x0001000c00600000 0x00001000c0060000

def z520 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fc00f000702 0x1e7bc1fc00f00070

def z521 : W := mkw 0x3c131dec15e0feac 0x53c131dec15e0fea 0xebb31ffc30e0fffd 0xfebb31ffc30e0fff

def z522 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1dfac0003c9c0006 0xc1dfac0003c9c000

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0xbec520cfc3730007 0x7bec520cfc373000

def z524 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0x65b81f003c009f0a 0xd65b81f003c009f0

def z525 : W := mkw 0x2413082810c00824 0x52413082810c0082 0xebb3183c30809830 0xaebb3183c3080983

def z526 : W := mkw 0x603f00003ac00000 0xc603f00003ac0000 0x0fbf00003fe00007 0xc0fbf00003fe0000

def z527 : W := mkw 0x9213eb3b84148552 0x79213eb3b8414855 0x7dcbe73fcc9c87fe 0xf7dcbe73fcc9c87f

def z528 : W := mkw 0x580015c02f00d608 0x0580015c02f00d60 0xe0001fc03f00ff0b 0xde0001fc03f00ff0

def z529 : W := mkw 0x582c15c12f10d748 0x8582c15c12f10d74 0xfffc1fc33f10ffcf 0xffffc1fc33f10ffc

def z530 : W := mkw 0x613fa0417bdb4340 0xe613fa0417bdb434 0x1fffe0c3ffff0707 0xd1fffe0c3ffff070

def z531 : W := mkw 0x0100004441216280 0x0010000444121628 0x800000ccc0006000 0x0800000ccc000600

def z532 : W := mkw 0x783fb5c03fcad608 0xe783fb5c03fcad60 0x1fffe7c03fff0707 0xd1fffe7c03fff070

def z533 : W := mkw 0x2500004551f16be4 0x02500004551f16be 0x0040000033f3ffff 0xc0040000033f3fff

def z534 : W := mkw 0xda3ffffbaf14d75a 0xfda3ffffbaf14d75 0xffffffffff9cffff 0xfffffffffff9cfff

def z535 : W := mkw 0x01000045413163c0 0x001000045413163c 0x824520ccc37367cf 0x4824520ccc37367c

def z536 : W := mkw 0xd82cf7d2af00d608 0xad82cf7d2af00d60 0xf7bcffc3ff00ff0b 0xdf7bcffc3ff00ff0

def z537 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb3183c00e000f4 0x2ebb3183c00e000f

def z538 : W := mkw 0x2413082810c00824 0x52413082810c0082 0x0002003000800030 0x0000200300080003

def z539 : W := mkw 0x0000004001004200 0x0000000400100420 0x000000000300670b 0x4000000000300670

def z540 : W := mkw 0x01000045413163c0 0x001000045413163c 0xaac1000c037367cf 0x6aac1000c037367c

def z541 : W := mkw 0x803ffebe80202080 0xf803ffebe8020208 0xffbfffffc06060cd 0x7ffbfffffc06060c

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000030000080f8 0x260000030000080f

def z543 : W := mkw 0x002c569200000000 0x8002c56920000000 0xffbedff300000000 0x3ffbedff30000000

def z544 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fbfe00033630001 0x01fbfe0003363000

def z545 : W := mkw 0x643fa0043aea28a4 0xe643fa0043aea28a 0x1fffe0003ffff8ff 0xc1fffe0003ffff8f

def z546 : W := mkw 0x0000000000000000 0x0000000000000000 0x248000000000070a 0x5248000000000070

def z547 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0xbec520cfcfffe7ff 0xfbec520cfcfffe7f

def z548 : W := mkw 0x00134a3a00000000 0x500134a3a0000000 0xffbbdf3f00000000 0x3ffbbdf3f0000000

def z549 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x963dffcfc0000000 0x1963dffcfc000000

def z550 : W := mkw 0x01000005403121c0 0x001000005403121c 0x3cc1200fc07307ce 0x73cc1200fc07307c

def z551 : W := mkw 0x0000000400202080 0x0000000040020208 0xbe8520cfc06060cd 0x7be8520cfc06060c

def z552 : W := mkw 0x780001403fcad608 0x0780001403fcad60 0x004000003fffff0f 0xc004000003fffff0

def z553 : W := mkw 0x0000000100100140 0x0000000010010014 0x20000003000007c8 0x320000003000007c

def z554 : W := mkw 0x1a0057d30514d75a 0x01a0057d30514d75 0xfdcadff30c9cfffe 0xffdcadff30c9cfff

def z555 : W := mkw 0x81005effc13163c0 0x181005effc13163c 0xe0001fffc00067c8 0x3e0001fffc00067c

def z556 : W := mkw 0x2013000410e02080 0x42013000410e0208 0xabb3000c30e060cd 0xeabb3000c30e060c

def z557 : W := mkw 0x0200421300140152 0x0020042130014015 0x1dcac0330c9c00f6 0xe1dcac0330c9c00f

def z558 : W := mkw 0x243fa82c10e028a4 0xf243fa82c10e028a 0xffbff83c30e0f8fd 0xeffbff83c30e0f8f

def z559 : W := mkw 0x0000004001004200 0x0000000400100420 0xe7b418c03300ff0b 0xde7b418c03300ff0

def z560 : W := mkw 0x002c148000000000 0x8002c14800000000 0xffbd3fcfc0000000 0x3ffbd3fcfc000000

def z561 : W := mkw 0x0200421300140152 0x0020042130014015 0x1040c003001c0000 0x01040c003001c000

def z562 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1ef5200033730007 0x41ef520003373000

def z563 : W := mkw 0xa43fbcac90e028a4 0xfa43fbcac90e028a 0xebb738fcf0e0f8fd 0xeebb738fcf0e0f8f

def z564 : W := mkw 0x5a0043532f14d75a 0x05a0043532f14d75 0x7dcac7333f9cffff 0xf7dcac7333f9cfff

def z565 : W := mkw 0x7c3f1de83fc0de2c 0xd7c3f1de83fc0de2 0xe7be1ff03f80ff3b 0xde7be1ff03f80ff3

def z566 : W := mkw 0x723fe3133ede8552 0xe723fe3133ede855 0x7dfac7333c9c87fe 0xf7dfac7333c9c87f

def z567 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fbfe0003c8c0000 0x81fbfe0003c8c000

def z568 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0xebb738fcc0000000 0x2ebb738fcc000000

def z569 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x0001200000630000 0x0000120000063000

def z570 : W := mkw 0x643fa82c3aea28a4 0xf643fa82c3aea28a 0xebb7383c33e3f8fd 0xeebb7383c33e3f8f

def z571 : W := mkw 0x2513082d50f129e4 0x52513082d50f129e 0xfbf3383ff0f3f8fd 0xefbf3383ff0f3f8f

def z572 : W := mkw 0x723fe3133ede8552 0xe723fe3133ede855 0x1fffe7033fff0707 0xd1fffe7033fff070

def z573 : W := mkw 0x002c148000000000 0x8002c14800000000 0x823418c000000000 0x0823418c00000000

def z574 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0x6982003030e0f8fd 0xe6982003030e0f8f

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a81000000600005 0x40a8100000060000

def z576 : W := mkw 0x130043174435a5d2 0x0130043174435a5d 0x7dcbe73fccff87fe 0xf7dcbe73fccff87f

def z577 : W := mkw 0x002c148000000000 0x8002c14800000000 0xe7bc1fc03000f809 0xde7bc1fc03000f80

def z578 : W := mkw 0x013fa045413163c0 0xe013fa045413163c 0xbfffe0cfc37367cf 0x7bfffe0cfc37367c

def z579 : W := mkw 0x492c14c56b3173c8 0x8492c14c56b3173c 0xbef538cff3737fcf 0x7bef538cff3737fc

def z580 : W := mkw 0x2000000010c00000 0x02000000010c0000 0x0000000030e00005 0xc0000000030e0000

def z581 : W := mkw 0x190015c54531f7c8 0x0190015c54531f7c 0xfec53fcfc373ffcf 0x7fec53fcfc373ffc

def z582 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa6c400c0037367cf 0x5a6c400c0037367c

def z583 : W := mkw 0x122c579304148552 0x8122c57930414855 0xfffedff30c9c87fe 0xffffedff30c9c87f

def z584 : W := mkw 0x100001400500c600 0x0100001400500c60 0xe78c07c00f00e70b 0xde78c07c00f00e70

def z585 : W := mkw 0x2513086c51e16aa4 0x52513086c51e16aa 0x823538ccf3637801 0x0823538ccf363780

def z586 : W := mkw 0x0400082800000824 0x1040008280000082 0x4000183000009830 0x0400018300000983

def z587 : W := mkw 0x1200431304148552 0x0120043130414855 0x594ac7330c9c80f4 0xa594ac7330c9c80f

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x03b0000030000001 0xc03b000003000000

def z589 : W := mkw 0x592c15c56f31f7c8 0x8592c15c56f31f7c 0xbecd27cfcf7367cf 0x7becd27cfcf7367c

def z590 : W := mkw 0x012c14c5413163c0 0x8012c14c5413163c 0xfffd3fcfc37367cf 0x7fffd3fcfc37367c

def z591 : W := mkw 0x1200431304148552 0x0120043130414855 0x554ac7330c9c8732 0x9554ac7330c9c873

def z592 : W := mkw 0x643fa82c3aea28a4 0xf643fa82c3aea28a 0xebbbd83c3cecf8fd 0xeebbbd83c3cecf8f

def z593 : W := mkw 0x0413082c002028a4 0x50413082c002028a 0xebb3183c0000f8f8 0x2ebb3183c0000f8f

def z594 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1a77e00033ff0005 0x01a77e00033ff000

def z595 : W := mkw 0x8113ea7fc13163c0 0x78113ea7fc13163c 0xbec7e0ffc37367cf 0x7bec7e0ffc37367c

def z596 : W := mkw 0x1200010104148552 0x0120001010414855 0x004000000c1c0702 0x0004000000c1c070

def z597 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcac7330c1c0702 0x37dcac7330c1c070

def z598 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0132000030800000 0x8013200003080000

def z599 : W := mkw 0x8013ea3a80000000 0x78013ea3a8000000 0xbe87e0ffc0000000 0x3be87e0ffc000000

def z600 : W := mkw 0x8013ea3a80000000 0x78013ea3a8000000 0x7d8be73fc0000000 0x37d8be73fc000000

def z601 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0xe3b0180030e0f8fd 0xce3b0180030e0f8f

def z602 : W := mkw 0x36134b3a14c48c36 0x536134b3a14c48c3 0x413adf303c8c9830 0x8413adf303c8c983

def z603 : W := mkw 0x8013ea3a80000000 0x78013ea3a8000000 0xfbb3f83fc0000000 0x2fbb3f83fc000000

def z604 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0xe3b418c03300f809 0xce3b418c03300f80

def z605 : W := mkw 0x1200431204048412 0x0120043120404841 0x4000073000008030 0x0400007300000803

def z606 : W := mkw 0x0000000100100140 0x0000000010010014 0x00400000001007ce 0x400400000001007c

def z607 : W := mkw 0x2113a00550fb21c0 0x62113a00550fb21c 0x1843e00fc0ff00c4 0x21843e00fc0ff00c

def z608 : W := mkw 0x1200431304148552 0x0120043130414855 0x658807330c0087fa 0xf658807330c0087f

def z609 : W := mkw 0x3600010514f4adf6 0x03600010514f4adf 0x004000003cfcffff 0xc004000003cfcfff

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x820520ccc0000000 0x0820520ccc000000

def z611 : W := mkw 0x0100004141114340 0x0010000414111434 0x1ec520c3c3730707 0x51ec520c3c373070

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x28800000000000cc 0x628800000000000c

def z613 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x0bb7200033e30005 0xc0bb7200033e3000

def z614 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0x0000000030607801 0x0000000003060780

def z615 : W := mkw 0x592c15c16f11d748 0x8592c15c16f11d74 0x144c27c3cf130702 0x1144c27c3cf13070

def z616 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb3183c008080fc 0xeebb3183c008080f

def z617 : W := mkw 0x243f1cac10e028a4 0xd243f1cac10e028a 0xefbf1ffc30e0f8fd 0xfefbf1ffc30e0f8f

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x1444200003130002 0x0144420000313000

def z619 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0x000400c003000000 0x0000400c00300000

def z620 : W := mkw 0xa413ea3e90e028a4 0x7a413ea3e90e028a 0x1803e03fc0e000f4 0x21803e03fc0e000f

def z621 : W := mkw 0x0200421200040012 0x0020042120004001 0x0002c030008c0030 0x00002c030008c003

def z622 : W := mkw 0x8013ea3a80000000 0x78013ea3a8000000 0x0002c03000000000 0x00002c0300000000

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x8230180030007801 0x0823018003000780

def z624 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0xfdcac7ffcc9ce7fe 0xffdcac7ffcc9ce7f

def z625 : W := mkw 0x6c3f1cec3be07aac 0xd6c3f1cec3be07aa 0x823518cc33607801 0x0823518cc3360780

def z626 : W := mkw 0xc83ffefaab005208 0xfc83ffefaab00520 0xffbffffff3007801 0x3ffbffffff300780

def z627 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe0000c9c0006 0xc1fffe0000c9c000

def z628 : W := mkw 0x783fb5c03fcad608 0xe783fb5c03fcad60 0xe7bedfc03f8cff0b 0xde7bedfc03f8cff0

def z629 : W := mkw 0x3413092c14e0aca4 0x53413092c14e0aca 0xefbb1f3c3ce0ffff 0xfefbb1f3c3ce0fff

def z630 : W := mkw 0x0100004441216280 0x0010000444121628 0xa68520ccc363670b 0x5a68520ccc363670

def z631 : W := mkw 0x003fa82800000000 0xf003fa8280000000 0xffbff83c00000000 0x2ffbff83c0000000

def z632 : W := mkw 0x0113086d413163c0 0x50113086d413163c 0xfff738ffc37367cf 0x7fff738ffc37367c

def z633 : W := mkw 0x783fa1403fcad608 0xe783fa1403fcad60 0x1fffe0003fffff0f 0xc1fffe0003fffff0

def z634 : W := mkw 0x482c14802a001008 0x8482c14802a00100 0x0030180030001800 0x0003018003000180

def z635 : W := mkw 0x592c15c46f21f688 0x8592c15c46f21f68 0xe7bd3fccff63ff0b 0xde7bd3fccff63ff0

def z636 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe1381fc03c00ff08 0x9e1381fc03c00ff0

def z637 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0xbfbfe0cfc0000000 0x3bfbfe0cfc000000

def z638 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x8bb3180c30e07805 0xc8bb3180c30e0780

def z639 : W := mkw 0x5a2c57d32f14d75a 0x85a2c57d32f14d75 0xe7bc1ff33f00fffb 0xfe7bc1ff33f00fff

def z640 : W := mkw 0x1000010004008400 0x0100001000400840 0x410807000c008000 0x8410807000c00800

def z641 : W := mkw 0x0013082800000000 0x5001308280000000 0x4132183000000000 0x0413218300000000

def z642 : W := mkw 0x84005ebe802028a4 0x184005ebe802028a 0xe0001fffc000f8f8 0x3e0001fffc000f8f

def z643 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x17fce0003f1f0003 0xc17fce0003f1f000

def z644 : W := mkw 0x1200010104148552 0x0120001010414855 0x65c807000c9c87fe 0xd65c807000c9c87f

def z645 : W := mkw 0x2413082810c00824 0x52413082810c0082 0x69b21830308098fc 0xe69b21830308098f

def z646 : W := mkw 0x923fffba84048412 0xf923fffba8404841 0xffbfffffcc8c8030 0xbffbfffffcc8c803

def z647 : W := mkw 0x7c3fbdec3feafeac 0xf7c3fbdec3feafea 0xfffffffc3fffffff 0xffffffffc3ffffff

def z648 : W := mkw 0x0000004101104340 0x0000000410110434 0xbec400c3031067cf 0x7bec400c3031067c

def z649 : W := mkw 0x502c01002e008400 0x8502c01002e00840 0x67bc07003f00870b 0xd67bc07003f00870

def z650 : W := mkw 0x0100004141114340 0x0010000414111434 0xbec520cfc3130702 0x3bec520cfc313070

def z651 : W := mkw 0x2400082c10e028a4 0x12400082c10e028a 0xe000183c30e0f8fd 0xee000183c30e0f8f

def z652 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xaab1180c306078cd 0x6aab1180c306078c

def z653 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1ffbc0003cfc0007 0xc1ffbc0003cfc000

def z654 : W := mkw 0x580001002e009408 0x0580001002e00940 0x000000003c009800 0x8000000003c00980

def z655 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0x47bc1f003f009803 0xc47bc1f003f00980

def z656 : W := mkw 0x522ce3132e1e8552 0xa522ce3132e1e855 0x144ce7030f1f0702 0x1144ce7030f1f070

def z657 : W := mkw 0x0000004001004200 0x0000000400100420 0xa00000c000006708 0x1a00000c00000670

def z658 : W := mkw 0x2000000010ca0000 0x02000000010ca000 0x0040000000ff0004 0x00040000000ff000

def z659 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa68400cfc30067cb 0x7a68400cfc30067c

def z660 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbffffffc8c0000 0xbffbffffffc8c000

def z661 : W := mkw 0x803ff69280000000 0xe803ff6928000000 0x1fbfe7c3c0000000 0x11fbfe7c3c000000

def z662 : W := mkw 0xc83fbce8ab005208 0xfc83fbce8ab00520 0x823538ccf3007801 0x0823538ccf300780

def z663 : W := mkw 0x1200431304148552 0x0120043130414855 0x7d8ac733000087f8 0x37d8ac733000087f

def z664 : W := mkw 0x36134b3e14e4acb6 0x536134b3e14e4acb 0xebbbdf3c3cecf8fd 0xeebbbdf3c3cecf8f

def z665 : W := mkw 0x0200421300140152 0x0020042130014015 0x79c2c033009c80fc 0xe79c2c033009c80f

def z666 : W := mkw 0x01000045413163c0 0x001000045413163c 0xb84120cfc07367cc 0x3b84120cfc07367c

def z667 : W := mkw 0x123fe31304148552 0xe123fe3130414855 0x7fffe7330c9c87fe 0xf7fffe7330c9c87f

def z668 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x07bd20003f630003 0xc07bd20003f63000

def z669 : W := mkw 0x0000000400202080 0x0000000040020208 0xbec5200c037360cf 0x6bec5200c037360c

def z670 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0x5fffff303fff0007 0xc5fffff303fff000

def z671 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x0008c0000c0c0000 0x00008c0000c0c000

def z672 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x0004200003030000 0x0000420000303000

def z673 : W := mkw 0x0500086d41316be4 0x10500086d41316be 0xe00018ffc000fff8 0x3e00018ffc000fff

def z674 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x1ec520003fff0007 0xc1ec520003fff000

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x6982003000000000 0x2698200300000000

def z676 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x1ffec0003f9c0007 0xc1ffec0003f9c000

def z677 : W := mkw 0x1200010004048412 0x0120001000404841 0x000000000c8c8030 0x8000000000c8c803

def z678 : W := mkw 0x1200431204048412 0x0120043120404841 0x7d8ac7330c8c8030 0xb7d8ac7330c8c803

def z679 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1ff7200033f30007 0xc1ff7200033f3000

def z680 : W := mkw 0x1000010004008400 0x0100001000400840 0x040807000c000702 0x1040807000c00070

def z681 : W := mkw 0x0000421200000000 0x0000042120000000 0x1408c70300000000 0x11408c7030000000

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3b0180000000000 0x0e3b018000000000

def z683 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1bf3e00030ff0005 0xc1bf3e00030ff000

def z684 : W := mkw 0x003fb48000000000 0xe003fb4800000000 0xffbfffc000000000 0x1ffbfffc00000000

def z685 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0xa6b418c033007f0b 0x5a6b418c033007f0

def z686 : W := mkw 0x583f1de82f00d608 0xd583f1de82f00d60 0xefbf1ffc3f00ff0b 0xfefbf1ffc3f00ff0

def z687 : W := mkw 0x2413082810c00824 0x52413082810c0082 0x0030180030001800 0x0003018003000180

def z688 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbcc000cfc01067ce 0x7bcc000cfc01067c

def z689 : W := mkw 0x3613092d14f4adf6 0x53613092d14f4adf 0xebf3183c3cfcffff 0xeebf3183c3cfcfff

def z690 : W := mkw 0x120043530514c752 0x0120043530514c75 0xffcec7f30f9ce7ff 0xfffcec7f30f9ce7f

def z691 : W := mkw 0x0000000400202080 0x0000000040020208 0x0801000c006000c4 0x20801000c006000c

def z692 : W := mkw 0x2513086d51f16be4 0x52513086d51f16be 0xebb318fff0e0fffd 0xfebb318fff0e0fff

def z693 : W := mkw 0x0100004441216280 0x0010000444121628 0xaa8520ccc36360cd 0x6aa8520ccc36360c

def z694 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x0803003c30e0f8fd 0xe0803003c30e0f8f

def z695 : W := mkw 0x602c00003aca0000 0x8602c00003aca000 0x07fc00003fff0007 0xc07fc00003fff000

def z696 : W := mkw 0x37134b7f55f5eff6 0x537134b7f55f5eff 0xffffffffffffffff 0xffffffffffffffff

def z697 : W := mkw 0x7e3f5fff3ff4fffe 0xd7e3f5fff3ff4fff 0xffffdfff3ffcffff 0xfffffdfff3ffcfff

def z698 : W := mkw 0x983ffffa8500d608 0xf983ffffa8500d60 0xffbfffffc000ff08 0x3ffbfffffc000ff0

def z699 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa04000cfc37367cf 0x7a04000cfc37367c

def z700 : W := mkw 0x0100000140110140 0x0010000014011014 0x10402003c0130000 0x010402003c013000

def z701 : W := mkw 0x1200431304148552 0x0120043130414855 0x7cc00733001087fe 0x77cc00733001087f

def z702 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0xe7bc1fc03c009800 0x9e7bc1fc03c00980

def z703 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0803000000e00004 0x00803000000e0000

def z704 : W := mkw 0x412ca0416b1b4340 0xa412ca0416b1b434 0x144ce0c3cf1f0702 0x1144ce0c3cf1f070

def z705 : W := mkw 0x5a2c57d32f14d75a 0x85a2c57d32f14d75 0xf7fcdfc33f1cff0b 0xdf7fcdfc33f1cff0

def z706 : W := mkw 0x0000004001004200 0x0000000400100420 0xbe8520cfc300670b 0x7be8520cfc300670

def z707 : W := mkw 0xa42cf69690e028a4 0xaa42cf69690e028a 0x140ce7c3f0e0f8fd 0xd140ce7c3f0e0f8f

def z708 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7fc1fc03f73ff0f 0xde7fc1fc03f73ff0

def z709 : W := mkw 0x4a2c56d32b14535a 0x84a2c56d32b14535 0x9a76d8f3339c78f5 0x29a76d8f3339c78f

def z710 : W := mkw 0x80135eba80000000 0x580135eba8000000 0xffbbdfffc0000000 0x3ffbbdfffc000000

def z711 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa24520cfc37367cf 0x7a24520cfc37367c

def z712 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0x1fffe7ffffff0007 0xf1fffe7ffffff000

def z713 : W := mkw 0x5b0001456f35f7da 0x05b0001456f35f7d 0x004000003fffffff 0xc004000003ffffff

def z714 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0x1c0de7cfc0000000 0x31c0de7cfc000000

def z715 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe00fffff0007 0xe1fffe00fffff000

def z716 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0xfffff8ffffff0007 0xffffff8ffffff000

def z717 : W := mkw 0x0200421300140152 0x0020042130014015 0xfbf2d833309cf8fd 0xefbf2d833309cf8f

def z718 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xf53effffc0000000 0x3f53effffc000000

def z719 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x014ac0003fff0007 0xc014ac0003fff000

def z720 : W := mkw 0x0100004441216280 0x0010000444121628 0xbe8520cfc363670b 0x7be8520cfc363670

def z721 : W := mkw 0x0000000100100140 0x0000000010010014 0xbec520cfc37307cf 0x7bec520cfc37307c

def z722 : W := mkw 0x592c15856e31b5c8 0x8592c15856e31b5c 0x59793f0ffc7398c4 0xa59793f0ffc7398c

def z723 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbffffff080f8fd 0xfffbffffff080f8f

def z724 : W := mkw 0x1200431304148552 0x0120043130414855 0xffcac7330c9ce7ff 0xfffcac7330c9ce7f

def z725 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0c3ffff0007 0xd1fffe0c3ffff000

def z726 : W := mkw 0x592c15c06f01d608 0x8592c15c06f01d60 0xe7bc3fc0ff03ff0b 0xde7bc3fc0ff03ff0

def z727 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xffbffffff0800000 0xbffbffffff080000

def z728 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xefb7183c33e0f8ff 0xeefb7183c33e0f8f

def z729 : W := mkw 0xf83fffbabeca9408 0xff83fffbabeca940 0x413adf303c8c9800 0x8413adf303c8c980

def z730 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffcc9c80fe 0xfffffffffcc9c80f

def z731 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc3000003 0x7ffbfffffc300000

def z732 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fc03f007f03 0x1e7bc1fc03f007f0

def z733 : W := mkw 0x182c15c00500d608 0x8182c15c00500d60 0xe7bc1fc03000ff09 0xde7bc1fc03000ff0

def z734 : W := mkw 0x823ffeba80040012 0xf823ffeba8004001 0xffbfffffc08c0030 0x3ffbfffffc08c003

def z735 : W := mkw 0x01000045413163c0 0x001000045413163c 0xb64520cfc37367cb 0x3b64520cfc37367c

def z736 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fcfff00ff0b 0xfe7bc1fcfff00ff0

def z737 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbfffffff8c0003 0xfffbfffffff8c000

def z738 : W := mkw 0x580001402f00d608 0x0580001402f00d60 0xe7b81f003f00ff0b 0xde7b81f003f00ff0

def z739 : W := mkw 0xc02cfebaaa0a0000 0xbc02cfebaaa0a000 0xf44cffffcf1f0002 0x3f44cffffcf1f000

def z740 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x167de0003fff0007 0xc167de0003fff000

def z741 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x8a33183c30e0f8fd 0xe8a33183c30e0f8f

def z742 : W := mkw 0x0100004141114340 0x0010000414111434 0xbec520cfc3730707 0x7bec520cfc373070

def z743 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0x1fffe03c3fff0007 0xe1fffe03c3fff000

def z744 : W := mkw 0x723fe3133ede8552 0xe723fe3133ede855 0x62352733336387f9 0x362352733336387f

def z745 : W := mkw 0x442ca82c2a2a28a4 0xb442ca82c2a2a28a 0xf44cf83c0f1ff8fa 0x2f44cf83c0f1ff8f

def z746 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xfffffffff3ff0005 0x3fffffffff3ff000

def z747 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0xfd8effffc0000000 0x3fd8effffc000000

def z748 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffcfff0007 0xfffffffffcfff000

def z749 : W := mkw 0x3813b5c015cad608 0x63813b5c015cad60 0xf843ffc000ffff0c 0x1f843ffc000ffff0

def z750 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xfffffffffcfc0007 0xffffffffffcfc000

def z751 : W := mkw 0x190001454531f7c8 0x0190001454531f7c 0x000000000000ffc8 0x0000000000000ffc

def z752 : W := mkw 0x813ffeffc13163c0 0xf813ffeffc13163c 0x417adf30037367cf 0x4417adf30037367c

def z753 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbfcd20cfcf7367cf 0xfbfcd20cfcf7367c

def z754 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe0301fffc0000000 0x3e0301fffc000000

def z755 : W := mkw 0xc03ffebaaa0a0000 0xfc03ffebaaa0a000 0xffbfffffcc0c0000 0x3ffbfffffcc0c000

def z756 : W := mkw 0x613fa0457bfb63c0 0xe613fa0457bfb63c 0xa13ac0cffc8c67c8 0xba13ac0cffc8c67c

def z757 : W := mkw 0x603fbca83aca0000 0xf603fbca83aca000 0xfffffffc3fff0007 0xffffffffc3fff000

def z758 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe63c1fc03f00ff0b 0x1e63c1fc03f00ff0

def z759 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x140de7cfc0000000 0x1140de7cfc000000

def z760 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xffbedfc03f00ff0b 0xdffbedfc03f00ff0

def z761 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xd73fffffc0000000 0x1d73fffffc000000

def z762 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc0800004 0xfffbfffffc080000

def z763 : W := mkw 0x601300003aca0000 0x4601300003aca000 0x1ffbc0003fff0007 0xc1ffbc0003fff000

def z764 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x453c1fc03f00ff0b 0xd453c1fc03f00ff0

def z765 : W := mkw 0x5a2cf7d32f1ed75a 0xa5a2cf7d32f1ed75 0x144ce7c30f1f0702 0x1144ce7c30f1f070

def z766 : W := mkw 0x923fbda984148552 0xf923fbda98414855 0x827538cccc9c87fe 0xc827538cccc9c87f

def z767 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xefbc1fc03f00ffcf 0xfefbc1fc03f00ffc

def z768 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xeab1183c3060f8fd 0x6eab1183c3060f8f

def z769 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe3b2183030e0f8fd 0xce3b2183030e0f8f

def z770 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0003f7f0003 0x01fffe0003f7f000

def z771 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x413218303080f8f8 0x8413218303080f8f

def z772 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0x1ffff8003fff1807 0xc1ffff8003fff180

def z773 : W := mkw 0xc83ffebaaa001008 0xfc83ffebaaa00100 0xffbffffff0001800 0x3ffbffffff000180

def z774 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebf3183c33f3f8ff 0xeebf3183c33f3f8f

def z775 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe3b2183c3080f8f9 0xee3b2183c3080f8f

def z776 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x1fcfe0000fff0007 0xc1fcfe0000fff000

def z777 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0x1fffe0303fff0037 0xc1fffe0303fff003

def z778 : W := mkw 0x80135eba80000000 0x580135eba8000000 0xe1321fffc0000000 0x3e1321fffc000000

def z779 : W := mkw 0x01000045413163c0 0x001000045413163c 0x9ec520cfc3736707 0x59ec520cfc373670

def z780 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0003fff80ff 0xc1fffe0003fff80f

def z781 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe030183c3000f8f8 0x2e030183c3000f8f

def z782 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfffff83c3ffff8ff 0xefffff83c3ffff8f

def z783 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0x600007330000e7f8 0x3600007330000e7f

def z784 : W := mkw 0xd813eb7aaf00d608 0x7d813eb7aaf00d60 0x1803e03fff00ff0b 0xe1803e03fff00ff0

def z785 : W := mkw 0xe03fbca8baca0000 0xfe03fbca8baca000 0xbffff8cfffff0007 0xfbffff8cfffff000

def z786 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe0001fffc00080f8 0x3e0001fffc00080f

def z787 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x17fce0003fff0007 0xc17fce0003fff000

def z788 : W := mkw 0x27134a3f50f529f6 0x527134a3f50f529f 0x1843e03fc0ff00f4 0x21843e03fc0ff00f

def z789 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xefbe1fc03f80ff0f 0xdefbe1fc03f80ff0

def z790 : W := mkw 0x2413a82c10ea28a4 0x72413a82c10ea28a 0xfffbf83c3cfff8ff 0xefffbf83c3cfff8f

def z791 : W := mkw 0x802c5eba80000000 0x9802c5eba8000000 0xffbedfffc0000000 0x3ffbedfffc000000

def z792 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xffbfffffc0e00004 0x3ffbfffffc0e0000

def z793 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe7bedfffc0000000 0x3e7bedfffc000000

def z794 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffffffffff730007 0xfffffffffff73000

def z795 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xffb3183f30e0f8fd 0xfffb3183f30e0f8f

def z796 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe2053fffc0000000 0x3e2053fffc000000

def z797 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcac7333c9cffff 0xf7dcac7333c9cfff

def z798 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe5b81fc03c00ff0a 0xde5b81fc03c00ff0

def z799 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcee7f3cc9c87fe 0xf7dcee7f3cc9c87f

def z800 : W := mkw 0x2513086951d14b64 0x52513086951d14b6 0x557638f3f3939f32 0x9557638f3f3939f3

def z801 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xf7bc3fc3ff00ff0b 0xdf7bc3fc3ff00ff0

def z802 : W := mkw 0xa03ffeba90ca0000 0xfa03ffeba90ca000 0xffffffffccff0006 0xfffffffffccff000

def z803 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec520cff373ffcf 0xfbec520cff373ffc

def z804 : W := mkw 0x36134b3f14f4adf6 0x536134b3f14f4adf 0x9679df0f3c7c7f03 0x19679df0f3c7c7f0

def z805 : W := mkw 0x6013a0003aca0000 0x66013a0003aca000 0x1dcbe0003fff0007 0xc1dcbe0003fff000

def z806 : W := mkw 0x1200431304148552 0x0120043130414855 0x7c4ac7330c9c87fe 0x37c4ac7330c9c87f

def z807 : W := mkw 0x803ff69280000000 0xe803ff6928000000 0xbfbfe7cfc0000000 0x3bfbfe7cfc000000

def z808 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x4933183c30e0f8fd 0xe4933183c30e0f8f

def z809 : W := mkw 0x6013a0003aca0000 0x66013a0003aca000 0x0042c0003fff0007 0xc0042c0003fff000

def z810 : W := mkw 0x603fb4803aca0000 0xe603fb4803aca000 0xffffffcfffff0007 0xfffffffcfffff000

def z811 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0xffbffffff080f839 0xfffbffffff080f83

def z812 : W := mkw 0x580015c02f00d608 0x0580015c02f00d60 0xe3b01fc03f00ff0b 0xde3b01fc03f00ff0

def z813 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0x004000000373e7ff 0x4004000000373e7f

def z814 : W := mkw 0x2413a82c10ea28a4 0x72413a82c10ea28a 0xebb3383c30e3f8fd 0xeebb3383c30e3f8f

def z815 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb7383c33e3f8fd 0xeebb7383c33e3f8f

def z816 : W := mkw 0x1200431304148552 0x0120043130414855 0x410ac7300c8c87f8 0x8410ac7300c8c87f

def z817 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe3b41fc03300ff09 0xde3b41fc03300ff0

def z818 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffc3130002 0x3ffffffffc313000

def z819 : W := mkw 0x0413082c002028a4 0x50413082c002028a 0xebb3183c3000f8f9 0xeebb3183c3000f8f

def z820 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0xe008dfffc0000000 0x3e008dfffc000000

def z821 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb318fff0e0f8fd 0xfebb318fff0e0f8f

def z822 : W := mkw 0x1200431304148552 0x0120043130414855 0x1dcac7330c9c07f6 0xf1dcac7330c9c07f

def z823 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x1fbfe7ffc0000000 0x31fbfe7ffc000000

def z824 : W := mkw 0xe0005ebabaca0000 0x1e0005ebabaca000 0xe0401fffffff0007 0xfe0401fffffff000

def z825 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe933183c30e0f8fc 0xae933183c30e0f8f

def z826 : W := mkw 0x84005eba80000824 0x184005eba8000082 0xe0001fffc0009830 0x3e0001fffc000983

def z827 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xfdcadfffcc9c0006 0xffdcadfffcc9c000

def z828 : W := mkw 0x6013a0003aca0000 0x66013a0003aca000 0x1bf3e0003fff0007 0xc1bf3e0003fff000

def z829 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bedfc03f8cff0b 0xde7bedfc03f8cff0

def z830 : W := mkw 0x130043564525e692 0x0130043564525e69 0xc30fe7fccfefe031 0x8c30fe7fccfefe03

def z831 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x144ce0000f7f0007 0x4144ce0000f7f000

def z832 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffffffffffff80ff 0xfffffffffffff80f

def z833 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x7d8fe7ffc0000000 0x37d8fe7ffc000000

def z834 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffbfffffff00f80b 0xfffbfffffff00f80

def z835 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fc03f80ffff 0xde7bc1fc03f80fff

def z836 : W := mkw 0x803fbca880000000 0xf803fbca88000000 0xffbd3fcfc0000000 0x3ffbd3fcfc000000

def z837 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xffbd3fc03f00ff0b 0xdffbd3fc03f00ff0

def z838 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbef538cff3737fcf 0x7bef538cff3737fc

def z839 : W := mkw 0x2013000010c00000 0x42013000010c0000 0xebb3183030e0f8fd 0xeebb3183030e0f8f

def z840 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xfeb53fffc0000000 0x3feb53fffc000000

def z841 : W := mkw 0x002c14c001004200 0x8002c14c00100420 0xe7bc1fc03300ff0b 0xde7bc1fc03300ff0

def z842 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bd3fccff00ff0b 0xde7bd3fccff00ff0

def z843 : W := mkw 0xe03fb480baca0000 0xee03fb480baca000 0x1fffe0c0ffff0007 0xc1fffe0c0ffff000

def z844 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xe2353ffff3630001 0x3e2353ffff363000

def z845 : W := mkw 0x80005eba80000000 0x180005eba8000000 0x80001fcfc0000000 0x180001fcfc000000

def z846 : W := mkw 0x2400000410e028a4 0x02400000410e028a 0xebb2183030e0f8fd 0xeebb2183030e0f8f

def z847 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfbf3d83c30fcf8fd 0xefbf3d83c30fcf8f

def z848 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x1842c0003fff0007 0xc1842c0003fff000

def z849 : W := mkw 0x01000045413163c0 0x001000045413163c 0xfff738fff3f3ffff 0xffff738fff3f3fff

def z850 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffc0100006 0x7ffffffffc010000

def z851 : W := mkw 0x603fb4803aca0000 0xe603fb4803aca000 0x1fffe7c03fff0007 0xd1fffe7c03fff000

def z852 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe0301fc03000ff08 0x1e0301fc03000ff0

def z853 : W := mkw 0xf23fffbabece8412 0xff23fffbabece841 0x413adf303c8c8030 0x8413adf303c8c803

def z854 : W := mkw 0x592c01456f31f7c8 0x8592c01456f31f7c 0x1ffd20003f73ffcf 0xc1ffd20003f73ffc

def z855 : W := mkw 0x5a2c15c02f04d61a 0x85a2c15c02f04d61 0xe7bc1fc03f8cff3b 0xde7bc1fc03f8cff3

def z856 : W := mkw 0x01000045413163c0 0x001000045413163c 0x9e4520cfc37367c7 0x39e4520cfc37367c

def z857 : W := mkw 0x003f1ca800000000 0xd003f1ca80000000 0xffbf3fffc0000000 0x3ffbf3fffc000000

def z858 : W := mkw 0xc02cf692aa0a0000 0xac02cf692aa0a000 0xbecde7cfcf7f0007 0x7becde7cfcf7f000

def z859 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x82353fcfc0000000 0x182353fcfc000000

def z860 : W := mkw 0x5b2c57d36f15d75a 0x85b2c57d36f15d75 0x144ce7c3cf1f0702 0x1144ce7c3cf1f070

def z861 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xf63dffffc0000000 0x3f63dffffc000000

def z862 : W := mkw 0x1000010004008400 0x0100001000400840 0x7dcac7300c9c87fe 0xf7dcac7300c9c87f

def z863 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbffffff3e30005 0xfffbffffff3e3000

def z864 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1efde0003f7f0007 0x41efde0003f7f000

def z865 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x157ee0003fff0007 0xc157ee0003fff000

def z866 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfff3183c30f0f8ff 0xefff3183c30f0f8f

def z867 : W := mkw 0xe43ffebabaca0824 0xfe43ffebabaca082 0xffffffffffff9837 0xfffffffffffff983

def z868 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xfffff8303ffff8ff 0xefffff8303ffff8f

def z869 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x144ce0000fff0006 0x0144ce0000fff000

def z870 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffcc8c0000 0xbffbfffffcc8c000

def z871 : W := mkw 0x803ffeba800a0000 0xf803ffeba800a000 0xffffffffc01f0000 0x3ffffffffc01f000

def z872 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe3b1183c3060f8f9 0xee3b1183c3060f8f

def z873 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x3fffe0003fff070f 0xd3fffe0003fff070

def z874 : W := mkw 0x0000421200000000 0x0000042120000000 0xffcfe7ffcfff0007 0xfffcfe7ffcfff000

def z875 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0x5ffff8303fff0007 0xc5ffff8303fff000

def z876 : W := mkw 0x0500004541316be4 0x00500004541316be 0xbec520cfc373ffff 0x7bec520cfc373fff

def z877 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xe230183c3000f8f9 0x2e230183c3000f8f

def z878 : W := mkw 0x01000045413163c0 0x001000045413163c 0xaa8520cfc36367cd 0x7aa8520cfc36367c

def z879 : W := mkw 0x1200431304148552 0x0120043130414855 0x5dcac7300c9c87fe 0xc5dcac7300c9c87f

def z880 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xfffc1fc03f10ff0f 0xdfffc1fc03f10ff0

def z881 : W := mkw 0xa0135eba90c00000 0x5a0135eba90c0000 0xebb31ffff0e00005 0xfebb31ffff0e0000

def z882 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x69b2183030e0f8fd 0xe69b2183030e0f8f

def z883 : W := mkw 0xc02c5ebaaa000000 0x9c02c5ebaaa00000 0xe7bc1fffff000003 0xfe7bc1fffff00000

def z884 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe33c1fc03f00ff09 0x9e33c1fc03f00ff0

def z885 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x7fffe7003fff0007 0xd7fffe7003fff000

def z886 : W := mkw 0x1200431304148552 0x0120043130414855 0xffcfe7ffcfff87ff 0xfffcfe7ffcfff87f

def z887 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xffbc1fc33f00ff0b 0xfffbc1fc33f00ff0

def z888 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1ff03f00fffb 0xfe7bc1ff03f00fff

def z889 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0xfe8dffffc0000000 0x3fe8dffffc000000

def z890 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffffffffff9c0007 0xfffffffffff9c000

def z891 : W := mkw 0xe03fa828baca0000 0xfe03fa828baca000 0x1fffe00cffff0007 0xc1fffe00cffff000

def z892 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x197be0003fff0007 0xc197be0003fff000

def z893 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xfc801fffc0000000 0x3fc801fffc000000

def z894 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffffffffff9f0002 0xbffffffffff9f000

def z895 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffbffffffc000000 0xbffbffffffc00000

def z896 : W := mkw 0x1200431304148552 0x0120043130414855 0x3ccac7330c9c07fe 0x73ccac7330c9c07f

def z897 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe9821fffc0000000 0x3e9821fffc000000

def z898 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x037fe0003fff0007 0xc037fe0003fff000

def z899 : W := mkw 0x8013ea3a80000000 0x78013ea3a8000000 0xff8fe7ffc0000000 0x3ff8fe7ffc000000

def z900 : W := mkw 0x2513082c50e128a4 0x52513082c50e128a 0xebb3383cf0e3f8fd 0xeebb3383cf0e3f8f

def z901 : W := mkw 0x01000045413163c0 0x001000045413163c 0x3cc520cfc37307ce 0x73cc520cfc37307c

def z902 : W := mkw 0x6013a0003aca0000 0x66013a0003aca000 0x1843e0000fff0006 0x01843e0000fff000

def z903 : W := mkw 0x1200431304148552 0x0120043130414855 0xffcbc73f0c9c87fe 0xfffcbc73f0c9c87f

def z904 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbe8520cfc36367c9 0x3be8520cfc36367c

def z905 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0xf7bcffffc0000000 0x3f7bcffffc000000

def z906 : W := mkw 0x7c3f1dec3fe0feac 0xd7c3f1dec3fe0fea 0x0c0f07fc0fe007f6 0x30c0f07fc0fe007f

def z907 : W := mkw 0x1200431304148552 0x0120043130414855 0x594ac7330c9c87fe 0xe594ac7330c9c87f

def z908 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xffbffffff0e0f80d 0xfffbffffff0e0f80

def z909 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x41381f003c00ff08 0x841381f003c00ff0

def z910 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xefbe1ff03f00ff0b 0xfefbe1ff03f00ff0

def z911 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbff520cff37367cf 0xfbff520cff37367c

def z912 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xf408dfffc0000000 0x3f408dfffc000000

def z913 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xea33183c30e0f8fd 0x2ea33183c30e0f8f

def z914 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xebb73fffc0000000 0x3ebb73fffc000000

def z915 : W := mkw 0x1200431304148552 0x0120043130414855 0x7fcbc7330cfc87ff 0xf7fcbc7330cfc87f

def z916 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x1ecde0003fff0007 0xc1ecde0003fff000

def z917 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb738fcf0e0f8fd 0xeebb738fcf0e0f8f

def z918 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xf7fcdfc03f1cff0b 0xdf7fcdfc03f1cff0

def z919 : W := mkw 0xd82cb5c0af00d608 0xad82cb5c0af00d60 0xe7bc3fc0ff00ff0b 0xde7bc3fc0ff00ff0

def z920 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xfffffffffffff80f 0xffffffffffffff80

def z921 : W := mkw 0x683fb4803aca1008 0xe683fb4803aca100 0x1ffff8003fff1807 0xc1ffff8003fff180

def z922 : W := mkw 0x190001454531f7c8 0x0190001454531f7c 0x004000000373ffcf 0x4004000000373ffc

def z923 : W := mkw 0x402c00002a000000 0x8402c00002a00000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z924 : W := mkw 0x80135eba80000000 0x580135eba8000000 0xe8031fffc0000000 0x3e8031fffc000000

def z925 : W := mkw 0x730001457fffe7d2 0x0730001457fffe7d 0x004000003fffe7ff 0xc004000003fffe7f

def z926 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc00080f8 0x3ffbfffffc00080f

def z927 : W := mkw 0xc03ffebaaa0a0000 0xfc03ffebaaa0a000 0xffffffffcf9f0006 0xfffffffffcf9f000

def z928 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xfffffffffc9c0006 0xffffffffffc9c000

def z929 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x7fffe0303fff0007 0xe7fffe0303fff000

def z930 : W := mkw 0x6013a0003aca0000 0x66013a0003aca000 0x1ec7e0003fff0007 0xc1ec7e0003fff000

def z931 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbffffff0000001 0xfffbffffff000000

def z932 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe7b81fc03c00ff0b 0xde7b81fc03c00ff0

def z933 : W := mkw 0xe03ffebabac00000 0xfe03ffebabac0000 0xffbfffffffe00007 0xfffbfffffffe0000

def z934 : W := mkw 0x582cb5c02f0ad608 0xa582cb5c02f0ad60 0xfffeffc03f9fff0f 0xdfffeffc03f9fff0

def z935 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7fc1fc03f9cff0f 0xde7fc1fc03f9cff0

def z936 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0x4bb3183030e0f8fd 0xc4bb3183030e0f8f

def z937 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe33fffffc0000000 0x3e33fffffc000000

def z938 : W := mkw 0x0000148000000000 0x0000014800000000 0xe0001fcfc0000000 0x3e0001fcfc000000

def z939 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xffffffc03fffff0f 0xdffffffc03fffff0

def z940 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfbf3383c30f3f8fd 0xefbf3383c30f3f8f

def z941 : W := mkw 0x80135eba80000000 0x580135eba8000000 0xffb73fffc0000000 0x3ffb73fffc000000

def z942 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffffffffcfff0006 0x3ffffffffcfff000

def z943 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc3630001 0x3ffbfffffc363000

def z944 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xffbffffff0600001 0x3ffbffffff060000

def z945 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb3183c3080f8fd 0xeebb3183c3080f8f

def z946 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xffbbd83c30e0f8fd 0xeffbbd83c30e0f8f

def z947 : W := mkw 0x603fb4803aca0000 0xe603fb4803aca000 0x5fffff003fff0007 0xc5fffff003fff000

def z948 : W := mkw 0x0000421200000000 0x0000042120000000 0xe00007ffc0000000 0x3e00007ffc000000

def z949 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbfffffffef0001 0xbffbfffffffef000

def z950 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0x9fffffcfffff0007 0xd9fffffcfffff000

def z951 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xe13adffffc8c0000 0xbe13adffffc8c000

def z952 : W := mkw 0x01000045413163c0 0x001000045413163c 0x9a4520cfc37367cf 0x69a4520cfc37367c

def z953 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xfdbadfffc0000000 0x3fdbadfffc000000

def z954 : W := mkw 0x843ffeba80000824 0xf843ffeba8000082 0xffbfffffc0009830 0x3ffbfffffc000983

def z955 : W := mkw 0x002c148000000000 0x8002c14800000000 0xbe8d27cfc0000000 0x3be8d27cfc000000

def z956 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0x1fcfe0000fffe7ff 0xc1fcfe0000fffe7f

def z957 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xebb1183c3060f8fd 0xeebb1183c3060f8f

def z958 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0x9ffff80c3fff0007 0xc9ffff80c3fff000

def z959 : W := mkw 0x110001454531e7c0 0x0110001454531e7c 0x004000000f73e7cf 0xc004000000f73e7c

def z960 : W := mkw 0xe03fbca8baca0000 0xfe03fbca8baca000 0x1ffff8003fff0007 0xc1ffff8003fff000

def z961 : W := mkw 0x2413a82c10ea28a4 0x72413a82c10ea28a 0xfff7f83c33fff8ff 0xefff7f83c33fff8f

def z962 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7be1ff03f80ff3b 0xde7be1ff03f80ff3

def z963 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec520cfcfff67cf 0xfbec520cfcfff67c

def z964 : W := mkw 0x1200431304148552 0x0120043130414855 0xfffadf330c9c87fe 0xffffadf330c9c87f

def z965 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xefb3183c30e0ffff 0xfefb3183c30e0fff

def z966 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xffb7383c30e0f8fd 0xeffb7383c30e0f8f

def z967 : W := mkw 0x8013feba80000000 0x78013feba8000000 0xe0013fffc0000000 0x3e0013fffc000000

def z968 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x87bc1fc03f007f03 0xd87bc1fc03f007f0

def z969 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0xffbffffff08098fc 0xfffbffffff08098f

def z970 : W := mkw 0x0000000000000000 0x0000000000000000 0xff8d27cfc0000000 0x3ff8d27cfc000000

def z971 : W := mkw 0xa03ffeba90ca0000 0xfa03ffeba90ca000 0xffffffffc3ff0007 0x7ffffffffc3ff000

def z972 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1ecfe0000fff0007 0x41ecfe0000fff000

def z973 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc0600005 0x7ffbfffffc060000

def z974 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbecde0cfcf7f67cf 0x7becde0cfcf7f67c

def z975 : W := mkw 0x01000045413163c0 0x001000045413163c 0x820520cfc3636701 0x1820520cfc363670

def z976 : W := mkw 0xa03ffeba90ca0000 0xfa03ffeba90ca000 0xffbfffffc0630000 0x3ffbfffffc063000

def z977 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xf7fc3fc03f13ff0b 0xdf7fc3fc03f13ff0

def z978 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec720ffc3f367ff 0x7bec720ffc3f367f

def z979 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xfffd3fcfff73ff0f 0xffffd3fcfff73ff0

def z980 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xff8fffffc0000000 0x3ff8fffffc000000

def z981 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe10adfffc0000000 0x3e10adfffc000000

def z982 : W := mkw 0x590001456f31f7c8 0x0590001456f31f7c 0x004000000f7367cf 0x4004000000f7367c

def z983 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xefbd1fcc3f00ff0b 0xfefbd1fcc3f00ff0

def z984 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1c4fe0003fff0007 0xc1c4fe0003fff000

def z985 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe3b81f003f00ff0b 0xce3b81f003f00ff0

def z986 : W := mkw 0x790001457ffbf7c8 0x0790001457ffbf7c 0x004000003fffffcf 0xc004000003fffffc

def z987 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x863c1fc03f00ff0b 0xd863c1fc03f00ff0

def z988 : W := mkw 0x1200431304148552 0x0120043130414855 0x7fcfe7330c9c87fe 0xf7fcfe7330c9c87f

def z989 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0xb40ce7cfc0000000 0x3b40ce7cfc000000

def z990 : W := mkw 0x602c00003aca0000 0x8602c00003aca000 0x1ffec0003fff0007 0xc1ffec0003fff000

def z991 : W := mkw 0xe03fbca8baca0000 0xfe03fbca8baca000 0xffffffccffff0007 0xdffffffccffff000

def z992 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xbe8fe7ffc0000000 0x3be8fe7ffc000000

def z993 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebf3183c3cfcf8ff 0xeebf3183c3cfcf8f

def z994 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc0808030 0xbffbfffffc080803

def z995 : W := mkw 0x01000045413163c0 0x001000045413163c 0x144520cfc3730702 0x1144520cfc373070

def z996 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x5d3fffffc0000000 0x35d3fffffc000000

def z997 : W := mkw 0x582cb5c02f0ad608 0xa582cb5c02f0ad60 0xfffdffc03f7fff0f 0xdfffdffc03f7fff0

def z998 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xfffffffff3730007 0x7fffffffff373000

def z999 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xfec53fffc3730007 0x7fec53fffc373000

def z1000 : W := mkw 0x80005eba80000000 0x180005eba8000000 0x000007ffc0000000 0x3000007ffc000000

def z1001 : W := mkw 0x482c14c02b005208 0x8482c14c02b00520 0xe7bc1fc033007f0b 0x5e7bc1fc033007f0

def z1002 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x1c4de0000f7f0006 0x01c4de0000f7f000

def z1003 : W := mkw 0x130043574535e7d2 0x0130043574535e7d 0xa00007cfc00067c8 0x3a00007cfc00067c

def z1004 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe333183c30e0f8f9 0xae333183c30e0f8f

def z1005 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0303fff00f7 0xe1fffe0303fff00f

def z1006 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbffffff0007801 0x3ffbffffff000780

def z1007 : W := mkw 0x01000045413163c0 0x001000045413163c 0xba4520cfc37367cd 0x3ba4520cfc37367c

def z1008 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0x140ce7ffc0000000 0x3140ce7ffc000000

def z1009 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec520cfc3736703 0x3bec520cfc373670

def z1010 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1dcfe0000fff0006 0xc1dcfe0000fff000

def z1011 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x47bc1f003f00ff0b 0xc47bc1f003f00ff0

def z1012 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xbfffe00c3fff0007 0xebfffe00c3fff000

def z1013 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbffffff0009800 0xbffbffffff000980

def z1014 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffcc1c0002 0x3ffffffffcc1c000

def z1015 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0x004000000c9ce7fe 0xc004000000c9ce7f

def z1016 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1a77e0003fff0007 0xc1a77e0003fff000

def z1017 : W := mkw 0x582cb5c02f00d608 0xa582cb5c02f00d60 0xf7bcffc03f00ff0b 0xdf7bcffc03f00ff0

def z1018 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe0001fffc000f808 0x3e0001fffc000f80

def z1019 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x3fffe0003fff00cf 0xe3fffe0003fff00c

def z1020 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dfadf333c9c9ffe 0xf7dfadf333c9c9ff

def z1021 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x1dcee0003fff0007 0xc1dcee0003fff000

def z1022 : W := mkw 0x1200431304148552 0x0120043130414855 0xffcec7f30c9c87fe 0xfffcec7f30c9c87f

def z1023 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe0000fff0007 0xc1fffe0000fff000

def z1024 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xbfffe0c03fff0007 0xdbfffe0c03fff000

def z1025 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcac7330c9c07f6 0x37dcac7330c9c07f

def z1026 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z1027 : W := mkw 0x1200431304148552 0x0120043130414855 0x7fcec7330f9c87ff 0xf7fcec7330f9c87f

def z1028 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbfc720cfc3f367cf 0xfbfc720cfc3f367c

def z1029 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x17fde0003f7f0003 0xc17fde0003f7f000

def z1030 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0x960de7cfc0000000 0x1960de7cfc000000

def z1031 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe7b41fc03300ff0b 0xde7b41fc03300ff0

def z1032 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1e7fe0003fff0007 0x01e7fe0003fff000

def z1033 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0xe0043fffc0000000 0x3e0043fffc000000

def z1034 : W := mkw 0x1200431304148552 0x0120043130414855 0x554ac7330c9c87fe 0xd554ac7330c9c87f

def z1035 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xf8013fffc0000000 0x3f8013fffc000000

def z1036 : W := mkw 0x1b0057d74535f7da 0x01b0057d74535f7d 0xe0001fffc000fff8 0x3e0001fffc000fff

def z1037 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfbb3383ff0e0f8fd 0xefbb3383ff0e0f8f

def z1038 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0x967dffcfff7f0003 0x1967dffcfff7f000

def z1039 : W := mkw 0xa013feba90ca0000 0x7a013feba90ca000 0xf843ffffc0ff0004 0x3f843ffffc0ff000

def z1040 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xfff738fff3f3f8ff 0xffff738fff3f3f8f

def z1041 : W := mkw 0xe43ffebabaca0824 0xfe43ffebabaca082 0xffbffffffc8c9830 0xbffbffffffc8c983

def z1042 : W := mkw 0x002c569200000000 0x8002c56920000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z1043 : W := mkw 0x2413082c10ea28a4 0x52413082c10ea28a 0xebf3183c30fff8fd 0xeebf3183c30fff8f

def z1044 : W := mkw 0x93005fffc535e7d2 0x193005fffc535e7d 0xe0001fffc000e7f8 0x3e0001fffc000e7f

def z1045 : W := mkw 0xc03ffebaaa0a0000 0xfc03ffebaaa0a000 0xffffffffcf7f0007 0x7ffffffffcf7f000

def z1046 : W := mkw 0x8013feba80000000 0x78013feba8000000 0xfbb3ffffc0000000 0x3fbb3ffffc000000

def z1047 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbfcfe0cfc37367cf 0x7bfcfe0cfc37367c

def z1048 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0x1c4fe7ffcfff0006 0x31c4fe7ffcfff000

def z1049 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xc73c1fc03f00ff03 0x9c73c1fc03f00ff0

def z1050 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe132183c30e0f8fd 0xee132183c30e0f8f

def z1051 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0xfffff83c3fff9837 0xefffff83c3fff983

def z1052 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x9fffe0ccffff0007 0xc9fffe0ccffff000

def z1053 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x9fbfffcfc0000000 0x19fbfffcfc000000

def z1054 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x0048c0003fff0007 0xc0048c0003fff000

def z1055 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe3b81fc03c00ff09 0xde3b81fc03c00ff0

def z1056 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe2341fc03f00ff0b 0xde2341fc03f00ff0

def z1057 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0000fff0006 0x01fffe0000fff000

def z1058 : W := mkw 0x582cb5c02f0ad608 0xa582cb5c02f0ad60 0xe7bcdfc03f0cff0b 0xde7bcdfc03f0cff0

def z1059 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbffffffcec0005 0xfffbffffffcec000

def z1060 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0x7ffff8303fff98ff 0xe7ffff8303fff98f

def z1061 : W := mkw 0x01000045413163c0 0x001000045413163c 0x964520cfc37367cf 0x5964520cfc37367c

def z1062 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xebb2183c3080f8fd 0xeebb2183c3080f8f

def z1063 : W := mkw 0x803f5eba80000000 0xd803f5eba8000000 0xefbf1fffc0000000 0x3efbf1fffc000000

def z1064 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xfa37ffffc0000000 0x3fa37ffffc000000

def z1065 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xbebdffcfc0000000 0x3bebdffcfc000000

def z1066 : W := mkw 0x80135eba80000000 0x580135eba8000000 0xe2311fffc0000000 0x3e2311fffc000000

def z1067 : W := mkw 0x1200431304148552 0x0120043130414855 0x614ac7330c9c87fe 0xf614ac7330c9c87f

def z1068 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fc03300ff09 0x1e7bc1fc03300ff0

def z1069 : W := mkw 0x17004b7f4535eff6 0x117004b7f4535eff 0xe0001fffc000fff8 0x3e0001fffc000fff

def z1070 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0x000000000000e7f8 0x0000000000000e7f

def z1071 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffbffffff3000001 0x3ffbffffff300000

def z1072 : W := mkw 0x1200431304148552 0x0120043130414855 0x7ffac7333c9c87ff 0xf7ffac7333c9c87f

def z1073 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1d7fe0003fff0006 0x81d7fe0003fff000

def z1074 : W := mkw 0x1200431304148552 0x0120043130414855 0x754ac7330c9c87fa 0xb754ac7330c9c87f

def z1075 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1fcfe0000fff0007 0xc1fcfe0000fff000

def z1076 : W := mkw 0x7d0001457ff1ffec 0x07d0001457ff1ffe 0x004000003ff3ffff 0xc004000003ff3fff

def z1077 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc0006009 0x7ffbfffffc000600

def z1078 : W := mkw 0x0000000400202080 0x0000000040020208 0xebb3183c30e0f8fd 0xeebb3183c30e0f8f

def z1079 : W := mkw 0xa03ffeba90ca0000 0xfa03ffeba90ca000 0xffbfffffc08c0000 0x3ffbfffffc08c000

def z1080 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebbbd83c3cecf8fd 0xeebbbd83c3cecf8f

def z1081 : W := mkw 0x003fb48000000000 0xe003fb4800000000 0xffbfffcfc0000000 0x3ffbfffcfc000000

def z1082 : W := mkw 0xc03ffebaaa0a0000 0xfc03ffebaaa0a000 0xffffffffff1f0003 0xfffffffffff1f000

def z1083 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe1301fc03000ff08 0x9e1301fc03000ff0

def z1084 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe1381fc03f00ff0b 0xde1381fc03f00ff0

def z1085 : W := mkw 0x01000045413163c0 0x001000045413163c 0xfec520ffc373e7ff 0x7fec520ffc373e7f

def z1086 : W := mkw 0x01000045413163c0 0x001000045413163c 0xffc720ffc37367cf 0x7ffc720ffc37367c

def z1087 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc08000f4 0x3ffbfffffc08000f

def z1088 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xdb3fffffc0000000 0x2db3fffffc000000

def z1089 : W := mkw 0x102c158004008400 0x8102c15800400840 0xe7bc1fc03c00ff0b 0xde7bc1fc03c00ff0

def z1090 : W := mkw 0x01000045413163c0 0x001000045413163c 0xa68520cfc36367cb 0x7a68520cfc36367c

def z1091 : W := mkw 0x01000045413163c0 0x001000045413163c 0x1ec520cfc37307c7 0x71ec520cfc37307c

def z1092 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb3183c3080f8f8 0xaebb3183c3080f8f

def z1093 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0xff8fe7ffc0000000 0x3ff8fe7ffc000000

def z1094 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xea811fffc0000000 0x3ea811fffc000000

def z1095 : W := mkw 0x603fb4803aca0000 0xe603fb4803aca000 0x9ffff8c03fff0007 0xc9ffff8c03fff000

def z1096 : W := mkw 0x5a2c57d32f14d75a 0x85a2c57d32f14d75 0x040c07c30f000702 0x1040c07c30f00070

def z1097 : W := mkw 0x26134a3f10f429f6 0x526134a3f10f429f 0x0803003f00e000f4 0x20803003f00e000f

def z1098 : W := mkw 0x100001400500c600 0x0100001400500c60 0xe7bc1fc03f00ff0b 0xde7bc1fc03f00ff0

def z1099 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffffffffff7f0003 0x3ffffffffff7f000

def z1100 : W := mkw 0x582c15c02f0ad608 0x8582c15c02f0ad60 0xe7fc1fc03f1fff0b 0xde7fc1fc03f1fff0

def z1101 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ecde0000f7f0007 0x41ecde0000f7f000

def z1102 : W := mkw 0x402c14802a000000 0x8402c14802a00000 0xfffd3fcfff730007 0xffffd3fcfff73000

def z1103 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec520cfc3f3e7ff 0xfbec520cfc3f3e7f

def z1104 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xefbb183c3ce0f8ff 0xeefbb183c3ce0f8f

def z1105 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xfffffffff3f30007 0xffffffffff3f3000

def z1106 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xf93bffffc0000000 0x3f93bffffc000000

def z1107 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xebb3183c3060f8f9 0x2ebb3183c3060f8f

def z1108 : W := mkw 0x802c5eba80000000 0x9802c5eba8000000 0xe1381fffc0000000 0x3e1381fffc000000

def z1109 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xefbd1fc03f60ff0f 0xdefbd1fc03f60ff0

def z1110 : W := mkw 0xc03ffebaaa0a0000 0xfc03ffebaaa0a000 0xffbfffffc3030000 0x3ffbfffffc303000

def z1111 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbffffff0000000 0x3ffbffffff000000

def z1112 : W := mkw 0x1200431304148552 0x0120043130414855 0xfdcac7ffcc9c87fe 0xffdcac7ffcc9c87f

def z1113 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffcc000002 0xfffbfffffcc00000

def z1114 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec520cfc37307c6 0x3bec520cfc37307c

def z1115 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x144de0000f7f0002 0x0144de0000f7f000

def z1116 : W := mkw 0x0400082c002028a4 0x10400082c002028a 0xe130183c3000f8f8 0xae130183c3000f8f

def z1117 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe3b01fffc0000000 0x3e3b01fffc000000

def z1118 : W := mkw 0x1300431344158552 0x0130043134415855 0x7dcae733cc9f87fe 0xf7dcae733cc9f87f

def z1119 : W := mkw 0x1200431304148552 0x0120043130414855 0x69cac7300c9c87fe 0xe69cac7300c9c87f

def z1120 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xf802dfffc0000000 0x3f802dfffc000000

def z1121 : W := mkw 0x8013feba80000000 0x78013feba8000000 0xe002dfffc0000000 0x3e002dfffc000000

def z1122 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffc0730004 0x3ffffffffc073000

def z1123 : W := mkw 0x3413092c14e0aca4 0x53413092c14e0aca 0x6d8b073c0ce087fe 0xf6d8b073c0ce087f

def z1124 : W := mkw 0x01000045413163c0 0x001000045413163c 0xfec538cfc373ffcf 0x7fec538cfc373ffc

def z1125 : W := mkw 0x1200431304148552 0x0120043130414855 0x794ac7330c9c87fc 0xb794ac7330c9c87f

def z1126 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x1448c0003fff0007 0xc1448c0003fff000

def z1127 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x82341fc033007f01 0x182341fc033007f0

def z1128 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x9ffff8003fff7807 0xc9ffff8003fff780

def z1129 : W := mkw 0xa513ea3fd0f129e4 0x7a513ea3fd0f129e 0x1843e03fc0f300f4 0x21843e03fc0f300f

def z1130 : W := mkw 0x01000045413163c0 0x001000045413163c 0xffc520cfc373e7cf 0xfffc520cfc373e7c

def z1131 : W := mkw 0x502c01002e008400 0x8502c01002e00840 0xe7bc1f003f00ff0b 0xde7bc1f003f00ff0

def z1132 : W := mkw 0x643fa0003aca0824 0xe643fa0003aca082 0x1fffe0003fff9837 0xc1fffe0003fff983

def z1133 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xfffffffffcff0004 0xbfffffffffcff000

def z1134 : W := mkw 0x01000045413163c0 0x001000045413163c 0xffcfe0ffcfffe7ff 0xfffcfe0ffcfffe7f

def z1135 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe9b2183c3080f8fc 0xee9b2183c3080f8f

def z1136 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xfffff8003fff0007 0xcfffff8003fff000

def z1137 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xf4043fffc0000000 0x3f4043fffc000000

def z1138 : W := mkw 0x793fa1457ffbf7c8 0xe793fa1457ffbf7c 0x1fffe0003fffffcf 0xc1fffe0003fffffc

def z1139 : W := mkw 0x733fa1457fffe7d2 0xe733fa1457fffe7d 0x1fffe0003fffe7ff 0xc1fffe0003fffe7f

def z1140 : W := mkw 0x00134a3a00000000 0x500134a3a0000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z1141 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bc1fc03c00ff08 0x9e7bc1fc03c00ff0

def z1142 : W := mkw 0x802c5eba80000000 0x9802c5eba8000000 0xe2341fffc0000000 0x3e2341fffc000000

def z1143 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcbe7330cff87fe 0xf7dcbe7330cff87f

def z1144 : W := mkw 0x600000003aca0000 0x0600000003aca000 0x1fcfe0003fff0007 0xc1fcfe0003fff000

def z1145 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1b7fe0003fff0005 0x81b7fe0003fff000

def z1146 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0xbfffe0003fff600f 0xcbfffe0003fff600

def z1147 : W := mkw 0x8013feba80000000 0x78013feba8000000 0x1803e7ffc0000000 0x31803e7ffc000000

def z1148 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0x65b81f003f00ff0b 0xd65b81f003f00ff0

def z1149 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc0008008 0xfffbfffffc000800

def z1150 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xe231183c30e0f8fd 0xee231183c30e0f8f

def z1151 : W := mkw 0x003fe21200000000 0xe003fe2120000000 0xffbfe7ffc0000000 0x3ffbfe7ffc000000

def z1152 : W := mkw 0x603fe2123aca0000 0xe603fe2123aca000 0xffffe7ffffff0007 0xfffffe7ffffff000

def z1153 : W := mkw 0x2413a82c10e028a4 0x72413a82c10e028a 0xfbb3f83c30e0f8fd 0xefbb3f83c30e0f8f

def z1154 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x5ffff8003fff9807 0xc5ffff8003fff980

def z1155 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x1ffde0003f7f0007 0xc1ffde0003f7f000

def z1156 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0xfffff83c3ffff80f 0xefffff83c3ffff80

def z1157 : W := mkw 0x0000004001004200 0x0000000400100420 0xbec520cfc373670f 0x7bec520cfc373670

def z1158 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0xffbfffffc0800030 0x3ffbfffffc080003

def z1159 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xc33c1fc03f00ff0b 0xcc33c1fc03f00ff0

def z1160 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc000f808 0x3ffbfffffc000f80

def z1161 : W := mkw 0x590001456f31f7c8 0x0590001456f31f7c 0x000000003f00ffcb 0xc000000003f00ffc

def z1162 : W := mkw 0x01000045413163c0 0x001000045413163c 0xffcd27cfc37367cf 0x7ffcd27cfc37367c

def z1163 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xa6bc1fc03f007f0b 0x5a6bc1fc03f007f0

def z1164 : W := mkw 0x01000045413163c0 0x001000045413163c 0xfff538cfc37367cf 0x7fff538cfc37367c

def z1165 : W := mkw 0x2400082c10e028a4 0x12400082c10e028a 0xe3b0183c30e0f8fd 0xee3b0183c30e0f8f

def z1166 : W := mkw 0x802cf69280000000 0xa802cf6928000000 0xffbdffcfc0000000 0x3ffbdffcfc000000

def z1167 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1fffe0003ffff80f 0xc1fffe0003ffff80

def z1168 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xebbbdfffc0000000 0x3ebbbdfffc000000

def z1169 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe53c1fc03f00ff0a 0x9e53c1fc03f00ff0

def z1170 : W := mkw 0xa413a82c90e028a4 0x7a413a82c90e028a 0xebb3383cf0e0f8fd 0xeebb3383cf0e0f8f

def z1171 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcac7330fff87ff 0xf7dcac7330fff87f

def z1172 : W := mkw 0x6000a0003aca0000 0x26000a0003aca000 0x1040e0003fff0007 0xc1040e0003fff000

def z1173 : W := mkw 0x802c5eba80000000 0x9802c5eba8000000 0xffbd3fffc0000000 0x3ffbd3fffc000000

def z1174 : W := mkw 0x643fa8283aca0824 0xf643fa8283aca082 0xfffff8303ffff83f 0xcfffff8303ffff83

def z1175 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xe7bd3fffc0000000 0x3e7bd3fffc000000

def z1176 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xcb33183c30e0f8f5 0xacb33183c30e0f8f

def z1177 : W := mkw 0x03000045413563d2 0x003000045413563d 0xbec520cfc3ff67ff 0x7bec520cfc3ff67f

def z1178 : W := mkw 0xc03ffebaaa000000 0xfc03ffebaaa00000 0xffbfffffcf000002 0x3ffbfffffcf00000

def z1179 : W := mkw 0x6c3fbcec3bea7aac 0xf6c3fbcec3bea7aa 0x823538cc33637801 0x0823538cc3363780

def z1180 : W := mkw 0x582c15802e009408 0x8582c15802e00940 0xe7b81f003c00ff0b 0xde7b81f003c00ff0

def z1181 : W := mkw 0x01000045413163c0 0x001000045413163c 0x1c4520cfc37367cf 0x71c4520cfc37367c

def z1182 : W := mkw 0x8013feba80000000 0x78013feba8000000 0xfe87ffffc0000000 0x3fe87ffffc000000

def z1183 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe6841fffc0000000 0x3e6841fffc000000

def z1184 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc000070a 0x7ffbfffffc000070

def z1185 : W := mkw 0x002c148000000000 0x8002c14800000000 0xe7bc1fcfc0000000 0x3e7bc1fcfc000000

def z1186 : W := mkw 0x582cb5c02f0ad608 0xa582cb5c02f0ad60 0xe7bc3fc03f03ff0b 0xde7bc3fc03f03ff0

def z1187 : W := mkw 0xe03ffebabaca0000 0xfe03ffebabaca000 0xffbfffffff630003 0xfffbfffffff63000

def z1188 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xefbb1f3c30e0f8fd 0xfefbb1f3c30e0f8f

def z1189 : W := mkw 0x602ca0003aca0000 0xa602ca0003aca000 0x144ce0003f7f0003 0x0144ce0003f7f000

def z1190 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x1dfac0003fff0007 0xc1dfac0003fff000

def z1191 : W := mkw 0x1200431304148552 0x0120043130414855 0x1c4ac7330c9c87fe 0xf1c4ac7330c9c87f

def z1192 : W := mkw 0x1200431304148552 0x0120043130414855 0x658ac7330c8c87fa 0xf658ac7330c8c87f

def z1193 : W := mkw 0x8000569280000000 0x0800056928000000 0xa00007cfc0000000 0x3a00007cfc000000

def z1194 : W := mkw 0x8000569280000000 0x0800056928000000 0xbe8527cfc0000000 0x3be8527cfc000000

def z1195 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dcac0000fff0007 0xc1dcac0000fff000

def z1196 : W := mkw 0xa613ea3f90f429f6 0x7a613ea3f90f429f 0x1843e03fc0fc00f4 0x21843e03fc0fc00f

def z1197 : W := mkw 0xda2cf7d3af14d75a 0xada2cf7d3af14d75 0x144ce7c3cf1c0702 0x1144ce7c3cf1c070

def z1198 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x177fe0003fff0003 0x8177fe0003fff000

def z1199 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xf7bdffcfc0000000 0x1f7bdffcfc000000

def z1200 : W := mkw 0x180015c00500d608 0x0180015c00500d60 0xe2301fc03000ff09 0x1e2301fc03000ff0

def z1201 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbc4520cfc37367ce 0x3bc4520cfc37367c

def z1202 : W := mkw 0x2413082810c00824 0x52413082810c0082 0xebb218303080f8fd 0xeebb218303080f8f

def z1203 : W := mkw 0x0000421200000000 0x0000042120000000 0xfe8527ffc0000000 0x3fe8527ffc000000

def z1204 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xefb718fc30e0f8fd 0xfefb718fc30e0f8f

def z1205 : W := mkw 0x0000148000000000 0x0000014800000000 0xfe853fcfc0000000 0x3fe853fcfc000000

def z1206 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x07fec0003fff0007 0xc07fec0003fff000

def z1207 : W := mkw 0xe03fbca8baca0000 0xfe03fbca8baca000 0xfffff8fcffff0007 0xefffff8fcffff000

def z1208 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffffffffc09c0004 0x3ffffffffc09c000

def z1209 : W := mkw 0x3700014555f5eff6 0x03700014555f5eff 0x004000003fffffff 0xc004000003ffffff

def z1210 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe7bd3fc03f63ff0b 0xde7bd3fc03f63ff0

def z1211 : W := mkw 0xa4135eba90c00824 0x5a4135eba90c0082 0xe1321ffff0809830 0xbe1321ffff080983

def z1212 : W := mkw 0xa03ffeba90c00000 0xfa03ffeba90c0000 0xffbffffff0e080fd 0xfffbffffff0e080f

def z1213 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcbe73fcc9c87fe 0xf7dcbe73fcc9c87f

def z1214 : W := mkw 0x01000045413163c0 0x001000045413163c 0xb6c520cfc373670b 0x5b6c520cfc373670

def z1215 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3b018303000f8f9 0xee3b018303000f8f

def z1216 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x5fffe0303fff8037 0xc5fffe0303fff803

def z1217 : W := mkw 0xa03ffeba90ca0000 0xfa03ffeba90ca000 0xfffffffff0ff0005 0xffffffffff0ff000

def z1218 : W := mkw 0x402ca0002a0a0000 0xa402ca0002a0a000 0x164de0000f7f0003 0x0164de0000f7f000

def z1219 : W := mkw 0x130001454535e7d2 0x0130001454535e7d 0x004000000f7f67cf 0x4004000000f7f67c

def z1220 : W := mkw 0x8013feba80000000 0x78013feba8000000 0xfd8bffffc0000000 0x3fd8bffffc000000

def z1221 : W := mkw 0x1200431304148552 0x0120043130414855 0xfdcadf330c9cfffe 0xffdcadf330c9cfff

def z1222 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xfffedff03f9cffff 0xffffedff03f9cfff

def z1223 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe5881fffc0000000 0x3e5881fffc000000

def z1224 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe3b01ffff000f809 0xfe3b01ffff000f80

def z1225 : W := mkw 0x8000feba80000000 0x38000feba8000000 0xf000ffffc0000000 0x3f000ffffc000000

def z1226 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xffbfffffc00000cc 0x7ffbfffffc00000c

def z1227 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0x9e3fffffc0000000 0x39e3fffffc000000

def z1228 : W := mkw 0x582c15c02f00d608 0x8582c15c02f00d60 0xe6b41fc03300ff0b 0x5e6b41fc03300ff0

def z1229 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x7fffe0003fff800f 0xc7fffe0003fff800

def z1230 : W := mkw 0x2413082c10e028a4 0x52413082c10e028a 0xc333183c30e0f8fd 0xcc333183c30e0f8f

def z1231 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x3fffe0033fff0007 0xf3fffe0033fff000

def z1232 : W := mkw 0x80005eba80000000 0x180005eba8000000 0xe9821fffc08080fc 0xfe9821fffc08080f

def z1233 : W := mkw 0x1000010004008400 0x0100001000400840 0xe3b01f003000ff09 0xde3b01f003000ff0

def z1234 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0xffbffffff0001800 0x3ffbffffff000180

def z1235 : W := mkw 0x603fa0003aca0000 0xe603fa0003aca000 0x0bfbc0003fff0007 0xc0bfbc0003fff000

def z1236 : W := mkw 0x0000421200000000 0x0000042120000000 0xbe8de7cfc0000000 0x3be8de7cfc000000

def z1237 : W := mkw 0x802cfeba80000000 0xb802cfeba8000000 0x940cffcfc0000000 0x1940cffcfc000000

def z1238 : W := mkw 0x603fa8283aca0000 0xf603fa8283aca000 0xfffff83c3fff80ff 0xefffff83c3fff80f

def z1239 : W := mkw 0x603fb4803aca0000 0xe603fb4803aca000 0xffffffc03ffff80f 0xdffffffc03ffff80

def z1240 : W := mkw 0x2613ea3f10fe29f6 0x72613ea3f10fe29f 0x1843e03f00ff00f4 0x21843e03f00ff00f

def z1241 : W := mkw 0x1200431304148552 0x0120043130414855 0x65cac7300c9c87fe 0xd65cac7300c9c87f

def z1242 : W := mkw 0x01000045413163c0 0x001000045413163c 0xbec7e0cfc3ff67cf 0x7bec7e0cfc3ff67c

def z1243 : W := mkw 0xe03ff692baca0000 0xee03ff692baca000 0xbfffe7cfffff0007 0xfbfffe7cfffff000

def z1244 : W := mkw 0x1200431304148552 0x0120043130414855 0x7dcee7330f9f87fe 0xf7dcee7330f9f87f

def z1245 : W := mkw 0xa43ffeba90c00824 0xfa43ffeba90c0082 0xffbffffff0e09835 0xfffbffffff0e0983

def z1246 : W := mkw 0x803ffeba80000000 0xf803ffeba8000000 0xfc0fffffc0000000 0x3fc0fffffc000000

def z1247 : W := mkw 0x802c5eba80000000 0x9802c5eba8000000 0xe40c1fffc0000000 0x3e40c1fffc000000

def z1248 : W := mkw 0x403fa0002a0a0000 0xe403fa0002a0a000 0x1fffe0000f7f0007 0x41fffe0000f7f000

def z1249 : W := mkw 0x1200431304148552 0x0120043130414855 0x698ac7330c8c87fc 0xf698ac7330c8c87f

def z1250 : W := mkw 0x2413a82c10ea28a4 0x72413a82c10ea28a 0xebb3d83c30ecf8fd 0xeebb3d83c30ecf8f

def z1251 : W := mkw 0x1200431304148552 0x0120043130414855 0x5d4ac7330c9c87f6 0xb5d4ac7330c9c87f

def z1252 : W := mkw 0x0000421200000000 0x0000042120000000 0xfd8ac7ffc0000000 0x3fd8ac7ffc000000

def z1253 : W := mkw 0x1200431204048412 0x0120043120404841 0x6d8ac7300c8c87fe 0xf6d8ac7300c8c87f

def z1254 : W := mkw 0x1200431304148552 0x0120043130414855 0x7d8ac7330c8c87f8 0xb7d8ac7330c8c87f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z8,z4,z9,z6]),(0,[z1,z2,z3,z4,z5,z10,z6])],[(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z2,z3,z4,z12,z6,z13]),(0,[z14,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z1,z2,z17,z18,z3,z5,z6]),(0,[z1,z2,z3,z19,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z20,z6])],[(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z22])],[(0,[z1,z23,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z15]),(0,[z1,z2,z3,z25,z4,z5,z6]),(0,[z1,z26,z2,z27,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z29])],[(0,[z1,z2,z3,z4,z5,z30,z6]),(0,[z1,z2,z3,z4,z5,z6,z31]),(0,[z1,z2,z3,z32,z4,z5,z6])],[(1,[z33,z2,z3,z34,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z6])],[(0,[z36,z1,z2,z3,z4,z5,z13]),(1,[z37,z1,z2,z3,z4,z5]),(0,[z38,z1,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z40,z2,z3,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z43])],[(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z4,z46,z47,z5,z6]),(0,[z1,z2,z3,z48,z4,z5,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z50])],[(0,[z1,z2,z3,z4,z5,z51,z6])],[(0,[z1,z52,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z55,z3,z4,z5,z6]),(0,[z56,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z57,z6]),(0,[z1,z2,z58,z3,z4,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z6])],[(1,[z36,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z5,z6]),(0,[z1,z2,z62,z3,z4,z63,z6]),(0,[z1,z2,z3,z4,z64,z5,z6]),(0,[z1,z2,z3,z65,z66,z5,z6]),(0,[z67,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z68,z6]),(1,[z1,z55,z3,z4,z69,z6])],[(0,[z1,z70,z3,z4,z5,z6,z71]),(0,[z72,z1,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(1,[z1,z2,z3,z4,z9,z24])],[(0,[z1,z2,z3,z74,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z75]),(0,[z54,z1,z3,z4,z5,z76,z6]),(0,[z1,z77,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z6,z78]),(0,[z1,z2,z79,z3,z4,z5,z50]),(0,[z1,z2,z3,z4,z80,z81,z6]),(0,[z1,z2,z82,z4,z5,z83,z6]),(1,[z1,z2,z17,z84,z3,z6]),(0,[z85,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z24]),(1,[z1,z2,z3,z4,z80,z13])],[(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z66,z4,z5,z6]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z84,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z90,z6]),(0,[z91,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z6,z92]),(0,[z1,z2,z93,z3,z4,z5,z6])],[(1,[z94,z2,z95,z4,z5,z6]),(0,[z96,z2,z3,z97,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z71])],[(0,[z1,z2,z3,z4,z5,z99,z6]),(0,[z28,z1,z100,z3,z4,z5,z6]),(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z80,z6])],[(0,[z1,z103,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z105,z5,z6]),(0,[z1,z2,z106,z3,z4,z5,z6])],[(0,[z107,z1,z2,z3,z108,z4,z5]),(0,[z1,z2,z3,z109,z4,z5,z6])],[(0,[z110,z1,z55,z2,z3,z4,z6]),(0,[z14,z1,z111,z3,z4,z5,z6]),(0,[z1,z2,z3,z112,z4,z5,z6]),(0,[z1,z3,z4,z5,z113,z6,z71]),(0,[z28,z1,z2,z3,z5,z114,z6]),(0,[z1,z2,z3,z4,z5,z114,z6]),(0,[z1,z2,z3,z4,z5,z24,z83]),(0,[z1,z2,z84,z3,z4,z5,z115]),(0,[z116,z1,z2,z3,z4,z5,z24])]],
   [[(0,[z1,z2,z3,z4,z5,z117,z6]),(1,[z1,z2,z3,z4,z63,z6]),(0,[z1,z40,z2,z3,z65,z5,z6]),(0,[z1,z2,z3,z65,z5,z81,z6]),(0,[z1,z2,z3,z4,z69,z5,z118])],[(0,[z1,z2,z3,z4,z30,z6,z13]),(1,[z119,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z121,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z122,z4,z5,z6]),(0,[z110,z1,z123,z3,z4,z5,z6]),(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z9,z5,z24])],[(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z128,z6])],[(1,[z1,z2,z3,z129,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z108,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z133,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z134])],[(0,[z54,z110,z1,z2,z3,z4,z6]),(0,[z54,z1,z2,z3,z4,z69,z6])],[(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z136,z1,z2,z60,z3,z4,z6]),(0,[z1,z2,z3,z97,z4,z5,z13]),(1,[z137,z2,z3,z4,z5,z6])]],
   [[(1,[z138,z70,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z139,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z105,z5,z6]),(0,[z1,z2,z3,z4,z5,z141,z6]),(0,[z1,z2,z142,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z77,z3,z4,z5,z113,z6]),(0,[z28,z1,z2,z3,z66,z5,z6]),(0,[z1,z2,z143,z3,z4,z5,z6])],[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z113]),(0,[z86,z1,z3,z4,z5,z6,z71]),(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z66,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z145,z5,z6]),(0,[z1,z2,z3,z146,z4,z5,z6])],[(1,[z14,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z147,z6]),(1,[z1,z2,z82,z4,z5,z83])],[(0,[z148,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z149,z5,z6]),(0,[z1,z150,z2,z3,z4,z5,z6]),(0,[z1,z151,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z152,z153]),(0,[z1,z2,z3,z4,z5,z83,z13]),(0,[z1,z2,z3,z4,z5,z13,z154])],[(0,[z1,z2,z3,z4,z5,z6,z15]),(0,[z1,z155,z2,z3,z4,z5,z6]),(0,[z1,z156,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z157,z6]),(0,[z1,z2,z3,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z159])],[(0,[z1,z2,z3,z4,z5,z6,z160]),(0,[z1,z2,z62,z3,z4,z5,z68]),(1,[z1,z2,z3,z4,z24,z13])],[(0,[z104,z1,z2,z109,z4,z5,z6]),(0,[z1,z2,z3,z161,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z162,z6]),(0,[z1,z2,z3,z108,z4,z5,z13])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z163]),(0,[z1,z156,z2,z18,z3,z5,z6]),(0,[z86,z1,z77,z3,z4,z5,z6]),(0,[z1,z77,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z164])]],
   [[(0,[z1,z2,z3,z4,z5,z165,z6]),(0,[z33,z1,z2,z3,z4,z5,z13]),(0,[z1,z123,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z166]),(0,[z1,z2,z3,z167,z4,z5,z6])],[(0,[z168,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z169,z5,z6]),(0,[z1,z2,z3,z4,z170,z5,z6])],[(0,[z1,z60,z3,z4,z5,z76,z6]),(0,[z171,z1,z2,z3,z4,z5,z6]),(0,[z1,z172,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z1,z2,z3,z173,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z174]),(0,[z1,z2,z3,z4,z175,z5,z6]),(1,[z1,z2,z3,z4,z57,z6]),(0,[z1,z2,z82,z3,z4,z5,z24])],[(0,[z1,z176,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z177,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z178]),(0,[z1,z2,z3,z179,z4,z5,z6])],[(0,[z138,z1,z60,z3,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z5,z6]),(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z1,z181,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z182,z34,z5]),(0,[z1,z2,z3,z4,z5,z6,z183]),(0,[z1,z2,z3,z4,z5,z24,z184]),(0,[z104,z1,z2,z3,z4,z5,z185]),(0,[z28,z1,z2,z3,z5,z81,z6]),(1,[z1,z2,z79,z4,z80,z6]),(0,[z1,z2,z3,z4,z5,z6,z186])],[(0,[z1,z55,z60,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z5,z81,z6]),(1,[z1,z2,z3,z4,z5,z187])],[(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z189]),(0,[z1,z2,z3,z4,z12,z5,z24]),(1,[z56,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z4,z5,z114,z6]),(0,[z1,z181,z2,z3,z8,z4,z6]),(0,[z125,z1,z2,z3,z4,z190,z6]),(1,[z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z191,z6])],[(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z62,z3,z4,z5,z193]),(0,[z194,z1,z2,z3,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z6]),(0,[z1,z2,z27,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z195,z6]),(0,[z1,z2,z196,z3,z4,z5,z6]),(0,[z1,z2,z197,z3,z4,z5,z6])],[(0,[z1,z2,z3,z66,z47,z5,z6]),(0,[z1,z198,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z199,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z200]),(0,[z1,z181,z2,z3,z4,z5,z13])],[(0,[z94,z1,z2,z3,z4,z5,z6]),(1,[z201,z2,z3,z4,z5,z6]),(1,[z1,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z202,z6]),(0,[z1,z2,z3,z4,z5,z203,z6])],[(0,[z1,z2,z3,z4,z5,z204,z6]),(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z206,z1,z2,z3,z4,z5,z6])],[(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z47,z5,z114,z6]),(0,[z208,z1,z2,z3,z4,z5,z6])],[(0,[z138,z1,z2,z3,z4,z5,z24]),(0,[z1,z70,z2,z3,z4,z5,z24]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z211,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z212]),(1,[z1,z2,z3,z213,z5,z6]),(0,[z104,z1,z2,z3,z4,z214,z6]),(0,[z1,z2,z215,z3,z4,z5,z6]),(0,[z1,z55,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z216,z6]),(0,[z1,z217,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z218,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z219]),(0,[z1,z2,z3,z4,z5,z6,z118]),(0,[z1,z77,z2,z3,z4,z5,z113]),(0,[z28,z1,z2,z3,z4,z5,z13])],[(0,[z107,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z6,z220]),(0,[z1,z2,z3,z4,z5,z6,z221]),(0,[z1,z2,z222,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z223,z6]),(0,[z1,z2,z18,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z224,z5,z6]),(0,[z1,z2,z3,z225,z4,z5,z6]),(0,[z226,z1,z2,z3,z8,z4,z6]),(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z2,z228,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z13,z229])],[(0,[z1,z2,z3,z230,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z231,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z232,z6]),(0,[z28,z1,z156,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z233]),(0,[z1,z2,z3,z4,z113,z6,z78]),(0,[z1,z2,z3,z4,z5,z83,z6]),(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z5,z152,z6])],[(0,[z110,z1,z2,z3,z4,z80,z6]),(0,[z14,z1,z2,z3,z108,z4,z5]),(1,[z1,z2,z3,z4,z5,z157]),(0,[z1,z2,z3,z4,z69,z80,z6]),(0,[z1,z2,z3,z235,z4,z5,z6]),(0,[z1,z2,z3,z236,z4,z5,z6])],[(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z107,z1,z77,z2,z3,z4,z5]),(0,[z1,z40,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z238,z5,z6]),(0,[z125,z1,z2,z4,z5,z6,z153]),(0,[z91,z1,z2,z3,z4,z5,z152]),(0,[z1,z2,z3,z239,z4,z5,z6])],[(0,[z1,z2,z3,z4,z240,z5,z6]),(1,[z1,z2,z241,z3,z4,z5]),(0,[z1,z2,z60,z3,z4,z5,z13]),(0,[z226,z1,z2,z3,z4,z5,z13]),(1,[z1,z242,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z4,z5,z153,z13]),(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z5,z6])],[(0,[z1,z2,z3,z244,z4,z5,z6]),(0,[z110,z1,z2,z3,z64,z5,z6]),(0,[z1,z245,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z66,z4,z5,z13]),(0,[z1,z246,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z95,z4,z34,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z247,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z248]),(0,[z1,z2,z3,z129,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z250,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z251]),(0,[z252,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z253,z6]),(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z255,z6])],[(0,[z110,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z69,z5,z24]),(1,[z1,z2,z3,z4,z190,z6]),(0,[z1,z2,z17,z3,z4,z5,z24]),(0,[z256,z1,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z257,z5,z6]),(0,[z1,z156,z3,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z258,z6]),(0,[z259,z1,z2,z3,z4,z5,z6]),(0,[z260,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z261,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z262,z13])],[(0,[z1,z2,z3,z4,z5,z189,z6]),(0,[z263,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z214,z6]),(0,[z1,z2,z3,z4,z5,z174,z6])],[(0,[z264,z1,z2,z3,z4,z5,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z96,z72,z2,z3,z4,z5,z6]),(1,[z1,z2,z266,z4,z5,z6]),(0,[z1,z3,z109,z4,z47,z5,z6]),(0,[z1,z2,z3,z65,z5,z114,z6]),(0,[z1,z2,z267,z3,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z187]),(0,[z1,z2,z3,z4,z5,z7,z6])],[(1,[z1,z2,z3,z4,z5,z118]),(0,[z1,z2,z268,z3,z4,z5,z6]),(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z24]),(0,[z1,z270,z2,z84,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z271]),(1,[z1,z2,z272,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z221]),(0,[z1,z2,z3,z4,z273,z5,z6]),(0,[z274,z1,z2,z3,z4,z5,z6])],[(1,[z1,z123,z3,z4,z5,z6]),(0,[z1,z2,z3,z149,z109,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z275,z4,z5,z6]),(0,[z1,z2,z84,z3,z4,z6,z13]),(0,[z1,z2,z3,z4,z5,z6,z276])],[(0,[z70,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z47,z5,z81,z6]),(0,[z1,z181,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z277,z24])],[(0,[z1,z2,z3,z4,z5,z278,z6]),(0,[z279,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z24]),(0,[z1,z281,z2,z3,z4,z5,z6])],[(0,[z107,z1,z2,z3,z4,z5,z83]),(0,[z1,z27,z3,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z113]),(0,[z1,z2,z282,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z283])],[(0,[z284,z1,z2,z3,z4,z5,z6]),(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z286]),(0,[z1,z2,z3,z4,z5,z6,z287]),(0,[z1,z2,z3,z4,z5,z152,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z1,z55,z2,z3,z4,z6,z13]),(0,[z1,z181,z2,z79,z4,z5,z6]),(0,[z1,z181,z2,z8,z4,z5,z6])],[(0,[z54,z1,z2,z3,z4,z5,z13]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z1,z290,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z291])]],
   [[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z292,z6]),(1,[z1,z2,z3,z293,z5,z6]),(0,[z1,z2,z294,z3,z4,z5,z6]),(1,[z1,z2,z295,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z296]),(0,[z1,z297,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z276,z13])],[(0,[z138,z1,z70,z3,z4,z5,z6]),(0,[z1,z298,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z5,z152])],[(0,[z1,z2,z241,z60,z3,z4,z5]),(0,[z1,z2,z299,z3,z4,z5,z6]),(0,[z1,z2,z82,z3,z4,z5,z13])],[(0,[z104,z1,z2,z3,z129,z5,z6]),(0,[z1,z181,z2,z27,z4,z5,z6]),(1,[z1,z2,z3,z4,z300,z6]),(0,[z1,z2,z3,z4,z5,z6,z301])],[(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z1,z304,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z305,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z78]),(0,[z1,z2,z3,z306,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z283,z13]),(0,[z307,z1,z2,z3,z4,z5,z24])],[(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z308,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z309,z6]),(1,[z1,z2,z3,z4,z5,z310]),(0,[z311,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z13]),(0,[z132,z1,z2,z3,z4,z5,z24])],[(0,[z2,z60,z3,z4,z5,z30,z6]),(0,[z1,z2,z95,z4,z5,z80,z6]),(0,[z1,z181,z2,z95,z4,z5,z6]),(0,[z33,z96,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z312,z6]),(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z13]),(1,[z263,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z3,z314,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z315,z6])]],
   [[(0,[z1,z316,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z187,z6])],[(0,[z1,z317,z2,z3,z4,z5,z6])],[(0,[z94,z72,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z318,z4,z5,z6]),(0,[z1,z55,z3,z4,z69,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z24]),(0,[z1,z319,z2,z3,z4,z5,z6])],[(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z71]),(0,[z1,z2,z18,z3,z5,z114,z6])],[(0,[z1,z2,z17,z3,z97,z5,z6]),(0,[z1,z2,z3,z4,z5,z321,z6]),(0,[z1,z156,z40,z3,z4,z5,z6]),(0,[z1,z2,z322,z3,z4,z5,z6]),(0,[z1,z2,z3,z323,z4,z5,z6])],[(0,[z1,z2,z324,z3,z4,z5,z6]),(1,[z1,z2,z3,z225,z4,z6]),(0,[z1,z2,z3,z325,z4,z5,z6]),(0,[z1,z2,z17,z3,z47,z5,z6])],[(0,[z1,z70,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z6]),(0,[z1,z2,z3,z4,z5,z83,z283]),(0,[z1,z2,z326,z3,z4,z5,z24])],[(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z328,z6]),(1,[z96,z2,z3,z97,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z329,z5,z6]),(0,[z1,z330,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z331,z5,z6])]],
   [[(0,[z332,z1,z2,z3,z4,z5,z6]),(0,[z1,z333,z2,z3,z4,z5,z6]),(1,[z54,z1,z3,z4,z76,z6])],[(0,[z1,z2,z3,z4,z5,z6,z334]),(0,[z2,z3,z4,z5,z184,z6,z15]),(0,[z107,z1,z2,z3,z4,z5,z184]),(0,[z1,z2,z3,z4,z5,z335,z6]),(1,[z54,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z6,z336]),(0,[z1,z2,z3,z108,z4,z5,z283])],[(0,[z36,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z95,z4,z5,z6,z153]),(0,[z1,z337,z2,z3,z4,z5,z6]),(0,[z338,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z339,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z95,z4,z5,z24]),(0,[z1,z2,z340,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z248]),(0,[z226,z1,z2,z3,z4,z30,z6]),(0,[z14,z1,z77,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z47,z5,z24]),(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z342]),(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z344])],[(0,[z345,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z347,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z30,z13]),(0,[z1,z2,z3,z4,z5,z348,z6]),(1,[z1,z2,z4,z46,z5,z6]),(0,[z1,z2,z3,z4,z5,z349,z13]),(0,[z1,z2,z3,z4,z5,z350,z6])],[(0,[z72,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z62,z3,z4,z5,z24]),(0,[z1,z351,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z81,z24]),(0,[z1,z352,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z353]),(0,[z104,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z354,z3,z4,z5,z6]),(0,[z1,z355,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z29])],[(0,[z356,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z357,z6]),(0,[z110,z1,z2,z3,z8,z4,z6]),(0,[z1,z2,z3,z65,z4,z5,z13]),(0,[z1,z2,z3,z358,z4,z5,z6]),(0,[z1,z2,z359,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z202]),(1,[z1,z2,z3,z4,z145,z6]),(1,[z91,z1,z2,z3,z5,z283])]],
   [[(0,[z1,z2,z27,z3,z4,z5,z24]),(0,[z54,z360,z2,z3,z4,z5,z6]),(0,[z361,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z362,z6]),(0,[z1,z2,z3,z4,z363,z5,z6])],[(0,[z364,z1,z2,z3,z4,z5,z6]),(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z366])],[(0,[z1,z2,z3,z4,z5,z367,z6]),(0,[z1,z2,z3,z4,z5,z368,z6]),(0,[z110,z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z369,z5,z6]),(0,[z14,z1,z242,z3,z4,z5,z6]),(0,[z1,z2,z109,z4,z5,z80,z6])],[(0,[z110,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z370,z6]),(0,[z104,z28,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z13]),(0,[z1,z2,z17,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z371,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z13])],[(0,[z94,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z372,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z24,z6])],[(0,[z1,z137,z2,z3,z4,z5,z6]),(0,[z1,z2,z272,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z373])],[(1,[z1,z2,z3,z64,z5,z6]),(0,[z1,z2,z374,z3,z4,z5,z6]),(0,[z1,z2,z3,z266,z4,z5,z6]),(0,[z1,z375,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z6])],[(0,[z1,z2,z3,z4,z5,z376,z6]),(0,[z1,z2,z84,z3,z4,z80,z6])]],
   [[(0,[z377,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z378,z6]),(0,[z1,z2,z242,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z379,z6]),(0,[z1,z380,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z57,z6]),(0,[z1,z2,z3,z381,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z189]),(0,[z1,z2,z79,z3,z4,z80,z6]),(0,[z1,z2,z3,z8,z4,z6,z13])],[(0,[z382,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z97,z5,z6]),(1,[z226,z2,z3,z4,z12,z6]),(0,[z226,z1,z2,z3,z4,z12,z6]),(0,[z14,z1,z2,z266,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z83]),(0,[z1,z2,z3,z4,z5,z383,z6]),(0,[z1,z55,z2,z3,z4,z69,z6])],[(0,[z1,z2,z17,z3,z34,z5,z6]),(0,[z1,z2,z3,z384,z4,z5,z6]),(0,[z28,z1,z26,z2,z4,z5,z6]),(0,[z385,z1,z2,z3,z4,z5,z6]),(0,[z1,z270,z2,z3,z4,z5,z6])],[(0,[z138,z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z386,z5,z6]),(0,[z1,z2,z3,z4,z5,z387,z6]),(0,[z1,z2,z3,z4,z5,z76,z13]),(0,[z125,z1,z2,z3,z4,z5,z153]),(0,[z1,z2,z3,z4,z5,z5,z24])],[(0,[z36,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z388,z3,z4,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z390,z3,z4,z5,z6]),(0,[z391,z1,z2,z3,z4,z5,z6]),(1,[z1,z156,z3,z65,z5,z6]),(0,[z1,z2,z84,z3,z4,z5,z24])],[(0,[z1,z2,z3,z4,z392,z5,z6]),(0,[z1,z393,z2,z3,z4,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z395,z6]),(1,[z1,z2,z3,z4,z170,z6]),(0,[z1,z26,z2,z3,z4,z5,z24]),(0,[z1,z40,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z396,z4,z5,z6]),(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z398,z5,z6]),(1,[z1,z2,z3,z108,z5,z152])],[(0,[z399,z1,z2,z3,z4,z5,z6]),(0,[z107,z1,z2,z3,z4,z5,z24]),(0,[z1,z26,z2,z66,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z6,z400]),(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z7,z6])]],
   [[(0,[z1,z2,z3,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z403,z6]),(0,[z1,z2,z3,z4,z5,z6,z404])],[(0,[z1,z2,z3,z4,z405,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z24]),(0,[z1,z40,z2,z18,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z283])],[(0,[z1,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z406]),(0,[z1,z2,z407,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z105,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z71]),(0,[z116,z1,z2,z3,z4,z9,z6]),(0,[z256,z1,z2,z3,z4,z5,z24])],[(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z2,z60,z3,z95,z4,z5,z6]),(0,[z14,z1,z2,z3,z293,z5,z6])],[(0,[z1,z2,z62,z4,z5,z80,z6]),(0,[z1,z2,z3,z410,z4,z5,z6])],[(1,[z1,z2,z3,z8,z4,z13])],[(0,[z1,z2,z3,z4,z411,z5,z6]),(0,[z412,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z6]),(0,[z1,z2,z414,z3,z4,z5,z6]),(1,[z116,z1,z2,z3,z4,z13])]],
   [[(0,[z1,z2,z3,z4,z5,z415,z6]),(0,[z1,z2,z27,z4,z5,z80,z6]),(0,[z416,z1,z2,z3,z4,z5,z6]),(0,[z1,z417,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z418,z5,z6]),(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z420])],[(0,[z421,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z30,z24]),(0,[z422,z1,z2,z3,z4,z5,z6]),(0,[z1,z201,z2,z3,z4,z5,z6]),(0,[z423,z1,z2,z3,z4,z5,z6])],[(0,[z72,z2,z60,z3,z4,z5,z6]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z156,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z425,z6]),(0,[z1,z2,z3,z4,z5,z13,z183])],[(0,[z1,z2,z3,z4,z5,z426,z6]),(0,[z110,z1,z427,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z357]),(0,[z116,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z6,z344])],[(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z429,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z82,z3,z4,z5,z153])],[(0,[z1,z2,z3,z4,z5,z430,z6]),(0,[z1,z2,z3,z4,z5,z431,z6]),(0,[z1,z2,z66,z4,z5,z80,z6]),(0,[z1,z2,z3,z432,z4,z5,z6])],[(0,[z433,z1,z2,z3,z4,z5,z6]),(1,[z104,z1,z109,z4,z5,z6]),(0,[z1,z181,z2,z109,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z400]),(0,[z434,z1,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z9,z5,z13])],[(0,[z1,z2,z3,z4,z5,z6,z435]),(0,[z14,z1,z2,z3,z4,z5,z184]),(0,[z1,z2,z3,z4,z5,z15,z13]),(0,[z1,z2,z3,z4,z5,z6,z436]),(0,[z1,z2,z437,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z301,z13])]],
   [[(0,[z1,z2,z62,z4,z5,z6,z153]),(0,[z110,z2,z3,z4,z5,z30,z6]),(1,[z1,z2,z3,z238,z5,z6]),(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z1,z2,z439,z3,z4,z5,z6])],[(0,[z96,z1,z2,z3,z34,z5,z6]),(0,[z440,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z18,z66,z5,z6]),(0,[z1,z2,z3,z4,z5,z292,z24])],[(0,[z1,z2,z3,z4,z5,z441,z6]),(0,[z54,z1,z2,z3,z4,z9,z6]),(0,[z1,z2,z3,z4,z5,z6,z442])],[(0,[z1,z2,z3,z443,z4,z5,z6]),(0,[z28,z1,z150,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z444]),(1,[z1,z2,z3,z4,z81,z13]),(0,[z1,z2,z3,z4,z5,z6,z13])],[(0,[z1,z2,z3,z4,z5,z6,z445]),(0,[z1,z2,z3,z4,z46,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z446]),(0,[z1,z2,z3,z4,z447,z5,z6])],[(0,[z28,z1,z2,z4,z5,z114,z6])],[(0,[z1,z2,z3,z4,z448,z5,z6]),(0,[z104,z1,z2,z3,z4,z309,z6]),(0,[z1,z2,z3,z449,z4,z5,z6]),(0,[z1,z2,z4,z5,z83,z6,z153])],[(0,[z1,z2,z3,z4,z5,z450,z6]),(0,[z104,z263,z2,z3,z4,z5,z6]),(0,[z1,z3,z65,z4,z47,z5,z6]),(0,[z1,z2,z79,z4,z5,z80,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z451]),(0,[z1,z2,z82,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z452,z6]),(0,[z110,z1,z2,z3,z4,z30,z6]),(0,[z1,z156,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z453,z5,z6]),(0,[z1,z454,z2,z3,z4,z5,z6]),(1,[z1,z2,z84,z3,z4,z13]),(0,[z1,z2,z3,z4,z455,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z456])],[(0,[z36,z1,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z457,z4,z5,z6]),(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z459,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z248]),(0,[z1,z2,z3,z109,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z6,z460]),(0,[z1,z55,z2,z3,z4,z76,z6]),(0,[z1,z2,z84,z3,z5,z81,z6]),(0,[z1,z2,z3,z4,z5,z6,z349])],[(0,[z1,z60,z3,z4,z5,z6,z71]),(0,[z1,z2,z3,z4,z461,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z114,z24]),(0,[z1,z462,z2,z3,z4,z5,z13])],[(0,[z1,z2,z62,z3,z225,z4,z6]),(0,[z1,z2,z3,z4,z5,z463,z6]),(0,[z1,z2,z3,z4,z5,z24,z113]),(0,[z1,z2,z18,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z182,z5,z6]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z1,z2,z3,z8,z4,z69,z6]),(0,[z1,z2,z3,z465,z4,z5,z6])],[(0,[z466,z1,z2,z3,z4,z5,z6]),(1,[z110,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z467,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z184,z13]),(0,[z54,z1,z2,z48,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z468,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z81,z6,z13])],[(0,[z470,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z370,z6]),(0,[z1,z156,z3,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z152]),(0,[z1,z2,z3,z4,z24,z6,z13])]],
   [[(0,[z1,z471,z2,z3,z4,z5,z6]),(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z84,z3,z73,z4,z6]),(1,[z1,z2,z3,z73,z81,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(0,[z131,z1,z2,z3,z4,z5,z24])],[(0,[z1,z2,z60,z3,z4,z5,z6]),(0,[z1,z77,z60,z3,z4,z5,z6]),(1,[z1,z2,z474,z4,z5,z6]),(0,[z28,z1,z181,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z475,z6])],[(0,[z1,z2,z3,z4,z5,z476,z6]),(0,[z1,z477,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z66,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z478,z6]),(1,[z1,z2,z3,z4,z5,z13])],[(0,[z36,z1,z2,z3,z4,z5,z24]),(0,[z1,z479,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z480,z5,z6]),(0,[z1,z55,z2,z3,z4,z9,z6]),(0,[z116,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z481,z4,z5,z6]),(0,[z1,z2,z482,z3,z4,z5,z6]),(0,[z1,z2,z3,z238,z4,z5,z6]),(0,[z1,z2,z3,z483,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z153])],[(0,[z14,z1,z2,z3,z4,z5,z24]),(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z146,z4,z5,z24])],[(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z152,z83]),(0,[z1,z2,z3,z4,z5,z486,z6]),(0,[z1,z2,z84,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z487,z6]),(0,[z110,z1,z2,z3,z4,z12,z6]),(0,[z1,z2,z3,z149,z4,z5,z6]),(0,[z1,z26,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z488,z6]),(0,[z1,z2,z3,z4,z5,z489,z6]),(0,[z91,z1,z2,z3,z5,z6,z283])]],
   [[(0,[z1,z2,z3,z4,z5,z490,z6]),(0,[z1,z2,z3,z4,z5,z491,z6]),(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z107,z1,z2,z3,z4,z5,z13]),(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z493,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z13]),(1,[z125,z1,z2,z4,z5,z153]),(0,[z1,z2,z3,z4,z5,z6,z420])],[(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z138,z2,z3,z95,z4,z5,z6]),(0,[z138,z226,z2,z3,z4,z5,z6]),(0,[z495,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z496,z6]),(0,[z1,z2,z497,z3,z4,z5,z6]),(0,[z1,z2,z498,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z499]),(0,[z500,z1,z2,z3,z4,z5,z6])],[(0,[z138,z1,z2,z3,z4,z5,z13]),(0,[z1,z70,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z501,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z13]),(0,[z1,z2,z3,z4,z5,z6,z502]),(0,[z1,z2,z3,z4,z503,z5,z6]),(0,[z1,z2,z3,z4,z5,z71,z13])],[(0,[z1,z2,z3,z4,z5,z504,z6]),(0,[z1,z55,z2,z3,z4,z5,z13]),(0,[z1,z77,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z13,z287])],[(1,[z107,z2,z3,z4,z5,z184]),(0,[z1,z505,z2,z3,z4,z5,z6])],[(0,[z1,z70,z3,z4,z5,z76,z6]),(0,[z506,z1,z2,z3,z4,z5,z6]),(0,[z1,z507,z2,z3,z109,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z8,z4,z5,z210]),(0,[z91,z1,z2,z3,z4,z5,z24])],[(0,[z14,z1,z2,z3,z213,z5,z6]),(0,[z1,z2,z508,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z190,z5,z6]),(0,[z509,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z510]),(0,[z1,z2,z3,z4,z5,z24,z283])],[(0,[z226,z1,z55,z2,z3,z4,z6]),(0,[z1,z2,z3,z73,z5,z81,z6]),(0,[z1,z2,z3,z4,z5,z24,z511])]],
   [[(0,[z1,z2,z512,z3,z4,z5,z6]),(1,[z1,z111,z3,z4,z5,z6]),(0,[z1,z2,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z513]),(0,[z514,z1,z2,z3,z4,z5,z6])],[(0,[z107,z2,z3,z4,z5,z184,z6])],[(0,[z1,z2,z3,z4,z5,z30,z13]),(0,[z104,z1,z2,z66,z4,z5,z6]),(0,[z1,z2,z3,z515,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z468,z6])],[(0,[z1,z2,z237,z60,z3,z4,z6]),(0,[z2,z62,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z30,z6]),(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z1,z2,z3,z516,z4,z5,z6])],[(0,[z226,z2,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z418,z5,z6])],[(0,[z1,z2,z3,z97,z5,z6,z283]),(0,[z110,z1,z2,z474,z4,z5,z6]),(0,[z2,z3,z4,z12,z5,z30,z6]),(0,[z14,z107,z2,z3,z4,z5,z6]),(0,[z1,z517,z2,z3,z4,z5,z6]),(0,[z1,z2,z518,z3,z4,z5,z6])],[(0,[z1,z2,z519,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z157]),(0,[z1,z2,z82,z3,z4,z5,z6]),(0,[z1,z2,z3,z520,z4,z5,z6]),(0,[z1,z2,z3,z521,z4,z5,z6])],[(0,[z1,z2,z3,z4,z522,z5,z6]),(0,[z523,z1,z2,z3,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z524,z4,z5,z6]),(0,[z1,z2,z525,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z202]),(0,[z1,z2,z3,z4,z5,z6,z527]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z206,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z6,z456])],[(0,[z1,z2,z3,z4,z529,z5,z6]),(0,[z136,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z370,z6]),(0,[z1,z2,z3,z4,z80,z6,z13])],[(0,[z1,z2,z3,z4,z5,z530,z6]),(1,[z1,z427,z3,z4,z5,z6]),(0,[z110,z1,z2,z45,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z6]),(1,[z1,z2,z3,z4,z5,z357]),(0,[z54,z1,z2,z3,z480,z5,z6]),(0,[z1,z2,z3,z4,z253,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z400])],[(0,[z531,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z97,z4,z5,z24]),(1,[z360,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z532,z6])],[(0,[z1,z2,z3,z533,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z534]),(0,[z1,z2,z3,z8,z4,z76,z6]),(0,[z535,z1,z2,z3,z4,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z13])],[(0,[z37,z1,z2,z60,z3,z4,z5]),(1,[z1,z2,z3,z4,z12,z13]),(0,[z1,z2,z3,z4,z5,z6,z536]),(0,[z1,z2,z537,z3,z4,z5,z6])],[(0,[z36,z1,z70,z3,z4,z5,z6]),(0,[z1,z2,z538,z3,z4,z5,z6]),(0,[z539,z1,z2,z3,z4,z5,z6]),(0,[z14,z86,z1,z2,z3,z4,z5]),(0,[z86,z107,z1,z2,z3,z4,z5]),(1,[z28,z1,z2,z5,z114,z6]),(0,[z1,z2,z17,z3,z4,z81,z6])]],
   [[(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z24])],[(0,[z1,z2,z3,z4,z5,z6,z541]),(0,[z2,z3,z97,z4,z34,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z544,z5,z6]),(0,[z1,z2,z3,z4,z300,z113,z6]),(0,[z1,z2,z3,z4,z5,z545,z6])],[(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z12,z6]),(0,[z1,z26,z3,z4,z47,z5,z6]),(0,[z1,z156,z26,z3,z4,z5,z6]),(0,[z1,z2,z547,z3,z4,z5,z6]),(0,[z1,z2,z295,z3,z8,z5,z6]),(0,[z1,z2,z3,z108,z4,z5,z24])],[(0,[z1,z2,z82,z95,z4,z5,z6]),(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z4,z5,z13]),(0,[z1,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z17,z3,z73,z5,z6])],[(0,[z33,z1,z2,z3,z4,z5,z24]),(0,[z104,z103,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z549]),(0,[z1,z2,z3,z4,z5,z114,z13]),(1,[z1,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z5,z6,z153]),(0,[z1,z2,z3,z73,z4,z81,z6]),(0,[z1,z2,z17,z84,z3,z4,z6])],[(0,[z550,z1,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z82,z4,z5,z6])],[(0,[z551,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z552,z6])],[(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z72,z138,z2,z3,z4,z5,z6]),(0,[z138,z2,z3,z4,z5,z30,z6]),(0,[z1,z77,z70,z3,z4,z5,z6]),(0,[z1,z26,z27,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z373]),(0,[z1,z2,z554,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z555]),(0,[z1,z181,z2,z3,z4,z80,z6])],[(0,[z1,z2,z556,z3,z4,z5,z6]),(0,[z1,z557,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z115]),(0,[z1,z2,z3,z558,z4,z5,z6]),(0,[z307,z1,z2,z3,z4,z5,z13])],[(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z34,z5]),(0,[z1,z561,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z562,z5,z6]),(0,[z96,z2,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z563]),(0,[z1,z2,z295,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z564,z5,z6])],[(0,[z1,z2,z3,z4,z5,z565,z6]),(1,[z1,z2,z3,z4,z182,z5]),(0,[z1,z2,z3,z4,z5,z566,z6]),(0,[z1,z2,z3,z4,z567,z5,z6]),(0,[z1,z2,z3,z4,z5,z568,z6]),(0,[z1,z2,z569,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z570,z6])],[(0,[z1,z2,z3,z571,z4,z5,z6]),(0,[z226,z2,z3,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z572,z6]),(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z574,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z13])],[(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z576,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z156,z2,z3,z65,z5,z6]),(0,[z1,z2,z3,z4,z69,z5,z6]),(0,[z1,z2,z8,z4,z5,z80,z6]),(0,[z1,z181,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z8,z4,z5,z13]),(0,[z577,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z283]),(0,[z1,z578,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z6])],[(1,[z103,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z579,z4,z5,z6]),(0,[z1,z181,z2,z66,z4,z5,z6]),(0,[z1,z2,z580,z3,z4,z5,z6]),(0,[z1,z2,z581,z3,z4,z5,z6]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z511])]],
   [[(0,[z1,z2,z583,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z262])],[],[(0,[z1,z584,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z585,z4,z5,z6]),(0,[z1,z586,z2,z3,z4,z5,z6]),(1,[z560,z1,z2,z3,z4,z5]),(1,[z1,z2,z308,z4,z5,z6]),(1,[z1,z2,z89,z4,z5,z6])],[(0,[z1,z587,z2,z3,z4,z5,z6]),(0,[z588,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z589,z5,z6]),(0,[z1,z590,z2,z3,z4,z5,z6])],[(0,[z1,z591,z2,z3,z4,z5,z6]),(0,[z226,z1,z2,z3,z4,z80,z6]),(0,[z28,z56,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z24])],[(0,[z1,z2,z3,z4,z5,z592,z6]),(0,[z1,z2,z3,z213,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z154]),(0,[z1,z593,z2,z3,z4,z5,z6])],[(1,[z1,z26,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z594,z5,z6]),(0,[z1,z2,z3,z4,z5,z277,z6]),(0,[z1,z2,z3,z4,z5,z6,z595])],[(0,[z1,z2,z3,z95,z4,z5,z13]),(0,[z1,z596,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z47,z5,z13]),(0,[z1,z2,z3,z4,z5,z76,z6]),(0,[z1,z2,z3,z8,z4,z81,z6]),(0,[z1,z597,z2,z3,z4,z5,z6]),(0,[z1,z2,z17,z84,z3,z5,z6])]],
   [[(0,[z1,z2,z598,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z599,z6]),(0,[z1,z2,z3,z97,z5,z81,z6]),(0,[z91,z107,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z600,z6]),(1,[z1,z2,z3,z4,z5,z115]),(0,[z1,z2,z601,z3,z4,z5,z6])],[(0,[z72,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z62,z3,z4,z5,z13]),(0,[z107,z1,z2,z3,z4,z5,z153]),(0,[z1,z2,z3,z602,z4,z5,z6]),(0,[z28,z201,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z603,z6]),(0,[z1,z2,z3,z4,z5,z81,z13])],[(0,[z1,z2,z60,z3,z4,z5,z24]),(0,[z94,z1,z2,z62,z4,z5,z6]),(0,[z72,z2,z62,z3,z4,z5,z6]),(0,[z226,z1,z2,z3,z4,z5,z24]),(0,[z104,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z604,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z81,z6]),(0,[z1,z2,z3,z5,z152,z6,z283])],[(0,[z1,z605,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z71,z153]),(0,[z1,z2,z3,z66,z4,z5,z24])],[(0,[z606,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z97,z5,z6]),(0,[z1,z2,z607,z3,z4,z5,z6]),(0,[z1,z2,z27,z3,z4,z5,z13]),(0,[z1,z40,z2,z3,z47,z5,z6]),(0,[z54,z137,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z300,z5,z6]),(0,[z1,z608,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z609,z4,z5,z6])],[(1,[z136,z1,z2,z3,z4,z6]),(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z97,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z1,z198,z2,z3,z4,z5,z13]),(0,[z1,z319,z2,z3,z4,z5,z24])],[(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z94,z2,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z613,z5,z6]),(0,[z1,z2,z614,z3,z4,z5,z6])]],
   [[(0,[z94,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z615,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z283]),(0,[z616,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z373]),(0,[z1,z2,z3,z617,z4,z5,z6])],[(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z3,z109,z4,z5,z6]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z620]),(0,[z1,z2,z84,z3,z4,z9,z6])],[(0,[z1,z621,z2,z3,z4,z5,z6]),(1,[z1,z77,z3,z4,z5,z113])],[(0,[z1,z2,z3,z4,z5,z622,z6]),(0,[z14,z91,z1,z2,z3,z4,z5]),(0,[z623,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z418,z5,z6]),(0,[z1,z2,z211,z3,z4,z5,z13])],[(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z624,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z625,z6])],[(0,[z1,z2,z3,z4,z5,z6,z626]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z84,z3,z8,z4,z6])],[(0,[z1,z2,z3,z4,z5,z628,z6]),(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z632,z2,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z145,z6]),(0,[z1,z2,z3,z4,z5,z633,z6])],[(0,[z1,z2,z3,z634,z4,z5,z6]),(0,[z1,z2,z3,z4,z635,z5,z6]),(0,[z1,z2,z3,z636,z4,z5,z6]),(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z638,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z639,z5,z6]),(0,[z28,z1,z2,z3,z4,z253,z6]),(0,[z1,z2,z79,z3,z8,z4,z6]),(1,[z1,z181,z2,z8,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z5,z13])],[(0,[z1,z640,z2,z3,z4,z5,z6]),(0,[z641,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z45,z4,z5,z6]),(1,[z1,z2,z48,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z642]),(0,[z1,z2,z3,z4,z9,z5,z6]),(0,[z1,z2,z3,z4,z5,z13,z13])],[(0,[z1,z40,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z239,z4,z5,z13]),(0,[z1,z2,z326,z3,z4,z5,z6])],[(0,[z54,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z643,z4,z5,z6])],[(0,[z1,z2,z427,z3,z4,z5,z6]),(0,[z1,z2,z17,z3,z65,z5,z6]),(0,[z28,z1,z2,z4,z5,z80,z6]),(0,[z1,z2,z3,z4,z5,z6,z229]),(0,[z1,z644,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z636,z5,z6]),(0,[z14,z1,z2,z3,z4,z170,z6]),(0,[z1,z2,z3,z4,z5,z6,z185])],[(0,[z72,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z1,z2,z645,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z646]),(0,[z1,z2,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z309,z5,z6]),(0,[z1,z2,z3,z4,z5,z647,z6])]],
   [[(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z649,z4,z5,z6])],[(0,[z1,z2,z62,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z193]),(0,[z28,z1,z2,z17,z3,z5,z6]),(0,[z650,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z81,z6]),(0,[z1,z2,z651,z3,z4,z5,z6])],[(0,[z1,z2,z652,z3,z4,z5,z6]),(1,[z1,z507,z2,z3,z5,z6]),(0,[z1,z2,z653,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z24])],[(0,[z1,z2,z3,z108,z34,z5,z6]),(0,[z1,z2,z3,z654,z4,z5,z6]),(0,[z1,z2,z3,z655,z4,z5,z6]),(0,[z54,z226,z1,z2,z3,z4,z6]),(0,[z1,z156,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z656,z4,z5,z6]),(1,[z1,z55,z2,z3,z4,z13]),(0,[z116,z1,z2,z3,z4,z6,z13])],[(0,[z657,z1,z2,z3,z4,z5,z6]),(0,[z119,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z69,z5,z76,z6]),(0,[z1,z2,z658,z3,z4,z5,z6])],[(0,[z33,z1,z2,z3,z34,z5,z6]),(1,[z1,z150,z3,z4,z5,z6]),(0,[z659,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z68]),(0,[z1,z2,z3,z4,z5,z6,z660]),(0,[z1,z462,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z661,z6]),(0,[z1,z2,z3,z4,z5,z6,z662]),(0,[z1,z663,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z664,z4,z5,z6]),(0,[z1,z665,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z83]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z667,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z668,z5,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z468,z6])],[(0,[z1,z2,z3,z4,z5,z184,z6]),(0,[z1,z2,z3,z4,z5,z6,z670]),(0,[z1,z2,z282,z3,z4,z5,z13])],[(0,[z1,z2,z3,z671,z4,z5,z6]),(0,[z1,z2,z474,z3,z4,z5,z6]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z2,z3,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z152,z13])],[(0,[z1,z673,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z674,z5,z6]),(0,[z675,z1,z2,z3,z4,z5,z6]),(0,[z1,z26,z2,z109,z4,z5,z6]),(0,[z1,z2,z3,z676,z4,z5,z6])],[(0,[z104,z1,z2,z27,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z185]),(0,[z104,z1,z2,z3,z4,z5,z549]),(0,[z28,z1,z2,z3,z4,z5,z310]),(0,[z1,z2,z3,z4,z5,z403,z24])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z36,z138,z2,z3,z4,z5,z6]),(0,[z1,z677,z2,z3,z4,z5,z6]),(0,[z1,z678,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z80,z76,z6]),(1,[z86,z1,z3,z4,z5,z71])],[(0,[z72,z1,z2,z95,z4,z5,z6]),(0,[z1,z2,z679,z3,z4,z5,z6]),(0,[z14,z1,z2,z308,z4,z5,z6]),(0,[z1,z680,z2,z3,z4,z5,z6]),(0,[z681,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z153]),(0,[z682,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z683,z3,z4,z5,z6]),(0,[z684,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z90])],[(0,[z14,z1,z2,z3,z4,z5,z153]),(0,[z85,z1,z2,z3,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z685,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z193]),(0,[z1,z2,z3,z4,z686,z5,z6]),(1,[z1,z270,z2,z4,z5,z6])],[(0,[z1,z2,z687,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z636,z5,z6]),(0,[z119,z1,z2,z4,z47,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6]),(0,[z1,z2,z84,z3,z4,z5,z6])],[(1,[z1,z2,z237,z3,z4,z6]),(0,[z1,z2,z690,z3,z4,z5,z6]),(0,[z33,z2,z3,z4,z34,z5,z6]),(0,[z1,z26,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z6,z13]),(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z1,z2,z84,z3,z4,z5,z90]),(0,[z302,z1,z2,z3,z4,z5,z13])],[(0,[z691,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z81,z6]),(0,[z1,z2,z3,z692,z4,z5,z6]),(0,[z107,z1,z2,z3,z4,z5,z6]),(0,[z1,z507,z2,z3,z4,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z65,z4,z5,z24]),(0,[z1,z2,z3,z4,z69,z5,z174]),(0,[z1,z2,z79,z3,z4,z5,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z695,z5,z6])],[(0,[z1,z2,z3,z696,z4,z5,z6]),(0,[z104,z1,z26,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z697,z6]),(0,[z1,z2,z3,z4,z5,z6,z698]),(0,[z699,z1,z2,z3,z4,z5,z6])],[(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z1,z70,z2,z3,z4,z5,z6]),(0,[z94,z1,z2,z95,z4,z5,z6]),(0,[z700,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z6]),(0,[z1,z701,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z660]),(0,[z1,z2,z3,z4,z12,z5,z660]),(0,[z1,z2,z3,z702,z4,z5,z6]),(1,[z1,z40,z3,z47,z5,z6]),(0,[z1,z40,z3,z4,z47,z5,z6]),(0,[z54,z1,z2,z272,z4,z5,z6]),(1,[z1,z2,z3,z480,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z221]),(0,[z422,z1,z2,z3,z4,z5,z24])],[(1,[z72,z2,z62,z4,z5,z6]),(0,[z1,z2,z703,z3,z4,z5,z6])],[(0,[z1,z2,z3,z704,z4,z5,z6]),(1,[z1,z2,z3,z4,z214,z6]),(0,[z1,z2,z3,z4,z5,z549,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z77,z2,z3,z4,z5,z71]),(0,[z1,z2,z82,z3,z4,z5,z83]),(0,[z706,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z24])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z707])],[(0,[z1,z2,z3,z708,z5,z6]),(1,[z1,z3,z709,z5,z6])],[(0,[z1,z2,z3,z4,z5,z710]),(0,[z711,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z712])],[(0,[z1,z2,z3,z4,z713,z5]),(0,[z38,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z213,z5,z13])],[(0,[z1,z2,z3,z4,z5,z714]),(0,[z1,z2,z3,z4,z715,z6]),(0,[z1,z2,z3,z105,z5,z6])],[(0,[z1,z2,z3,z97,z81,z13]),(0,[z91,z1,z2,z3,z293,z5]),(0,[z1,z26,z215,z4,z5,z6]),(0,[z1,z2,z439,z3,z4,z13])],[],[(0,[z249,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z643,z81,z6]),(0,[z1,z2,z3,z4,z7,z283])],[(0,[z1,z2,z45,z4,z5,z6])],[(0,[z86,z1,z2,z3,z4,z370]),(0,[z1,z156,z507,z3,z5,z6])],[(0,[z365,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z2,z3,z293,z5,z153]),(0,[z1,z717,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z468,z24])],[(0,[z131,z1,z2,z4,z5,z344])],[(0,[z136,z37,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z718]),(0,[z1,z2,z3,z636,z5,z6]),(0,[z1,z2,z48,z4,z5,z157])],[],[(0,[z1,z2,z3,z4,z719,z6]),(0,[z104,z1,z109,z4,z309,z6]),(0,[z720,z2,z3,z4,z5,z6]),(0,[z1,z2,z508,z3,z4,z13]),(0,[z86,z1,z3,z4,z5,z456]),(0,[z1,z2,z3,z4,z438,z13]),(0,[z1,z2,z3,z4,z190,z13])],[(0,[z201,z150,z3,z4,z5,z6]),(0,[z721,z2,z3,z4,z5,z13])]],
   [[(0,[z2,z3,z97,z722,z5,z6]),(0,[z1,z2,z3,z4,z441,z13]),(0,[z1,z2,z48,z480,z5,z6]),(0,[z28,z201,z2,z5,z114,z6])],[(0,[z1,z2,z3,z4,z5,z723]),(0,[z1,z2,z17,z84,z3,z115])],[(0,[z1,z724,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z725,z6]),(0,[z523,z2,z3,z4,z30,z13]),(0,[z1,z2,z266,z4,z5,z13])],[(0,[z1,z2,z3,z726,z5,z6]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z728,z4,z5,z6]),(0,[z2,z3,z4,z5,z13,z729])],[(0,[z1,z2,z272,z4,z5,z13])],[(0,[z1,z123,z3,z4,z5,z13]),(0,[z226,z2,z3,z4,z12,z189]),(0,[z1,z2,z3,z4,z450,z13]),(0,[z1,z2,z3,z4,z5,z730])],[(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z26,z3,z105,z5,z6]),(0,[z1,z270,z2,z17,z84,z6])],[(0,[z1,z2,z3,z8,z4,z248]),(0,[z1,z181,z2,z443,z4,z6])],[(0,[z1,z2,z3,z732,z5,z6]),(0,[z1,z2,z733,z3,z5,z6])],[],[(0,[z284,z60,z3,z4,z5,z6])],[(0,[z1,z55,z624,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z185])],[(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z2,z3,z722,z5,z6]),(0,[z1,z2,z3,z34,z81,z13]),(0,[z735,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z736,z5,z24])],[(0,[z1,z2,z17,z341,z3,z6]),(0,[z1,z150,z3,z4,z253,z6])],[(0,[z138,z2,z3,z4,z30,z13]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z14,z2,z308,z4,z5,z15])],[(0,[z1,z2,z3,z738,z5,z6]),(0,[z616,z1,z2,z4,z5,z153]),(0,[z1,z2,z3,z4,z5,z739])]],
   [[(0,[z1,z2,z3,z4,z405,z13]),(0,[z560,z1,z2,z3,z293,z5]),(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z2,z3,z4,z5,z157]),(0,[z1,z2,z3,z4,z300,z13])],[(0,[z1,z2,z237,z3,z4,z6]),(0,[z1,z2,z741,z4,z5,z6]),(0,[z1,z304,z2,z3,z4,z13]),(0,[z742,z2,z3,z4,z5,z13])],[(0,[z1,z242,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z468,z83])],[(0,[z1,z2,z3,z4,z743,z6]),(0,[z121,z1,z2,z3,z4,z13])],[(0,[z1,z40,z3,z47,z5,z6]),(0,[z1,z2,z3,z480,z5,z6]),(0,[z1,z2,z3,z4,z744,z6]),(1,[z1,z2,z745,z4,z6])],[(0,[z72,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z487,z13]),(0,[z1,z2,z3,z4,z370,z153]),(0,[z1,z2,z3,z4,z488,z13]),(0,[z1,z2,z295,z3,z81,z6]),(0,[z1,z2,z3,z4,z489,z13])],[(0,[z1,z2,z3,z4,z490,z13]),(0,[z1,z2,z3,z4,z491,z13]),(0,[z137,z2,z3,z4,z9,z6]),(0,[z1,z2,z4,z80,z262,z13])],[(0,[z1,z2,z3,z4,z496,z13]),(0,[z1,z3,z629,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z746])],[(0,[z104,z1,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z747])],[(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z3,z225,z4,z13]),(0,[z107,z2,z3,z4,z371,z5]),(0,[z1,z3,z709,z47,z5,z6]),(0,[z1,z2,z3,z749,z81,z6])],[(0,[z1,z2,z266,z4,z5,z6]),(0,[z523,z2,z3,z4,z30,z6]),(0,[z107,z2,z547,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z750])],[(0,[z1,z2,z751,z3,z4,z5]),(0,[z96,z2,z3,z97,z5,z13]),(0,[z2,z3,z4,z5,z184,z752]),(0,[z753,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z418,z5,z210]),(0,[z1,z2,z3,z89,z4,z13])],[(0,[z1,z2,z3,z4,z5,z754]),(0,[z1,z2,z272,z4,z5,z6]),(0,[z208,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z221]),(0,[z54,z1,z3,z4,z76,z13]),(0,[z1,z181,z2,z295,z8,z6])],[(0,[z1,z2,z3,z4,z5,z755]),(0,[z54,z1,z427,z3,z4,z6]),(0,[z1,z123,z3,z4,z5,z357])],[(0,[z37,z1,z2,z3,z4,z5]),(0,[z2,z3,z4,z12,z756,z6]),(0,[z1,z2,z3,z4,z757,z6])],[(0,[z1,z2,z308,z4,z170,z6]),(0,[z1,z319,z3,z4,z5,z413])]],
   [[(0,[z1,z2,z3,z758,z5,z6])],[(0,[z1,z2,z3,z4,z370,z292]),(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z2,z3,z760,z5,z6]),(0,[z42,z1,z3,z4,z5,z71])],[(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z2,z3,z4,z5,z762]),(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z150,z3,z4,z5,z310]),(0,[z1,z2,z3,z8,z418,z13])],[(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z2,z4,z765,z5,z6]),(0,[z1,z2,z3,z4,z145,z13])],[(0,[z1,z2,z3,z293,z5,z6]),(0,[z1,z2,z3,z108,z503,z5]),(0,[z1,z2,z295,z3,z5,z6])],[(0,[z382,z2,z95,z4,z5,z6]),(0,[z119,z1,z2,z4,z5,z723]),(0,[z1,z3,z4,z5,z113,z766])],[(0,[z1,z2,z3,z767,z5,z6]),(0,[z1,z2,z768,z4,z5,z6]),(0,[z1,z2,z769,z4,z5,z6]),(0,[z110,z2,z3,z64,z30,z6]),(0,[z1,z2,z3,z4,z770,z6])],[(0,[z110,z427,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z370,z13]),(0,[z28,z1,z561,z2,z5,z6]),(0,[z54,z137,z3,z4,z76,z6]),(0,[z1,z2,z771,z4,z5,z6])],[(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z2,z3,z4,z530,z13]),(0,[z1,z2,z3,z501,z81,z6]),(0,[z209,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z418,z5,z400]),(0,[z1,z2,z3,z749,z5,z6])],[(0,[z1,z2,z474,z64,z5,z6]),(0,[z1,z2,z774,z4,z5,z6]),(0,[z1,z608,z2,z3,z4,z13])],[(0,[z168,z1,z2,z4,z5,z153]),(0,[z1,z2,z775,z4,z5,z6]),(0,[z226,z427,z3,z4,z5,z6])],[(0,[z1,z2,z3,z776,z4,z6]),(0,[z1,z2,z3,z4,z386,z13]),(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z2,z3,z225,z4,z778]),(0,[z779,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z780,z6]),(0,[z1,z2,z18,z363,z5,z6])],[(0,[z136,z1,z2,z781,z4,z6])],[(0,[z136,z1,z2,z782,z4,z6]),(0,[z669,z2,z95,z4,z5,z6]),(0,[z1,z2,z783,z3,z4,z6]),(0,[z1,z2,z142,z3,z4,z13]),(0,[z1,z2,z3,z5,z784,z283])],[(0,[z1,z2,z3,z4,z6,z785]),(0,[z226,z2,z3,z4,z12,z13]),(0,[z1,z2,z3,z4,z5,z786])],[(0,[z274,z70,z3,z4,z5,z6]),(0,[z1,z2,z653,z4,z80,z6]),(0,[z28,z1,z2,z5,z114,z310]),(0,[z1,z2,z3,z4,z787,z6]),(0,[z1,z2,z3,z4,z545,z13])]],
   [[],[(0,[z1,z2,z3,z788,z5,z6]),(0,[z1,z2,z3,z789,z5,z6]),(0,[z1,z156,z3,z65,z5,z13]),(0,[z1,z2,z790,z4,z5,z6]),(0,[z1,z2,z48,z4,z5,z24]),(0,[z1,z2,z89,z4,z6,z13])],[(1,[z2,z3,z4,z756,z6]),(0,[z14,z2,z3,z4,z5,z134])],[(0,[z1,z2,z782,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z791]),(0,[z1,z2,z3,z4,z5,z792]),(1,[z1,z2,z3,z5,z784])],[(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z77,z3,z4,z113,z78]),(0,[z1,z2,z3,z418,z9,z6])],[],[(0,[z1,z2,z3,z4,z5,z794]),(0,[z119,z1,z156,z2,z5,z6]),(0,[z1,z2,z3,z73,z81,z373])],[(0,[z138,z70,z3,z4,z5,z6]),(0,[z1,z2,z795,z4,z5,z6])],[(0,[z72,z2,z62,z4,z63,z6])],[(0,[z1,z2,z3,z4,z5,z796]),(0,[z1,z797,z3,z4,z5,z6])],[(0,[z1,z2,z3,z798,z5,z6]),(0,[z1,z799,z3,z4,z5,z6]),(0,[z1,z2,z313,z4,z80,z6]),(0,[z137,z2,z3,z4,z5,z157])],[(1,[z2,z800,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z370])],[(0,[z1,z2,z3,z4,z24,z13])],[(0,[z1,z2,z3,z801,z5,z6])],[(0,[z1,z2,z3,z4,z5,z802]),(0,[z137,z2,z3,z480,z5,z6]),(0,[z803,z2,z3,z4,z5,z6]),(0,[z256,z2,z3,z4,z5,z292])],[(0,[z1,z2,z3,z4,z370,z6]),(0,[z14,z242,z3,z4,z5,z15]),(0,[z103,z2,z3,z4,z309,z6]),(1,[z1,z804,z4,z5,z6]),(0,[z1,z2,z3,z4,z805,z6]),(0,[z1,z806,z3,z4,z5,z6]),(0,[z28,z1,z2,z5,z114,z29]),(0,[z1,z2,z745,z4,z80,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z807]),(0,[z226,z137,z2,z3,z4,z6]),(0,[z1,z111,z3,z4,z170,z6])],[(0,[z37,z1,z242,z3,z4,z5]),(0,[z1,z2,z808,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z809]),(0,[z1,z2,z3,z4,z57,z6])],[(0,[z1,z2,z3,z4,z810,z6]),(0,[z1,z427,z3,z64,z5,z6]),(0,[z1,z2,z3,z4,z363,z13])],[(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z3,z4,z744,z76,z6]),(0,[z1,z2,z79,z4,z80,z6]),(0,[z1,z2,z3,z812,z5,z6])],[(0,[z1,z2,z813,z3,z4,z5]),(0,[z1,z2,z3,z4,z277,z13]),(0,[z1,z181,z2,z8,z4,z400]),(0,[z1,z2,z3,z4,z5,z187])],[(0,[z1,z2,z3,z4,z5,z24]),(0,[z56,z2,z3,z4,z5,z6]),(0,[z1,z2,z814,z4,z5,z6]),(0,[z85,z1,z3,z4,z5,z71])],[],[(0,[z1,z2,z815,z4,z5,z6]),(0,[z1,z816,z3,z4,z5,z13])],[(0,[z1,z2,z3,z817,z5,z6])],[(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z454,z3,z47,z5,z6])],[(0,[z1,z100,z3,z4,z5,z6]),(0,[z1,z819,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z821,z4,z5,z6]),(0,[z1,z2,z48,z4,z5,z221]),(0,[z1,z822,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z823]),(1,[z1,z2,z3,z4,z824])],[(0,[z1,z2,z3,z213,z5,z6]),(0,[z1,z2,z211,z4,z5,z153])],[(0,[z1,z2,z825,z4,z5,z6]),(0,[z91,z1,z2,z3,z5,z784])]],
   [[(0,[z1,z2,z66,z4,z214,z6]),(0,[z1,z77,z3,z4,z300,z113]),(0,[z201,z181,z2,z4,z5,z6]),(0,[z1,z2,z84,z3,z4,z400]),(0,[z1,z2,z3,z4,z7,z24])],[(0,[z1,z2,z3,z4,z5,z826]),(0,[z110,z2,z474,z4,z30,z6]),(0,[z1,z111,z308,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z827]),(0,[z1,z2,z4,z5,z83,z707])],[(0,[z1,z2,z3,z8,z4,z13])],[(0,[z116,z1,z2,z3,z4,z13])],[(0,[z1,z2,z3,z4,z628,z13]),(0,[z1,z2,z3,z4,z828,z6]),(0,[z1,z2,z3,z4,z633,z13])],[(0,[z1,z2,z3,z829,z5,z6]),(0,[z269,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z558,z4,z13])],[(1,[z830,z3,z4,z5,z6]),(0,[z33,z2,z3,z34,z5,z24]),(0,[z1,z2,z3,z831,z4,z6])],[(0,[z1,z2,z3,z4,z5,z832])],[(0,[z72,z2,z645,z4,z5,z6])],[(0,[z1,z2,z574,z4,z5,z83]),(0,[z1,z2,z3,z4,z190,z6]),(0,[z577,z1,z2,z3,z5,z283])],[(0,[z551,z2,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z833]),(0,[z1,z156,z100,z3,z5,z6]),(0,[z721,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z834])],[(0,[z119,z1,z2,z105,z5,z6]),(0,[z1,z2,z3,z835,z5,z6]),(0,[z1,z2,z341,z3,z4,z13])],[],[(0,[z1,z2,z3,z4,z5,z836]),(0,[z1,z70,z55,z3,z4,z13]),(0,[z1,z2,z3,z837,z5,z6]),(0,[z838,z2,z3,z4,z5,z6]),(0,[z360,z2,z3,z238,z5,z6]),(0,[z1,z55,z3,z4,z69,z24]),(0,[z28,z1,z2,z521,z5,z6]),(0,[z1,z2,z3,z4,z647,z13])],[(0,[z1,z2,z839,z4,z5,z6]),(0,[z1,z181,z2,z4,z253,z6])],[(0,[z1,z2,z3,z4,z5,z840]),(0,[z1,z2,z3,z4,z81,z13]),(0,[z1,z2,z17,z84,z3,z24]),(0,[z1,z2,z3,z4,z344,z13])]],
   [[(0,[z1,z123,z3,z4,z5,z6]),(0,[z841,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z2,z3,z4,z6,z843]),(0,[z1,z2,z66,z4,z80,z13])],[(0,[z226,z2,z3,z4,z522,z6]),(0,[z1,z2,z3,z4,z5,z844])],[(0,[z1,z2,z3,z4,z411,z13]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z2,z3,z443,z4,z13]),(0,[z54,z1,z48,z4,z76,z6]),(0,[z1,z477,z2,z8,z4,z6])],[(0,[z1,z2,z846,z4,z5,z6]),(0,[z1,z2,z3,z480,z6,z13])],[(0,[z1,z2,z847,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z248]),(0,[z1,z2,z3,z4,z468,z13])],[(0,[z1,z2,z3,z4,z848,z6])],[(0,[z1,z2,z3,z4,z63,z24]),(0,[z119,z849,z2,z4,z5,z6]),(0,[z1,z2,z84,z3,z81,z13])],[(0,[z1,z2,z3,z4,z5,z850]),(0,[z119,z1,z2,z4,z5,z24]),(1,[z1,z2,z3,z480,z13]),(0,[z1,z2,z683,z3,z4,z13]),(0,[z1,z2,z3,z4,z851,z6])],[(0,[z136,z1,z2,z3,z852,z6])],[(0,[z1,z701,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z300,z6]),(0,[z2,z3,z4,z5,z6,z853])],[(0,[z1,z2,z3,z4,z309,z185]),(0,[z1,z55,z2,z3,z4,z118]),(0,[z742,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z854,z5]),(0,[z1,z427,z474,z4,z5,z6]),(0,[z263,z2,z3,z4,z5,z185])],[(0,[z1,z2,z3,z855,z5,z6]),(0,[z226,z1,z2,z48,z4,z6]),(0,[z1,z3,z4,z5,z766,z71])],[(0,[z856,z2,z3,z4,z5,z6]),(0,[z137,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z59,z2,z3,z4,z13]),(0,[z1,z2,z326,z4,z5,z83])]],
   [[(0,[z857,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z33,z2,z3,z722,z5,z6]),(0,[z1,z2,z295,z3,z253,z6]),(0,[z1,z2,z3,z4,z9,z210])],[(0,[z1,z2,z45,z64,z5,z6]),(0,[z1,z2,z66,z105,z5,z6]),(0,[z1,z181,z507,z2,z5,z6]),(0,[z1,z2,z3,z4,z5,z859])],[(0,[z1,z2,z4,z860,z5,z6]),(0,[z1,z2,z3,z4,z5,z861]),(0,[z1,z862,z3,z4,z5,z6])],[(0,[z1,z2,z3,z149,z5,z24])],[(0,[z1,z2,z3,z225,z4,z6]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z28,z1,z100,z5,z114,z6]),(0,[z1,z2,z3,z4,z420,z13])],[(0,[z1,z150,z3,z4,z5,z29]),(0,[z1,z2,z235,z66,z5,z6])],[(0,[z1,z2,z3,z4,z864,z6]),(0,[z96,z2,z3,z97,z5,z6])],[(0,[z1,z2,z3,z4,z865,z6]),(0,[z54,z1,z3,z4,z76,z6]),(0,[z1,z2,z3,z5,z152,z784])],[(0,[z36,z830,z3,z4,z5,z6]),(0,[z263,z2,z3,z4,z214,z6]),(0,[z1,z2,z372,z3,z4,z13])],[],[(0,[z1,z2,z866,z4,z5,z6]),(0,[z136,z1,z427,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z4,z594,z13]),(0,[z1,z2,z3,z4,z868,z6]),(0,[z1,z181,z2,z8,z4,z210])],[(0,[z14,z2,z3,z213,z5,z15]),(0,[z28,z1,z150,z5,z114,z6]),(0,[z1,z2,z3,z4,z869,z6])],[(0,[z1,z2,z3,z4,z5,z870])],[(0,[z1,z2,z3,z4,z370,z15]),(0,[z14,z1,z2,z3,z4,z7]),(0,[z1,z2,z3,z65,z81,z13]),(0,[z1,z2,z3,z4,z5,z871])],[(0,[z125,z1,z2,z4,z5,z344]),(0,[z1,z2,z3,z4,z145,z6])],[(0,[z256,z2,z3,z4,z5,z184]),(0,[z201,z2,z3,z4,z57,z6]),(0,[z1,z2,z3,z4,z145,z90])]],
   [[(0,[z1,z55,z60,z3,z4,z13]),(0,[z1,z2,z872,z4,z5,z6]),(0,[z684,z1,z2,z3,z4,z13])],[(0,[z1,z479,z2,z3,z4,z13])],[(0,[z86,z1,z242,z3,z4,z5])],[(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z804,z109,z4,z5,z6]),(0,[z201,z2,z3,z4,z5,z24])],[(0,[z136,z226,z2,z3,z4,z6]),(0,[z874,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z875,z6]),(0,[z876,z2,z3,z4,z5,z13])],[(0,[z1,z877,z2,z4,z5,z6]),(0,[z1,z2,z343,z4,z80,z6]),(0,[z1,z270,z2,z4,z80,z6])],[(0,[z110,z2,z3,z4,z756,z6]),(0,[z1,z77,z3,z4,z5,z766])],[(0,[z878,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z90,z13]),(0,[z1,z879,z3,z4,z5,z24])],[(0,[z1,z2,z3,z880,z5,z6]),(0,[z1,z2,z3,z4,z5,z189]),(0,[z119,z1,z2,z4,z5,z759]),(0,[z201,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z881]),(0,[z1,z2,z17,z84,z3,z13]),(0,[z206,z1,z2,z3,z5,z511])],[(0,[z1,z2,z882,z4,z5,z6]),(0,[z226,z2,z3,z4,z12,z6]),(0,[z137,z2,z272,z4,z5,z6]),(0,[z137,z2,z3,z4,z5,z221]),(0,[z54,z360,z2,z3,z4,z13]),(0,[z1,z2,z84,z3,z4,z373])],[(0,[z14,z2,z266,z4,z5,z15]),(0,[z54,z1,z2,z3,z480,z13]),(0,[z1,z2,z84,z3,z4,z883])],[(0,[z1,z2,z3,z884,z5,z6]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z270,z2,z4,z5,z24]),(0,[z1,z886,z3,z4,z5,z13])],[(0,[z1,z2,z3,z887,z5,z6]),(0,[z1,z2,z3,z888,z5,z6]),(0,[z1,z156,z3,z65,z5,z6])],[(0,[z1,z2,z3,z108,z5,z152])],[(0,[z1,z2,z3,z4,z5,z889])],[(0,[z1,z2,z3,z4,z5,z890])]],
   [[(0,[z1,z2,z3,z671,z4,z13]),(0,[z1,z2,z3,z736,z5,z6]),(0,[z1,z2,z3,z4,z5,z549]),(0,[z1,z2,z3,z4,z6,z891]),(0,[z1,z2,z3,z745,z4,z6])],[(0,[z136,z1,z3,z4,z76,z6]),(0,[z1,z2,z3,z4,z892,z6]),(0,[z226,z2,z3,z4,z12,z660]),(0,[z1,z27,z804,z4,z5,z6]),(0,[z1,z2,z3,z4,z80,z118]),(0,[z56,z2,z3,z4,z253,z6]),(0,[z1,z2,z3,z4,z253,z24])],[(0,[z1,z26,z100,z4,z5,z6]),(0,[z234,z1,z2,z4,z5,z153])],[(0,[z1,z242,z3,z4,z170,z6]),(0,[z86,z1,z2,z3,z4,z78])],[(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z14,z2,z3,z293,z5,z15]),(0,[z1,z2,z3,z129,z309,z6]),(0,[z1,z2,z79,z745,z4,z6]),(0,[z1,z2,z8,z745,z4,z6])],[(0,[z1,z2,z3,z4,z240,z13]),(0,[z263,z2,z3,z129,z5,z6]),(0,[z1,z2,z3,z4,z6,z824])],[(0,[z110,z2,z3,z133,z4,z6]),(0,[z422,z1,z2,z3,z4,z13]),(0,[z1,z100,z3,z4,z253,z6])],[(0,[z1,z2,z308,z4,z5,z68]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z137,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z468,z153]),(0,[z85,z1,z3,z4,z5,z154])],[(0,[z1,z2,z3,z105,z309,z6])],[(0,[z1,z2,z3,z4,z5,z895]),(0,[z110,z2,z45,z4,z30,z6]),(0,[z263,z2,z3,z105,z5,z6]),(0,[z1,z2,z3,z19,z81,z6])],[(0,[z103,z2,z3,z4,z5,z185]),(0,[z1,z2,z3,z4,z157,z13])],[(0,[z1,z2,z266,z4,z170,z6]),(0,[z137,z3,z4,z5,z76,z6]),(0,[z201,z2,z4,z5,z80,z6]),(0,[z1,z2,z18,z3,z81,z13])],[(0,[z1,z896,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z104,z1,z109,z4,z5,z185]),(0,[z54,z1,z55,z3,z4,z13])],[(0,[z1,z2,z3,z4,z63,z867]),(0,[z110,z2,z3,z636,z30,z6]),(0,[z1,z2,z48,z4,z5,z13])],[(0,[z553,z60,z3,z4,z5,z6]),(0,[z119,z1,z2,z4,z868,z6])],[(0,[z1,z2,z3,z4,z898,z6]),(0,[z1,z2,z3,z4,z5,z899]),(0,[z1,z2,z900,z4,z5,z6]),(0,[z104,z263,z109,z4,z5,z6]),(0,[z901,z2,z3,z4,z5,z6])]],
   [[(0,[z138,z245,z3,z4,z5,z6]),(0,[z201,z2,z3,z5,z81,z6]),(0,[z1,z100,z17,z3,z5,z6]),(0,[z1,z2,z3,z4,z902,z6])],[(0,[z1,z903,z3,z4,z5,z6]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z905])],[(0,[z1,z2,z3,z4,z24,z670]),(0,[z1,z2,z3,z4,z57,z310]),(0,[z28,z1,z2,z5,z906,z6]),(0,[z1,z816,z3,z4,z5,z6])],[(0,[z1,z886,z3,z4,z5,z6])],[(0,[z1,z907,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z674,z24]),(0,[z104,z1,z507,z109,z5,z6]),(0,[z1,z2,z3,z4,z5,z881]),(0,[z1,z2,z3,z4,z5,z908]),(0,[z1,z2,z3,z909,z5,z13])],[(0,[z1,z2,z3,z293,z170,z6]),(0,[z1,z2,z3,z4,z370,z184]),(0,[z1,z77,z2,z3,z4,z370]),(0,[z103,z2,z3,z4,z214,z6]),(0,[z1,z2,z3,z910,z5,z6])],[(0,[z1,z2,z3,z4,z309,z24]),(0,[z56,z2,z3,z4,z5,z310]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z28,z1,z151,z2,z5,z6])],[(0,[z263,z2,z3,z4,z5,z24]),(0,[z104,z1,z109,z4,z214,z6]),(0,[z1,z507,z100,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z912]),(0,[z1,z2,z3,z133,z4,z13])],[(0,[z1,z2,z913,z4,z5,z6]),(0,[z1,z2,z3,z235,z4,z13]),(0,[z1,z270,z2,z5,z81,z6])],[(0,[z1,z2,z3,z108,z5,z599])],[(0,[z1,z2,z3,z4,z5,z914])],[(0,[z1,z915,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z916,z6]),(0,[z1,z100,z3,z4,z5,z310])],[(0,[z1,z2,z917,z4,z5,z6]),(0,[z226,z2,z3,z4,z216,z6]),(0,[z1,z2,z525,z4,z5,z153]),(0,[z1,z2,z3,z918,z5,z6]),(0,[z1,z2,z3,z4,z210,z13])],[(0,[z1,z2,z3,z5,z6,z919]),(0,[z1,z2,z3,z4,z57,z920]),(0,[z2,z3,z4,z5,z6,z729])],[],[(0,[z1,z2,z3,z4,z921,z6]),(0,[z1,z2,z3,z4,z756,z6]),(0,[z14,z2,z3,z4,z370,z15]),(0,[z1,z2,z3,z4,z223,z13]),(0,[z631,z1,z2,z3,z4,z13]),(0,[z1,z2,z922,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z923,z4,z6]),(0,[z1,z2,z482,z66,z5,z6]),(0,[z1,z2,z3,z4,z480,z13]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z270,z2,z8,z4,z6])],[(0,[z1,z2,z3,z4,z5,z13]),(0,[z2,z3,z4,z5,z752,z15])],[(0,[z389,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z14,z281,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z926])],[(0,[z1,z2,z3,z4,z5,z927]),(0,[z1,z3,z4,z69,z744,z6]),(0,[z1,z2,z4,z5,z707,z153]),(0,[z1,z2,z17,z84,z89,z6])],[(0,[z1,z2,z3,z4,z5,z928]),(0,[z1,z2,z3,z704,z4,z13]),(0,[z1,z2,z3,z4,z929,z6]),(0,[z119,z1,z2,z5,z114,z6]),(0,[z1,z2,z4,z46,z5,z24]),(0,[z1,z2,z18,z303,z5,z6]),(0,[z1,z270,z2,z4,z5,z13])],[(0,[z1,z427,z45,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z420]),(0,[z1,z2,z79,z4,z80,z202]),(0,[z1,z2,z295,z3,z5,z400])],[(0,[z1,z2,z3,z4,z930,z6]),(0,[z56,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z931])],[(0,[z2,z830,z3,z4,z5,z6]),(0,[z1,z2,z932,z3,z5,z6]),(0,[z1,z2,z3,z676,z81,z6])],[(0,[z1,z2,z800,z4,z5,z6]),(0,[z1,z2,z3,z64,z80,z6]),(0,[z1,z2,z3,z8,z64,z6]),(0,[z1,z181,z100,z4,z5,z6]),(0,[z28,z1,z2,z57,z114,z6])],[(0,[z264,z2,z95,z4,z5,z6]),(0,[z1,z427,z3,z636,z5,z6]),(0,[z1,z2,z4,z5,z6,z707])],[(0,[z226,z2,z508,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z933])],[],[(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z2,z3,z935,z5,z6]),(0,[z1,z2,z3,z4,z7,z13]),(0,[z1,z2,z89,z4,z5,z115]),(0,[z1,z2,z3,z909,z5,z6]),(0,[z1,z2,z936,z4,z5,z24])],[(0,[z1,z2,z3,z4,z5,z937]),(0,[z938,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z784])],[(0,[z136,z1,z2,z3,z939,z6]),(0,[z1,z2,z940,z4,z5,z6]),(0,[z1,z2,z3,z64,z5,z24]),(0,[z107,z2,z3,z4,z5,z291]),(1,[z1,z2,z3,z749,z6])],[(0,[z1,z2,z5,z906,z114,z6])]],
   [[],[(0,[z1,z156,z3,z381,z5,z6]),(0,[z1,z2,z3,z4,z468,z6]),(0,[z1,z2,z89,z4,z9,z6])],[(0,[z33,z2,z3,z34,z5,z13]),(0,[z103,z2,z3,z129,z5,z6]),(0,[z1,z3,z804,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z3,z4,z5,z778])],[(0,[z104,z1,z109,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z942])],[],[(0,[z1,z2,z3,z4,z5,z943]),(0,[z1,z2,z62,z4,z80,z13]),(0,[z1,z2,z3,z4,z292,z13]),(0,[z1,z2,z3,z4,z170,z24]),(0,[z103,z2,z3,z105,z5,z6]),(0,[z1,z2,z407,z84,z3,z6])],[(0,[z1,z2,z3,z4,z5,z944])],[(0,[z104,z1,z109,z105,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z94,z2,z800,z4,z5,z6]),(0,[z72,z2,z247,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z357]),(0,[z119,z1,z2,z5,z81,z6]),(0,[z945,z1,z2,z4,z5,z6]),(0,[z1,z2,z946,z4,z5,z6]),(0,[z1,z55,z3,z4,z69,z13]),(0,[z1,z2,z745,z4,z5,z6])],[(0,[z1,z2,z781,z4,z5,z6]),(1,[z1,z3,z4,z744,z6]),(0,[z1,z2,z3,z4,z5,z90]),(0,[z1,z2,z3,z4,z9,z824])],[],[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z2,z109,z4,z214,z6]),(0,[z1,z2,z3,z465,z5,z152])],[(0,[z948,z1,z2,z237,z3,z4])],[(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z3,z939,z5,z6]),(0,[z360,z2,z3,z4,z5,z157])],[(0,[z1,z2,z3,z213,z170,z6]),(0,[z1,z2,z3,z4,z5,z950]),(0,[z627,z1,z2,z3,z4,z13])]],
   [[(0,[z1,z2,z218,z3,z4,z13]),(0,[z104,z103,z109,z4,z5,z6]),(0,[z104,z1,z149,z109,z5,z6]),(0,[z1,z2,z3,z418,z5,z24])],[(0,[z2,z60,z3,z4,z30,z13]),(0,[z1,z2,z3,z4,z5,z951])],[(0,[z360,z2,z3,z480,z5,z6])],[(0,[z1,z830,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z63,z13]),(0,[z952,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z239,z5,z283])],[(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z119,z1,z2,z4,z5,z13]),(0,[z955,z1,z2,z3,z4,z5])],[(0,[z1,z2,z956,z3,z4,z5]),(0,[z1,z957,z2,z4,z5,z6]),(0,[z104,z1,z109,z4,z5,z24]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z959,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z6,z960]),(0,[z1,z111,z3,z293,z5,z6]),(0,[z107,z1,z2,z3,z4,z7]),(0,[z1,z100,z3,z66,z5,z6])],[(0,[z1,z2,z961,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z164])],[(0,[z1,z123,z3,z64,z5,z6]),(0,[z1,z2,z18,z66,z5,z24]),(0,[z1,z2,z3,z4,z468,z277])],[(0,[z1,z2,z3,z962,z5,z6]),(0,[z33,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z348,z13]),(0,[z963,z2,z3,z4,z5,z6]),(0,[z1,z964,z3,z4,z5,z6])],[(0,[z1,z2,z965,z4,z5,z6]),(0,[z1,z2,z3,z4,z182,z5]),(0,[z1,z2,z966,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z967]),(0,[z137,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z643,z4,z13])],[(0,[z1,z2,z3,z968,z5,z6])],[(0,[z1,z2,z109,z4,z80,z13]),(0,[z1,z2,z4,z46,z5,z13]),(0,[z1,z2,z3,z4,z190,z210])],[(0,[z1,z2,z3,z4,z5,z969]),(0,[z970,z1,z2,z3,z4,z5])],[(0,[z72,z2,z800,z4,z5,z6]),(0,[z1,z2,z3,z64,z5,z248]),(0,[z1,z2,z3,z149,z5,z13]),(0,[z876,z2,z3,z4,z5,z6]),(0,[z1,z2,z211,z4,z5,z287]),(0,[z1,z2,z282,z3,z5,z349])]],
   [[],[(0,[z1,z2,z82,z4,z5,z68]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z55,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z881,z13])],[],[(0,[z1,z2,z474,z636,z5,z6]),(0,[z1,z2,z17,z84,z3,z6])],[(0,[z1,z2,z3,z4,z972,z6]),(1,[z1,z2,z3,z418,z13]),(0,[z1,z2,z17,z84,z3,z90])],[(0,[z36,z37,z60,z3,z4,z5]),(0,[z1,z26,z27,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z973]),(0,[z110,z2,z3,z4,z30,z24]),(0,[z974,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z238,z5,z157])],[(0,[z1,z242,z308,z4,z5,z6]),(0,[z1,z593,z2,z8,z4,z6]),(0,[z1,z2,z3,z73,z81,z187])],[(0,[z427,z3,z4,z5,z30,z6]),(0,[z1,z2,z45,z636,z5,z6]),(1,[z1,z2,z5,z906,z6]),(0,[z1,z2,z3,z73,z81,z24])],[(0,[z119,z1,z40,z2,z5,z6]),(0,[z975,z2,z3,z4,z5,z6])],[(0,[z1,z55,z427,z3,z4,z6]),(0,[z2,z3,z4,z12,z30,z13]),(0,[z1,z507,z2,z5,z80,z6])],[(0,[z252,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z976]),(0,[z54,z1,z3,z4,z744,z6]),(0,[z1,z2,z295,z3,z5,z210])],[(0,[z1,z2,z3,z4,z63,z6])],[],[(0,[z1,z2,z3,z977,z5,z6]),(0,[z560,z1,z2,z3,z4,z810])],[(0,[z1,z2,z308,z4,z5,z83]),(0,[z201,z2,z3,z4,z5,z13])]],
   [[(1,[z2,z3,z4,z5,z752]),(0,[z1,z2,z3,z4,z9,z157]),(0,[z91,z1,z2,z3,z145,z283])],[(0,[z1,z2,z95,z4,z80,z13]),(0,[z978,z2,z3,z4,z5,z6]),(0,[z1,z77,z3,z4,z5,z113]),(0,[z1,z2,z3,z979,z5,z13])],[(0,[z1,z2,z3,z4,z5,z980]),(0,[z138,z316,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z2,z272,z238,z5,z6]),(0,[z1,z2,z3,z238,z5,z221]),(0,[z1,z2,z3,z4,z982,z5])],[(0,[z1,z2,z3,z983,z5,z6]),(0,[z1,z2,z3,z4,z34,z810]),(0,[z1,z2,z3,z4,z984,z6])],[(0,[z1,z2,z3,z985,z5,z6]),(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z2,z3,z480,z9,z6])],[(0,[z706,z2,z3,z34,z5,z6]),(0,[z1,z988,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z66,z705,z5,z6]),(0,[z1,z2,z3,z4,z990,z6]),(0,[z1,z2,z3,z4,z57,z29])],[(0,[z1,z2,z3,z47,z81,z13]),(0,[z1,z557,z3,z65,z5,z6])],[(0,[z1,z2,z3,z149,z5,z6]),(0,[z119,z1,z26,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z991])],[(0,[z1,z2,z3,z4,z5,z992]),(0,[z1,z111,z3,z4,z5,z24]),(0,[z1,z2,z48,z4,z5,z6]),(0,[z1,z2,z993,z4,z5,z6])],[(0,[z136,z36,z60,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z1,z2,z3,z4,z426,z13]),(0,[z1,z2,z308,z293,z5,z6]),(0,[z119,z995,z2,z4,z5,z6])],[(0,[z136,z1,z2,z3,z4,z748]),(1,[z1,z2,z3,z4,z810]),(0,[z1,z2,z3,z129,z214,z6]),(0,[z1,z151,z3,z47,z5,z6])],[(0,[z1,z2,z3,z4,z5,z996]),(0,[z1,z2,z3,z225,z997,z6]),(0,[z1,z2,z93,z3,z4,z13])],[(0,[z1,z427,z3,z4,z80,z6]),(0,[z361,z1,z2,z3,z4,z13])],[(0,[z136,z1,z2,z3,z4,z754]),(0,[z1,z55,z3,z4,z562,z6]),(0,[z1,z2,z3,z4,z253,z13])],[(0,[z948,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z3,z4,z12,z999]),(0,[z1,z2,z3,z105,z214,z6]),(0,[z1,z2,z3,z4,z5,z174]),(0,[z1,z100,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z57,z1000])],[(0,[z1,z2,z3,z8,z4,z118])]],
   [[(0,[z1,z2,z3,z1001,z5,z6])],[(0,[z1,z2,z3,z1002,z4,z6]),(0,[z110,z123,z3,z4,z30,z6]),(0,[z1,z111,z3,z213,z5,z6]),(0,[z1,z2,z1003,z3,z4,z6])],[(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z427,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1007,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1008])],[(0,[z1,z605,z2,z3,z4,z13]),(0,[z637,z1,z2,z3,z4,z13]),(0,[z360,z2,z3,z4,z5,z24])],[(0,[z1,z123,z474,z4,z5,z6]),(0,[z1009,z2,z3,z4,z5,z6]),(0,[z1,z181,z2,z295,z5,z6]),(0,[z125,z1,z2,z4,z190,z153]),(0,[z1,z454,z2,z3,z4,z13])],[(0,[z560,z1,z2,z3,z108,z5]),(0,[z1,z2,z3,z4,z1010,z6]),(0,[z1,z2,z3,z1011,z5,z24])],[(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z3,z4,z24,z78])],[(0,[z201,z2,z3,z4,z5,z6]),(0,[z110,z2,z3,z4,z30,z248]),(0,[z1,z2,z1015,z3,z4,z5]),(1,[z137,z2,z3,z4,z13]),(0,[z28,z1,z2,z5,z114,z24])],[(0,[z1,z2,z3,z4,z1016,z6]),(0,[z1,z246,z3,z4,z5,z113]),(0,[z1,z2,z3,z1017,z5,z6]),(0,[z125,z1,z2,z4,z5,z707])],[(0,[z1,z2,z3,z4,z170,z189]),(0,[z1,z2,z3,z4,z567,z13]),(0,[z28,z1,z156,z26,z5,z6]),(0,[z1,z2,z3,z979,z5,z6])],[(0,[z54,z1,z3,z238,z76,z6])],[],[(0,[z1,z680,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z1018])],[(0,[z830,z60,z3,z4,z5,z6]),(0,[z1,z2,z295,z5,z80,z6])],[(0,[z72,z2,z62,z4,z5,z68]),(0,[z422,z1,z3,z4,z5,z456])],[(0,[z1,z2,z3,z4,z1019,z6]),(0,[z1,z270,z2,z4,z5,z6]),(0,[z1,z2,z82,z4,z5,z707])]],
   [[(0,[z1,z2,z3,z852,z5,z6]),(0,[z1,z111,z266,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z752]),(0,[z1,z2,z3,z4,z476,z13]),(0,[z1,z2,z3,z4,z253,z942]),(0,[z1,z270,z2,z4,z5,z90]),(0,[z1,z2,z3,z5,z6,z784])],[(0,[z136,z1,z55,z3,z4,z6]),(0,[z1,z1020,z3,z4,z5,z6]),(0,[z28,z1,z2,z4,z214,z6])],[(0,[z1,z2,z3,z4,z309,z13]),(0,[z1,z2,z3,z4,z1021,z6])],[(0,[z1,z1022,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z293,z5]),(0,[z263,z2,z3,z4,z5,z13])],[(0,[z1023,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1024,z6]),(0,[z1,z2,z3,z4,z5,z660]),(0,[z1,z2,z308,z4,z370,z6])],[(0,[z1,z2,z3,z4,z214,z185]),(0,[z1,z2,z3,z4,z253,z6]),(0,[z1,z1025,z3,z4,z5,z6]),(0,[z1,z2,z3,z749,z4,z6])],[(0,[z1,z2,z1026,z3,z4,z6]),(0,[z650,z2,z62,z4,z5,z6]),(0,[z1,z1027,z3,z4,z5,z6]),(0,[z1,z55,z3,z4,z69,z174])],[(0,[z103,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z7,z6])],[(0,[z559,z2,z3,z34,z5,z6]),(0,[z72,z2,z62,z4,z5,z193]),(0,[z1,z2,z474,z225,z4,z6]),(0,[z1,z2,z498,z3,z4,z13]),(0,[z1,z2,z683,z4,z80,z6])],[(0,[z2,z3,z4,z722,z5,z6]),(0,[z1028,z2,z3,z4,z5,z6])],[(0,[z1,z2,z308,z4,z5,z24]),(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z2,z3,z4,z80,z115]),(0,[z1,z2,z89,z4,z5,z24])],[(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z2,z1031,z3,z5,z6]),(0,[z1,z2,z3,z238,z5,z24])],[(0,[z1,z2,z3,z4,z1032,z6]),(0,[z1,z2,z3,z4,z5,z1033])],[(0,[z1,z1034,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1035]),(0,[z91,z1,z2,z3,z4,z370]),(0,[z360,z2,z272,z4,z5,z6]),(0,[z360,z2,z3,z4,z5,z221])],[(0,[z1,z2,z1036,z3,z4,z6])],[(0,[z1,z2,z1037,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1038]),(0,[z1,z2,z3,z4,z5,z1039]),(0,[z1,z2,z1040,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z999,z13]),(0,[z1,z2,z3,z4,z5,z1041])],[(0,[z1042,z1,z2,z3,z4,z5]),(0,[z469,z2,z3,z34,z5,z6]),(0,[z1,z2,z1043,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z1044]),(0,[z2,z800,z95,z4,z5,z6]),(0,[z1,z2,z3,z225,z4,z1045]),(0,[z137,z2,z48,z4,z5,z6]),(0,[z28,z1,z2,z4,z80,z13])],[(0,[z1,z427,z3,z4,z5,z248]),(0,[z1,z2,z308,z213,z5,z6]),(0,[z1,z156,z3,z709,z5,z6])],[(0,[z1,z2,z241,z237,z3,z4]),(0,[z54,z1,z2,z272,z4,z13]),(0,[z1,z2,z3,z4,z5,z1046]),(0,[z1,z2,z295,z3,z8,z13]),(0,[z1,z2,z3,z749,z73,z6])],[(0,[z1047,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z766]),(0,[z1,z2,z3,z4,z5,z1048]),(0,[z1,z2,z3,z4,z9,z24])],[(0,[z136,z1,z2,z3,z4,z24]),(0,[z1,z2,z474,z4,z80,z6]),(0,[z1,z40,z100,z3,z5,z6]),(0,[z1,z2,z3,z4,z844,z13])],[(0,[z1,z2,z3,z1049,z5,z6]),(0,[z1,z2,z1050,z4,z5,z6])],[(0,[z54,z137,z2,z3,z4,z13]),(0,[z1,z3,z4,z5,z744,z6])],[(0,[z1,z2,z3,z4,z1051,z6]),(0,[z54,z1,z2,z3,z4,z844])],[(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z2,z3,z64,z5,z13]),(0,[z1,z2,z3,z4,z5,z1053]),(0,[z1,z2,z3,z4,z5,z310]),(0,[z1,z2,z3,z4,z532,z13])],[(0,[z611,z2,z62,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z2,z3,z1055,z5,z6]),(0,[z1,z2,z474,z4,z5,z24])],[(0,[z54,z1,z2,z3,z4,z248])],[(0,[z1,z77,z242,z3,z4,z5]),(0,[z1,z2,z3,z1056,z5,z6]),(0,[z1,z2,z3,z4,z1057,z6])],[(0,[z1,z2,z679,z4,z80,z6]),(0,[z1,z2,z3,z1058,z5,z6]),(0,[z849,z2,z3,z4,z5,z6]),(0,[z1,z181,z2,z8,z4,z24])]],
   [[(0,[z1,z2,z3,z4,z30,z248]),(0,[z119,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1,z2,z45,z4,z5,z24])],[(0,[z1,z2,z3,z4,z1060,z6]),(0,[z1,z2,z3,z4,z170,z13]),(0,[z28,z1,z2,z105,z5,z6]),(0,[z1,z2,z3,z129,z5,z185])],[(0,[z1061,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z309,z549])],[(0,[z36,z237,z60,z3,z4,z6]),(0,[z1,z111,z3,z4,z370,z6]),(0,[z263,z2,z3,z4,z5,z549]),(0,[z1,z1062,z2,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z13]),(1,[z1,z2,z48,z4,z13]),(0,[z1,z2,z3,z4,z5,z920]),(0,[z1,z2,z3,z4,z5,z1063])],[(0,[z137,z2,z3,z4,z5,z6]),(0,[z493,z70,z3,z4,z5,z6]),(0,[z1,z2,z3,z105,z5,z185]),(0,[z1,z2,z3,z4,z5,z1064]),(0,[z1,z2,z326,z4,z5,z277])],[(0,[z1,z2,z3,z4,z5,z1065]),(0,[z1,z2,z3,z4,z809,z6]),(0,[z1,z2,z437,z4,z80,z6]),(0,[z1,z2,z1040,z4,z5,z6])],[(0,[z1,z2,z4,z46,z5,z6]),(0,[z1,z55,z3,z4,z6,z276])],[(0,[z14,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z150,z3,z4,z57,z6]),(0,[z1,z2,z82,z4,z5,z83])],[(0,[z1,z1067,z3,z4,z5,z6]),(0,[z1,z507,z2,z3,z5,z24]),(0,[z1,z2,z3,z1068,z5,z6])],[(0,[z1,z2,z1069,z3,z4,z6])],[(0,[z1,z2,z1070,z237,z3,z4]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z1072,z3,z4,z5,z6]),(0,[z1,z2,z3,z418,z5,z13])],[(0,[z1,z2,z3,z4,z1073,z6]),(0,[z1,z1074,z3,z4,z5,z6]),(0,[z56,z150,z3,z4,z5,z6]),(0,[z1,z150,z3,z4,z5,z24])],[(0,[z1,z2,z1075,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z77,z2,z3,z4,z78])]],
   [[(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z936,z4,z5,z6]),(0,[z103,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z309,z897])],[(0,[z1078,z1,z2,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z13]),(0,[z54,z1,z2,z3,z238,z13])],[(0,[z1,z2,z3,z64,z5,z357]),(0,[z104,z1,z109,z4,z5,z13])],[(0,[z1,z2,z3,z4,z592,z13]),(0,[z1,z2,z308,z4,z5,z13]),(0,[z1,z77,z3,z4,z5,z276]),(0,[z28,z1,z2,z447,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1079]),(0,[z995,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z238,z5,z13])],[(0,[z28,z1,z2,z629,z5,z6]),(0,[z28,z1,z2,z253,z114,z6]),(0,[z1,z2,z18,z66,z5,z13])],[],[(0,[z1,z2,z1080,z4,z5,z6]),(0,[z1081,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1082]),(0,[z1,z2,z3,z239,z81,z13]),(0,[z1,z2,z518,z3,z4,z13])],[(0,[z1,z2,z1083,z3,z225,z6]),(0,[z1,z2,z48,z4,z6,z13])],[],[(0,[z1,z2,z237,z3,z4,z24]),(0,[z70,z830,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z170,z6])],[(0,[z1,z2,z3,z1084,z5,z6]),(0,[z1085,z2,z3,z4,z5,z6]),(0,[z1086,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z81,z400])],[(0,[z33,z2,z3,z182,z34,z5]),(0,[z1,z123,z45,z4,z5,z6])],[(0,[z1,z2,z474,z4,z5,z248]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z480,z5,z24]),(0,[z1,z2,z601,z4,z5,z83])],[(0,[z1,z2,z3,z4,z5,z1088]),(0,[z72,z2,z62,z4,z5,z24]),(0,[z1,z879,z3,z4,z5,z6]),(0,[z1,z1089,z2,z3,z5,z6]),(0,[z1,z26,z4,z453,z5,z6]),(0,[z1090,z2,z3,z4,z5,z6]),(0,[z1091,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z214,z24])]],
   [[(0,[z1,z123,z3,z636,z5,z6])],[(0,[z1,z2,z474,z8,z4,z6]),(0,[z1,z2,z84,z3,z749,z6]),(0,[z1,z2,z3,z4,z511,z13])],[(0,[z1,z2,z45,z4,z5,z248]),(0,[z1,z2,z1092,z4,z5,z6]),(0,[z110,z2,z3,z4,z30,z13])],[(0,[z226,z2,z3,z4,z756,z6]),(0,[z201,z2,z3,z4,z253,z6]),(0,[z1,z2,z3,z4,z80,z50])],[(0,[z1,z2,z3,z4,z5,z1093]),(0,[z269,z1,z3,z4,z76,z6]),(0,[z1,z2,z3,z418,z5,z6]),(0,[z1,z2,z3,z73,z81,z13]),(0,[z1,z578,z2,z3,z4,z13])],[(0,[z1,z2,z241,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z1,z2,z474,z4,z5,z13]),(0,[z1,z2,z3,z4,z1095,z6]),(0,[z1,z2,z4,z1096,z5,z6])],[(0,[z560,z1,z2,z3,z5,z283])],[(0,[z1,z2,z3,z1097,z5,z6]),(0,[z1,z2,z79,z4,z80,z50])],[(0,[z1,z1098,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1099]),(0,[z1,z2,z3,z676,z4,z13]),(0,[z1,z2,z3,z1100,z5,z6])],[],[(0,[z1101,z1,z2,z3,z4,z6])],[(0,[z136,z1,z2,z241,z3,z4]),(0,[z119,z1,z109,z4,z5,z6]),(0,[z1,z2,z3,z480,z5,z157]),(0,[z1,z270,z2,z4,z253,z6])],[(0,[z36,z60,z3,z4,z5,z24]),(0,[z1,z2,z225,z4,z80,z6]),(0,[z1,z2,z3,z1102,z4,z5]),(0,[z1103,z2,z3,z4,z5,z6]),(0,[z1,z2,z1104,z4,z5,z6]),(0,[z509,z1,z2,z3,z4,z13])],[(0,[z1,z2,z3,z4,z5,z1105]),(0,[z201,z2,z17,z3,z5,z6])],[(0,[z2,z62,z800,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z4,z5,z118]),(0,[z1,z2,z1107,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1108])]],
   [[(0,[z1,z2,z3,z1109,z5,z6]),(0,[z284,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z1110]),(0,[z422,z1,z2,z3,z4,z78])],[(0,[z1,z2,z3,z4,z5,z1111]),(0,[z1,z2,z3,z4,z214,z832])],[(0,[z103,z2,z3,z4,z5,z549]),(0,[z1,z1112,z3,z4,z5,z24])],[(0,[z94,z2,z95,z4,z5,z24]),(0,[z1,z242,z3,z4,z5,z83]),(0,[z1,z242,z266,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z272,z4,z5,z157]),(0,[z1114,z2,z3,z4,z5,z6])],[(0,[z1,z111,z3,z4,z5,z13]),(0,[z104,z1,z109,z4,z5,z549]),(0,[z104,z1,z804,z4,z5,z6]),(0,[z1,z2,z3,z5,z906,z6]),(0,[z1,z2,z84,z3,z4,z13])],[(0,[z1,z156,z3,z604,z5,z6]),(0,[z1,z217,z2,z3,z4,z13])],[(0,[z138,z830,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1115,z6]),(0,[z1,z150,z3,z4,z5,z13])],[(0,[z1,z2,z272,z480,z5,z6]),(0,[z1,z2,z3,z480,z5,z221])],[(0,[z1,z1116,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z9,z189]),(0,[z201,z2,z3,z4,z5,z310]),(0,[z1,z2,z3,z4,z5,z1117]),(0,[z1,z2,z3,z108,z5,z349])],[(0,[z85,z1,z55,z3,z4,z13]),(0,[z28,z1,z2,z322,z5,z6])],[(0,[z110,z2,z3,z4,z30,z6]),(0,[z1,z427,z3,z8,z4,z6]),(0,[z110,z2,z3,z4,z30,z357]),(0,[z1,z507,z26,z2,z5,z6])],[(0,[z1,z1118,z3,z4,z5,z6]),(0,[z1,z1119,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1120]),(0,[z1,z2,z3,z4,z78,z13]),(0,[z1,z2,z17,z3,z253,z6])],[(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z3,z129,z5,z24]),(0,[z1,z2,z48,z4,z69,z6]),(0,[z125,z1,z2,z4,z468,z153]),(0,[z1,z2,z3,z73,z81,z6])],[(0,[z1,z2,z1070,z3,z4,z5]),(0,[z1,z2,z3,z225,z4,z68]),(0,[z1,z2,z474,z4,z5,z357]),(0,[z1,z242,z3,z293,z5,z6]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z1,z2,z3,z4,z309,z6]),(0,[z1,z2,z3,z4,z214,z845]),(0,[z1,z2,z3,z1123,z5,z6]),(0,[z1124,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z5,z784])],[(0,[z263,z2,z3,z4,z5,z6]),(0,[z1,z1125,z3,z4,z5,z6]),(0,[z1,z427,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z418,z13]),(0,[z302,z2,z3,z4,z5,z301]),(0,[z1,z319,z2,z3,z4,z13])],[(0,[z1,z2,z3,z4,z1126,z6]),(0,[z360,z2,z3,z4,z5,z13]),(0,[z1,z2,z272,z4,z5,z221]),(0,[z1,z2,z3,z4,z300,z157]),(0,[z1,z2,z3,z1127,z5,z6])]],
   [[(0,[z138,z70,z3,z4,z5,z24]),(0,[z1,z2,z3,z105,z5,z24]),(0,[z1,z2,z3,z4,z1128,z6])],[(0,[z1,z2,z3,z5,z6,z1129])],[],[(0,[z110,z137,z2,z3,z4,z6]),(0,[z1130,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1131,z5,z6]),(0,[z28,z1,z2,z5,z114,z13])],[(0,[z1,z2,z3,z4,z1132,z6]),(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z308,z4,z5,z153]),(1,[z1,z2,z4,z5,z707])],[(0,[z1,z2,z266,z293,z5,z6]),(0,[z1,z2,z3,z293,z5,z83]),(0,[z1134,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z824])],[(0,[z1,z55,z3,z4,z69,z118]),(0,[z1,z2,z3,z4,z253,z310])],[(0,[z1,z2,z1135,z4,z5,z6]),(0,[z1,z2,z3,z225,z4,z193]),(0,[z1,z2,z3,z4,z5,z1045]),(0,[z28,z56,z2,z5,z114,z6]),(0,[z1,z2,z3,z4,z1136,z6])],[(0,[z1,z2,z3,z4,z5,z1137]),(0,[z1,z2,z3,z4,z5,z1138]),(0,[z1,z2,z3,z636,z5,z24]),(0,[z1,z2,z3,z4,z189,z13]),(0,[z1,z270,z2,z17,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1139])],[(0,[z1140,z1,z2,z3,z4,z5]),(0,[z1,z181,z2,z225,z4,z6]),(0,[z1,z2,z3,z1141,z5,z6]),(0,[z1,z2,z3,z4,z5,z1142]),(0,[z56,z2,z3,z4,z57,z6])],[(0,[z1,z2,z3,z4,z30,z13]),(0,[z54,z1,z3,z4,z76,z157]),(0,[z1,z2,z3,z4,z83,z78])],[(0,[z2,z3,z722,z34,z5,z6]),(0,[z1,z1143,z3,z4,z5,z6]),(0,[z1,z2,z79,z4,z80,z24])],[(0,[z1,z2,z3,z4,z1144,z6]),(0,[z72,z2,z62,z225,z4,z6]),(0,[z1,z2,z3,z4,z5,z29])],[(0,[z1,z2,z3,z709,z5,z6]),(0,[z56,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z202]),(0,[z91,z1,z2,z3,z5,z283])],[(0,[z1,z2,z3,z4,z1145,z6]),(0,[z226,z55,z60,z3,z4,z6]),(0,[z54,z1,z3,z480,z76,z6]),(0,[z91,z1,z2,z3,z5,z511])]],
   [[(0,[z1,z2,z3,z4,z1146,z6]),(0,[z1,z2,z653,z3,z4,z13])],[(0,[z60,z3,z4,z5,z490,z6])],[(0,[z1,z2,z3,z4,z12,z248]),(0,[z1,z3,z709,z4,z5,z6])],[(0,[z1,z55,z3,z4,z276,z13]),(0,[z56,z100,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z81,z373])],[(0,[z36,z60,z3,z4,z5,z13]),(0,[z1,z2,z3,z64,z5,z6]),(0,[z1,z2,z3,z4,z5,z1147])],[(0,[z1,z427,z3,z4,z5,z6]),(0,[z1,z427,z3,z4,z5,z357]),(0,[z137,z2,z3,z4,z6,z13]),(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1,z2,z89,z4,z5,z13])],[(0,[z1,z2,z3,z1148,z5,z6]),(0,[z1,z2,z3,z4,z5,z1149]),(0,[z1,z2,z1150,z4,z5,z6]),(0,[z54,z1,z3,z4,z76,z221])],[(0,[z37,z1,z3,z4,z5,z71]),(0,[z1151,z1,z2,z3,z4,z5]),(0,[z1,z242,z3,z4,z370,z6]),(0,[z1,z2,z3,z8,z4,z115])],[(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z2,z3,z4,z336,z13]),(0,[z1,z2,z1153,z4,z5,z6]),(0,[z91,z1,z2,z3,z7,z283])],[(0,[z1,z2,z3,z4,z1154,z6]),(0,[z1,z2,z3,z1155,z4,z6]),(0,[z1,z2,z3,z4,z12,z13])],[(0,[z1,z77,z3,z4,z5,z328]),(0,[z385,z2,z3,z97,z5,z6]),(0,[z1,z2,z48,z238,z5,z6]),(0,[z1,z2,z3,z4,z1156,z6])],[(0,[z94,z2,z95,z4,z5,z13]),(0,[z1,z2,z48,z4,z76,z6]),(0,[z1,z2,z222,z4,z80,z6]),(0,[z1,z2,z3,z4,z425,z24])],[(0,[z1157,z2,z3,z4,z5,z13])],[(0,[z1,z242,z3,z4,z5,z24]),(0,[z523,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z4,z5,z1158]),(1,[z2,z3,z722,z5,z6]),(0,[z470,z1,z2,z3,z4,z13])]],
   [[(0,[z1,z2,z3,z1159,z5,z6]),(0,[z2,z3,z4,z756,z30,z6]),(0,[z484,z2,z3,z4,z12,z6]),(0,[z1,z2,z266,z4,z370,z6]),(0,[z1,z2,z3,z4,z370,z83]),(0,[z1,z2,z3,z4,z555,z13]),(0,[z1,z40,z3,z47,z5,z24]),(0,[z1,z2,z3,z4,z5,z1160]),(0,[z1,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z32,z4,z13])],[(0,[z1,z2,z3,z4,z1161,z5]),(0,[z1162,z2,z3,z4,z5,z6]),(0,[z1,z59,z3,z4,z69,z6])],[(0,[z136,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z1163,z5,z6]),(0,[z2,z3,z800,z4,z5,z6]),(0,[z1164,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z190,z24]),(0,[z1,z2,z1165,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z159]),(0,[z1,z2,z3,z4,z824,z13])],[(0,[z1,z2,z3,z4,z5,z1166]),(0,[z1,z2,z3,z4,z1167,z6]),(0,[z1,z2,z211,z4,z80,z13]),(0,[z1,z2,z3,z4,z5,z373])],[(0,[z1,z665,z3,z65,z5,z6]),(0,[z1,z2,z3,z4,z5,z883])],[(0,[z1,z2,z3,z129,z5,z13]),(0,[z1,z507,z3,z47,z5,z6]),(0,[z1,z41,z27,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1168]),(0,[z1,z2,z266,z4,z5,z24]),(0,[z1,z2,z280,z4,z80,z6])],[(0,[z1,z242,z3,z213,z5,z6])],[(0,[z1,z2,z272,z4,z5,z24])],[(0,[z1,z2,z3,z1169,z5,z6]),(0,[z1,z123,z3,z4,z5,z24]),(0,[z1,z2,z3,z636,z5,z248]),(0,[z1,z2,z3,z105,z5,z13]),(0,[z119,z1,z2,z17,z5,z6]),(0,[z1,z2,z4,z5,z6,z1170]),(0,[z54,z1,z2,z48,z4,z13])],[(0,[z36,z241,z60,z3,z4,z5]),(0,[z1,z2,z3,z293,z370,z6]),(0,[z1,z2,z3,z4,z214,z549])],[(0,[z103,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z30,z301,z13]),(0,[z1,z100,z4,z5,z80,z6]),(0,[z1,z181,z2,z8,z4,z13])],[],[(0,[z136,z137,z2,z3,z4,z6]),(0,[z1,z2,z45,z4,z5,z13]),(0,[z1,z1171,z3,z4,z5,z6]),(0,[z104,z1,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z400])],[(0,[z1,z2,z308,z4,z5,z6]),(0,[z1,z2,z3,z4,z165,z13]),(0,[z560,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z5,z647,z6]),(0,[z1,z2,z17,z3,z749,z6])],[(0,[z130,z60,z3,z4,z5,z6]),(0,[z1,z2,z266,z213,z5,z6]),(0,[z14,z2,z3,z4,z5,z752]),(0,[z1,z2,z3,z238,z5,z6]),(1,[z1,z2,z89,z4,z13])]],
   [[(0,[z1,z2,z3,z293,z5,z24]),(0,[z1,z2,z18,z66,z5,z6]),(0,[z1,z2,z295,z3,z5,z24])],[(0,[z1,z2,z3,z636,z5,z13]),(0,[z110,z1,z2,z48,z4,z6]),(0,[z1,z2,z3,z4,z1172,z6])],[(0,[z1,z2,z3,z4,z5,z1173]),(0,[z1,z2,z3,z239,z81,z6])],[(0,[z1,z2,z3,z4,z1174,z6]),(0,[z1,z2,z3,z4,z5,z1175])],[(0,[z1,z2,z3,z4,z544,z13]),(0,[z1,z2,z3,z4,z300,z24]),(0,[z1,z2,z3,z418,z6,z13])],[(0,[z1,z2,z1176,z4,z5,z6]),(0,[z1177,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z522,z13]),(0,[z1,z507,z2,z3,z5,z13]),(0,[z1,z2,z3,z4,z5,z1178])],[(0,[z2,z3,z4,z5,z756,z6]),(0,[z1,z2,z3,z146,z5,z152])],[(0,[z1,z3,z4,z5,z1179,z6]),(0,[z1,z2,z3,z146,z5,z403])],[(0,[z1,z77,z294,z3,z4,z5]),(0,[z119,z1,z40,z47,z5,z6])],[(0,[z136,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1180,z5,z6]),(0,[z1,z2,z1083,z3,z5,z6])],[(0,[z1181,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z225,z4,z24]),(0,[z1,z2,z3,z4,z216,z13])],[(0,[z1,z2,z18,z5,z906,z6]),(0,[z1,z2,z3,z4,z883,z13]),(0,[z132,z2,z3,z4,z5,z420])],[(0,[z96,z2,z3,z97,z5,z24]),(0,[z1,z2,z3,z4,z5,z1182]),(0,[z1,z2,z3,z239,z5,z229])]],
   [[(0,[z1,z2,z474,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z2,z17,z498,z3,z6]),(0,[z54,z1,z3,z4,z76,z24])],[(0,[z1,z2,z3,z4,z5,z1184]),(0,[z1,z2,z3,z48,z4,z13])],[(0,[z1,z270,z2,z84,z4,z13])],[(0,[z1,z181,z2,z8,z4,z6]),(0,[z1,z2,z3,z4,z695,z24])],[(0,[z1185,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1186,z5,z6]),(0,[z1,z2,z3,z4,z253,z1117])],[(0,[z1,z2,z45,z4,z5,z357]),(0,[z1,z2,z3,z4,z5,z1187])],[(0,[z1,z2,z237,z3,z4,z13]),(0,[z107,z2,z3,z4,z5,z752]),(0,[z1,z2,z1188,z4,z5,z6]),(0,[z360,z2,z48,z4,z5,z6]),(0,[z1,z2,z3,z4,z1189,z6])],[(0,[z1,z2,z3,z4,z1190,z6]),(0,[z96,z2,z3,z188,z5,z6]),(0,[z1,z55,z2,z3,z4,z248]),(0,[z1,z242,z3,z4,z5,z13]),(0,[z1,z2,z3,z129,z5,z549]),(0,[z125,z1,z2,z4,z5,z153]),(0,[z1,z2,z3,z4,z145,z24])],[(0,[z33,z560,z2,z3,z34,z5]),(0,[z1,z55,z3,z4,z744,z6]),(0,[z1,z1191,z3,z4,z5,z6])],[(0,[z1,z2,z3,z636,z5,z357]),(0,[z1,z2,z3,z4,z309,z1099]),(0,[z269,z1,z109,z4,z5,z6]),(0,[z1,z40,z3,z47,z5,z13]),(0,[z1,z2,z3,z480,z5,z13]),(0,[z1,z198,z2,z4,z5,z262])],[(0,[z72,z2,z62,z4,z5,z13]),(0,[z1,z123,z3,z4,z5,z248]),(0,[z14,z2,z3,z4,z170,z15]),(0,[z1,z2,z3,z4,z642,z13])],[(0,[z1,z1192,z3,z4,z5,z6]),(0,[z107,z2,z3,z4,z5,z184]),(0,[z1,z2,z3,z4,z370,z24]),(0,[z1,z2,z3,z105,z5,z549]),(0,[z1,z2,z3,z4,z214,z13]),(0,[z201,z2,z3,z4,z5,z29])],[(0,[z1,z2,z3,z4,z5,z1193]),(0,[z1,z2,z3,z4,z5,z1194])],[(0,[z1195,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z6,z1196]),(0,[z119,z1,z2,z66,z5,z6]),(0,[z1,z2,z4,z5,z6,z1197]),(0,[z1,z2,z3,z4,z57,z24])],[(0,[z1,z507,z2,z3,z5,z6])],[(0,[z1,z111,z3,z4,z5,z6]),(0,[z1,z55,z2,z3,z4,z13])]],
   [[(0,[z1,z2,z3,z4,z1198,z6]),(0,[z1,z2,z3,z4,z5,z1199]),(0,[z1,z2,z1200,z3,z5,z6]),(0,[z1201,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1202,z4,z5,z6]),(0,[z1,z2,z3,z4,z278,z13]),(0,[z1,z150,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z50]),(0,[z2,z3,z4,z5,z13,z853])],[(0,[z1,z2,z3,z4,z5,z68]),(0,[z226,z2,z3,z4,z12,z24]),(0,[z1203,z1,z2,z3,z4,z5]),(0,[z1,z100,z3,z4,z57,z6])],[(0,[z1,z2,z3,z4,z452,z13]),(0,[z107,z2,z3,z4,z5,z301])],[(0,[z1,z2,z1204,z4,z5,z6]),(0,[z1,z2,z3,z213,z370,z6]),(0,[z1205,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1206,z6]),(0,[z1,z2,z3,z4,z6,z1207]),(0,[z1,z2,z3,z4,z5,z1208]),(0,[z1,z156,z3,z65,z5,z24])],[(0,[z1,z2,z3,z1209,z4,z5]),(0,[z1,z2,z3,z1210,z5,z6]),(0,[z1,z2,z3,z4,z5,z1211]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z1,z2,z3,z4,z273,z24]),(0,[z1,z100,z3,z4,z5,z24]),(0,[z28,z1,z2,z80,z81,z6]),(0,[z1,z181,z2,z8,z418,z6])],[(0,[z1,z2,z821,z4,z5,z24])],[(0,[z1,z1213,z3,z4,z5,z6]),(0,[z1214,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z293,z5,z13]),(0,[z1,z40,z46,z47,z5,z6]),(0,[z137,z2,z3,z238,z5,z6]),(0,[z86,z1,z3,z4,z5,z71]),(0,[z1,z2,z3,z4,z253,z29]),(0,[z1,z2,z295,z3,z5,z13])],[(0,[z360,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z213,z5,z24]),(0,[z54,z1,z272,z4,z76,z6]),(0,[z1,z2,z82,z4,z5,z262])],[(0,[z54,z360,z3,z4,z76,z6])],[(0,[z1,z2,z3,z4,z5,z193]),(0,[z1,z2,z3,z1011,z5,z6]),(0,[z1,z2,z804,z4,z5,z6]),(0,[z1,z2,z771,z4,z5,z13])],[(0,[z119,z1,z2,z4,z1115,z6]),(0,[z1215,z1,z2,z4,z5,z6])],[(0,[z1,z100,z3,z5,z114,z6]),(0,[z28,z1,z2,z5,z114,z6])],[(0,[z514,z2,z3,z97,z5,z6]),(0,[z263,z2,z3,z4,z309,z6]),(0,[z116,z1,z2,z3,z4,z824])]],
   [[(0,[z1,z2,z3,z4,z1216,z6])],[(0,[z104,z1,z507,z2,z5,z6])],[(0,[z1,z2,z4,z5,z68,z153]),(0,[z28,z1,z2,z3,z81,z13])],[(0,[z1,z2,z3,z4,z214,z6]),(0,[z1,z2,z3,z4,z639,z13])],[(0,[z1,z2,z4,z253,z80,z6]),(0,[z1,z2,z3,z4,z5,z1217])],[(0,[z14,z590,z2,z3,z4,z5])],[(0,[z119,z1,z100,z4,z5,z6]),(0,[z1,z3,z65,z709,z5,z6]),(0,[z54,z1,z3,z4,z191,z6])],[(0,[z136,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z1218,z4,z6]),(0,[z1,z2,z1219,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1220]),(0,[z1,z1221,z3,z4,z5,z6]),(0,[z1,z2,z3,z1222,z5,z6])],[(0,[z1,z2,z3,z4,z177,z13]),(0,[z1,z2,z3,z4,z5,z1223]),(0,[z1,z2,z48,z4,z9,z6]),(0,[z1,z2,z3,z4,z398,z24])],[(0,[z1,z2,z3,z4,z153,z78]),(0,[z1,z2,z3,z253,z81,z6]),(0,[z1,z2,z3,z4,z5,z1224]),(0,[z1,z2,z3,z4,z5,z1225]),(0,[z1,z181,z2,z745,z4,z6]),(0,[z523,z2,z3,z4,z5,z183])],[(0,[z86,z1,z3,z4,z5,z766]),(0,[z1,z2,z4,z5,z906,z6])],[(0,[z1,z2,z3,z4,z5,z1226])],[(0,[z138,z70,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z80,z248]),(0,[z1,z2,z3,z4,z5,z1227])],[(0,[z1,z2,z3,z1228,z5,z6]),(0,[z1,z2,z27,z4,z214,z6]),(0,[z1,z2,z3,z4,z1229,z6]),(0,[z1,z2,z3,z4,z5,z50])],[(0,[z1,z2,z1230,z4,z5,z6]),(0,[z1,z2,z3,z4,z1231,z6]),(0,[z1,z2,z3,z4,z5,z1232]),(0,[z1,z26,z804,z4,z5,z6]),(0,[z1,z1233,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1234]),(0,[z1,z2,z3,z4,z1235,z6]),(0,[z1,z2,z3,z4,z63,z1193]),(0,[z1236,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1237]),(0,[z1,z2,z3,z4,z404,z13])]],
   [[(0,[z36,z60,z3,z4,z5,z6]),(0,[z96,z2,z3,z722,z5,z6]),(0,[z1,z2,z3,z4,z1238,z6]),(0,[z1,z462,z3,z4,z5,z276])],[(0,[z37,z1,z77,z3,z4,z5]),(0,[z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z66,z5,z906,z6]),(0,[z1,z2,z3,z4,z1239,z6])],[(0,[z1,z2,z3,z4,z5,z999]),(0,[z1,z2,z607,z3,z4,z13]),(0,[z1,z2,z3,z1240,z5,z6]),(0,[z54,z1,z2,z3,z4,z118]),(0,[z1,z2,z89,z4,z5,z90])],[(0,[z1,z3,z109,z105,z5,z6]),(0,[z1,z2,z3,z4,z6,z78]),(0,[z1,z100,z3,z5,z81,z6])],[(0,[z1,z1241,z3,z4,z5,z6]),(0,[z1242,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z4,z13]),(0,[z1,z2,z3,z4,z80,z13])],[(0,[z1,z2,z3,z4,z63,z68]),(0,[z1,z2,z3,z4,z5,z1243])],[(0,[z1,z1112,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z57,z13])],[(0,[z94,z2,z95,z4,z5,z6]),(0,[z1,z1244,z3,z4,z5,z6]),(0,[z1,z2,z3,z314,z4,z13]),(0,[z1,z2,z3,z4,z5,z115])],[(0,[z1,z242,z3,z4,z5,z153]),(0,[z1,z2,z79,z4,z80,z13]),(0,[z1,z2,z8,z4,z80,z13]),(0,[z1,z2,z295,z84,z3,z6]),(0,[z1,z2,z3,z81,z349,z13]),(0,[z1157,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z152])],[(0,[z1,z2,z3,z4,z5,z1245]),(0,[z1,z2,z3,z4,z5,z1246]),(0,[z1,z2,z3,z4,z7,z403])],[(0,[z1,z319,z3,z4,z5,z113]),(0,[z56,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1247]),(0,[z1,z270,z2,z4,z5,z115]),(0,[z1,z2,z3,z4,z5,z824])],[(0,[z1,z2,z3,z997,z5,z6]),(0,[z1,z2,z3,z1248,z4,z6]),(0,[z1,z3,z4,z5,z6,z766])],[(0,[z1,z1249,z3,z4,z5,z6]),(0,[z1,z2,z1250,z4,z5,z6]),(0,[z14,z111,z3,z4,z5,z15])],[(0,[z37,z1,z2,z237,z3,z4]),(0,[z1,z2,z3,z4,z9,z90]),(0,[z1,z2,z3,z4,z455,z13])],[(0,[z1,z1251,z3,z4,z5,z6]),(0,[z1252,z1,z2,z3,z4,z5]),(0,[z1,z2,z27,z4,z80,z13]),(0,[z1,z2,z211,z4,z80,z6]),(0,[z1,z2,z3,z4,z403,z13])],[(0,[z1,z1253,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z63,z193]),(0,[z1,z1254,z3,z4,z5,z6]),(0,[z1,z26,z66,z47,z5,z6]),(0,[z1,z40,z3,z709,z5,z6]),(0,[z1,z100,z3,z4,z5,z13]),(0,[z1,z2,z84,z89,z4,z13])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 510).take 507) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1017).take 275) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1292)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [510, 507, 275] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 154).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 154).take 147).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 301).take 153).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 454).take 58).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [154, 147, 153, 58] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36348

theorem PEqualNP.Outside.L_meta_36348 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36348.solve