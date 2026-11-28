import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38779

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4270369280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x80004810a9016d56#64 ++ 0xa00012042a405b55#64 ++ 0x6408f8f1f903ffff#64 ++ 0xd9023e3c7e40ffff#64 : BitVec 256),
   (0x04332356660cb730#64 ++ 0xc10cc8d599832dcc#64 ++ 0xfc77275e661cff33#64 ++ 0xbf1dc9d799873fcc#64 : BitVec 256),
   (0x0985c59b8760e3c3#64 ++ 0x02617166e1d838f0#64 ++ 0xeb87c79f87e0e3c3#64 ++ 0x7ae1f1e7e1f838f0#64 : BitVec 256),
   (0x02d807e002b602a8#64 ++ 0x00b601f800ad80aa#64 ++ 0xfff807e007ff03fe#64 ++ 0xfffe01f801ffc0ff#64 : BitVec 256),
   (0x136ff80005dbd800#64 ++ 0x04dbfe000176f600#64 ++ 0xf7fff80007fffc01#64 ++ 0xfdfffe0001ffff00#64 : BitVec 256),
   (0x03feb6ed50000000#64 ++ 0x00ffadbb54000000#64 ++ 0xdbfffffff8000003#64 ++ 0xf6fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0080058002200280 0x00200160008800a0 0xeb80078007e003c2 0x7ae001e001f800f0

def z1 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff807e007ff03fe 0xfffe01f801ffc0ff

def z2 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbfffffff8000003 0xf6fffffffe000000

def z3 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77275e661cff33 0xbf1dc9d799873fcc

def z4 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff80007fffc01 0xfdfffe0001ffff00

def z5 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x6408f8f1f903ffff 0xd9023e3c7e40ffff

def z6 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x640800e0010303fe 0xd90200380040c0ff

def z8 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z9 : W := mkw 0x82d84ff0abb76ffe 0xa0b613fc2aeddbff 0xfff8fff1ffffffff 0xfffe3ffc7fffffff

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0x640020000000fc01 0x9900080000003f00

def z11 : W := mkw 0x88014912af61efd7 0xa2005244abd87bf5 0x2400000007e3fffc 0x0900000001f8ffff

def z12 : W := mkw 0x067a2264609e1438 0xc19e88991827850e 0x14782060601f1c3c 0x851e08181807c70f

def z13 : W := mkw 0x034dc00005d2c000 0x00d370000174b000 0xf7ffc00007ffe001 0xfdfff00001fff800

def z14 : W := mkw 0x0248000000920000 0x0092000000248000 0xf7f8000007ff0000 0xfdfe000001ffc000

def z15 : W := mkw 0x03feb6ed50920000 0x00ffadbb54248000 0xffffffffffff0003 0xffffffffffffc000

def z16 : W := mkw 0x02d807e002040220 0x00b601f800810088 0xfff807e0061c0332 0xfffe01f8018700cc

def z17 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x240838607903fffc 0x89020e181e40ffff

def z18 : W := mkw 0x036eb00000000000 0x00dbac0000000000 0xd3fff80000000001 0xf4fffe0000000000

def z19 : W := mkw 0x1001480005dbd800 0x040052000176f600 0x2400000007fffc00 0x0900000001ffff00

def z20 : W := mkw 0x02d807e0022402a8 0x00b601f8008900aa 0xdbf807e0000003fe 0xf6fe01f8000000ff

def z21 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xbff0070007ff03fc 0x2ffc01c001ffc0ff

def z22 : W := mkw 0x84336b56ef0dff76 0xe10cdad5bbc37fdd 0xfc77275e671fffff 0xbf1dc9d799c7ffff

def z23 : W := mkw 0x0000001000002100 0x0000000400000840 0x600000100000e303 0x18000004000038c0

def z24 : W := mkw 0x0985c59ba760e7d3 0x82617166e9d839f4 0xef87e7dfe7e0fff3 0xfbe1f9f7f9f83ffc

def z25 : W := mkw 0x0bfff7ffd7f6e3eb 0x02fffdfff5fdb8fa 0xffffffffffffe3ff 0xfffffffffffff8ff

def z26 : W := mkw 0x0105c0000540c000 0x0041700001503000 0xe387c00007e0e001 0x78e1f00001f83800

def z27 : W := mkw 0x027a326450000000 0x009e8c9914000000 0x1078386078000000 0x841e0e181e000000

def z28 : W := mkw 0x02fb27e006be92a8 0x00bec9f801afa4aa 0xffff27e007ffffff 0xffffc9f801ffffff

def z29 : W := mkw 0x0023200004089000 0x0008c80001022400 0xf4772000061cfc01 0xbd1dc80001873f00

def z30 : W := mkw 0x0000001020002510 0x8000000408000944 0x640020506000ff33 0x9900081418003fcc

def z31 : W := mkw 0x84336b56ef0dff76 0xe10cdad5bbc37fdd 0xfc7fffffff1fffff 0xff1fffffffc7ffff

def z32 : W := mkw 0x0000080000010800 0x0000020000004200 0x0408380000031c00 0x81020e000000c700

def z33 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0x93f7000006fc0000 0x24fdc00001bf0000

def z34 : W := mkw 0x0bddc7fb87f6e3eb 0x02f771fee1fdb8fa 0xffffc7ff87ffe3ff 0xfffff1ffe1fff8ff

def z35 : W := mkw 0x000101120600a300 0x00004044818028c0 0xe807071e0600e303 0x3a01c1c7818038c0

def z36 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0x8b87070e06e00000 0x22e1c1c381b80000

def z37 : W := mkw 0x13ffffed57ffdaa8 0x04fffffb55fff6aa 0xffffffffffffffff 0xffffffffffffffff

def z38 : W := mkw 0x13ffffe007ffdaa8 0x04fffff801fff6aa 0xffffffe007ffffff 0xfffffff801ffffff

def z39 : W := mkw 0x009007e0022402a8 0x002401f8008900aa 0x080007e0000003fe 0x020001f8000000ff

def z40 : W := mkw 0x067a3264700c1430 0xc19e8c991c03050c 0x14783860781c1c30 0x851e0e181e07070c

def z41 : W := mkw 0x82d80fe02ab70ebc 0xa0b603f80aadc3af 0xfff83fe07fff1ffe 0xfffe0ff81fffc7ff

def z42 : W := mkw 0x8db7efdfef6dfff7 0xe36dfbf7fbdb7ffd 0xffffffffffffffff 0xffffffffffffffff

def z43 : W := mkw 0x080141128760e3c3 0x02005044a1d838f0 0x2000000007e0e3c0 0x0800000001f838f0

def z44 : W := mkw 0x026a300000000000 0x009a8c0000000000 0x1078380000000000 0x841e0e0000000000

def z45 : W := mkw 0x0985c49b8560e1c3 0x02617126e1583870 0x0387c09f81e0e0c1 0x40e1f027e0783830

def z46 : W := mkw 0x04010112260cb730 0xc100404489832dcc 0x24000000061cff30 0x0900000001873fcc

def z47 : W := mkw 0x13fffeed55dbd800 0x04ffffbb5576f600 0xfffffffffffffc03 0xffffffffffffff00

def z48 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bf707fff8000002 0x26fdc1fffe000000

def z49 : W := mkw 0x0184858902200280 0x00612162408800a0 0xeb87c79f87e003c3 0x7ae1f1e7e1f800f0

def z50 : W := mkw 0x009007ed522402a8 0x002401fb548900aa 0x080007fff80003fe 0x020001fffe0000ff

def z51 : W := mkw 0x02c804a000b20088 0x00b20128002c8022 0x0380000000e00000 0x00e0000000380000

def z52 : W := mkw 0x07ffb7ff760cb730 0xc1ffedffdd832dcc 0xfffffffffe1cff33 0xffffffffff873fcc

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008f8f1f8000003 0xd0023e3c7e000000

def z54 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff8fff1ffff03ff 0xfffe3ffc7fffc0ff

def z55 : W := mkw 0x177fb35666deb730 0xc5dfecd599b7adcc 0xfff7275e66fcff33 0xbffdc9d799bf3fcc

def z56 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x2408d8a19903fffc 0x490236286640ffff

def z57 : W := mkw 0x049007ff72042730 0xc12401ffdc8109cc 0x080007fff8000332 0x020001fffe0000cc

def z58 : W := mkw 0x0beff59b8760e3c3 0x02fbfd66e1d838f0 0xfbffff9f87e0e3c3 0xfeffffe7e1f838f0

def z59 : W := mkw 0x04322244600c1430 0xc10c88911803050c 0x14702040601c1c30 0x851c08101807070c

def z60 : W := mkw 0x00004010a1006552 0x8000100428401954 0x6400e0d1e100fff3 0xd900383478403ffc

def z61 : W := mkw 0x8000080008010804 0x2000020002004201 0x000818201803000c 0x000206080600c003

def z62 : W := mkw 0x0258026000960028 0x009600980025800a 0x14780060001f003c 0x851e00180007c00f

def z63 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x6408f811f903fc01 0xd9023e047e40ff00

def z64 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xeb87078e07e003c2 0x7ae1c1e381f800f0

def z65 : W := mkw 0x80904efdf9016d56 0xa02413bf7e405b55 0x6c08fffff903ffff 0xdb023ffffe40ffff

def z66 : W := mkw 0x0000010002b602a8 0x0000004000ad80aa 0x2400000007ff03fc 0x0900000001ffc0ff

def z67 : W := mkw 0x03feb6ed50b20088 0x00ffadbb542c8022 0xdbfffffff9e300cf 0xf6fffffffe78c033

def z68 : W := mkw 0x0184848900000000 0x0061212240000000 0xcb87c79f80000003 0x72e1f1e7e0000000

def z69 : W := mkw 0x0984c489816040c3 0x0261312260581030 0x0380c08181e000c0 0x40e0302060780030

def z70 : W := mkw 0x134cd80001d34800 0x04d336000074d200 0x6788f80001e3fc01 0xd9e23e000078ff00

def z71 : W := mkw 0x03fef6fdd1006142 0x00ffbdbf74401850 0xfbfffffff900e3c3 0xfefffffffe4038f0

def z72 : W := mkw 0x07ffb7ff76beb7b8 0xc1ffedffddafadee 0xffffffffffffffff 0xffffffffffffffff

def z73 : W := mkw 0x1127f80d5549d800 0x0449fe0355527600 0x0007f81ff800fc01 0x0001fe07fe003f00

def z74 : W := mkw 0x03feb7ed52b602a8 0x00ffadfb54ad80aa 0xffffffffffff03ff 0xffffffffffffc0ff

def z75 : W := mkw 0x1127f8000549d800 0x0449fe0001527600 0x0007f8000000fc01 0x0001fe0000003f00

def z76 : W := mkw 0x0126b00d50000000 0x0049ac0354000000 0x0007f81ff8000001 0x0001fe07fe000000

def z77 : W := mkw 0x07ffb6ff7408b510 0xc1ffedbfdd022d44 0xdbfffffff800fc03 0xf6fffffffe003f00

def z78 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x8b87c71f86e0e001 0x22e1f1c7e1b83800

def z79 : W := mkw 0x10000800009b1800 0x040002000026c600 0x04000000001f1c00 0x010000000007c700

def z80 : W := mkw 0x136fb80004db9800 0x04dbee000136e600 0x97ff380006ff1c00 0xa5ffce0001bfc700

def z81 : W := mkw 0x80004910abb76ffe 0xa00012442aeddbff 0x6408f8f1ffffffff 0xd9023e3c7fffffff

def z82 : W := mkw 0x17fffff667ffffb8 0xc5fffffd99ffffee 0xfffffffe67ffffff 0xffffffff99ffffff

def z83 : W := mkw 0x000100120400a100 0x0000400481002840 0x0007001e0000e001 0x0001c00780003800

def z84 : W := mkw 0x0258026000960028 0x009600980025800a 0x10700000001c0000 0x041c000000070000

def z85 : W := mkw 0x0032224440000000 0x000c889110000000 0xd877275e60000003 0xb61dc9d798000000

def z86 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8f1fffffc03 0xfdfffe3c7fffff00

def z87 : W := mkw 0x8000480089014846 0x2000120022405211 0x0008d8a1990300cc 0x400236286640c033

def z88 : W := mkw 0x936ff8008ddbd846 0x24dbfe002376f611 0xf7fff8a19ffffccd 0xfdfffe2867ffff33

def z89 : W := mkw 0x0801010206608281 0x02004040819820a0 0x0000000006e00000 0x0000000001b80000

def z90 : W := mkw 0x0000480001014800 0x0000120000405200 0x6408f8000103fc01 0xd9023e000040ff00

def z91 : W := mkw 0x936ff810addbfd56 0xa4dbfe042b76ff55 0xf7fff8f1ffffffff 0xfdfffe3c7fffffff

def z92 : W := mkw 0x06fb27f666beb7b8 0xc1bec9fd99afadee 0xffff27fe67ffffff 0xffffc9ff99ffffff

def z93 : W := mkw 0x0000481021016d10 0x8000120408405b44 0x6408f8506103ff33 0xd9023e141840ffcc

def z94 : W := mkw 0x0d95c7dfe764e7f3 0xc36571f7f9d939fc 0xeb87c7dfe7e0e3f3 0x7ae1f1f7f9f838fc

def z95 : W := mkw 0x009007e0022402a8 0x002401f8008900aa 0xeb8007e007e003fe 0x7ae001f801f800ff

def z96 : W := mkw 0x80000010a8002556 0xa00000042a000955 0x000000f1f80003fe 0x0000003c7e0000ff

def z97 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7f27fe671fffff 0xff1fc9ff99c7ffff

def z98 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0000f811f800fc01 0x00003e047e003f00

def z99 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xeb87ff9fffe0ffc3 0x7ae1ffe7fff83ff0

def z100 : W := mkw 0x136ef80001db5800 0x04dbbe000076d600 0x17f8f80001ff1c00 0xc5fe3e00007fc700

def z101 : W := mkw 0x8bddcffbaff7efff 0xa2f773feebfdfbff 0xffffffffffffffff 0xffffffffffffffff

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x400800e000000002 0xd002003800000000

def z103 : W := mkw 0x0985c59b87f6e3eb 0x02617166e1fdb8fa 0xef87c79f87ffe3ff 0x7be1f1e7e1fff8ff

def z104 : W := mkw 0x0bffb7ef56608281 0x02ffedfbd59820a0 0x9bf7070e06e00000 0x26fdc1c381b80000

def z105 : W := mkw 0x127a3a64509b1800 0x049e8e991426c600 0x14783860781f1c00 0x851e0e181e07c700

def z106 : W := mkw 0x0248000000920000 0x0092000000248000 0xf7f800e007ff03fe 0xfdfe003801ffc0ff

def z107 : W := mkw 0x9127f810ad49fd56 0xa449fe042b527f55 0x0007f811f800fc01 0x0001fe047e003f00

def z108 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbff07ee00000002 0xf6ffc1fb80000000

def z109 : W := mkw 0x934cd80089d34846 0x24d336002274d211 0x0388d8a199e300cc 0x40e236286678c033

def z110 : W := mkw 0x0000010002040220 0x0000004000810088 0x24000000061c0330 0x09000000018700cc

def z111 : W := mkw 0x00000100022402a8 0x00000040008900aa 0x00000000000003fc 0x00000000000000ff

def z112 : W := mkw 0x0905c01b8540e143 0x02417006e1503850 0x0007c01f8000e001 0x0001f007e0003800

def z113 : W := mkw 0x03cc94a910000000 0x00f3252a44000000 0x0388d8a198000000 0x40e2362866000000

def z114 : W := mkw 0x0104800000000000 0x0041200000000000 0xc387c00000000001 0x70e1f00000000000

def z115 : W := mkw 0x83fefefdf9016d56 0xa0ffbfbf7e405b55 0xfffffffff903ffff 0xfffffffffe40ffff

def z116 : W := mkw 0x002368000509d800 0x0008da0001427600 0xf47ff800071ffc01 0xfd1ffe0001c7ff00

def z117 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x038ff80001e3fc01 0x40e3fe000078ff00

def z118 : W := mkw 0x0258026000960028 0x009600980025800a 0xf7f8006007ff003c 0xfdfe001801ffc00f

def z119 : W := mkw 0x8126f81df9016d56 0xa049be077e405b55 0x640ff8fff903ffff 0xd903fe3ffe40ffff

def z120 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x6400c0918103ffff 0x590030246040ffff

def z121 : W := mkw 0x088145928760e3c3 0x02205164a1d838f0 0xeb80078007e0e3c2 0x7ae001e001f838f0

def z122 : W := mkw 0x19a7fd9b8769fbc3 0x0669ff66e1da7ef0 0xeb87ff9f87e0ffc3 0x7ae1ffe7e1f83ff0

def z123 : W := mkw 0x87ffffffff0dff76 0xe1ffffffffc37fdd 0xffffffffff1fffff 0xffffffffffc7ffff

def z124 : W := mkw 0x0927f01fd540e143 0x0249fc07f5503850 0x0007f81ff800e001 0x0001fe07fe003800

def z125 : W := mkw 0x84014912af0dff76 0xe1005244abc37fdd 0x24000000071ffffc 0x0900000001c7ffff

def z126 : W := mkw 0x84322a44680d1c34 0xe10c8a911a03470d 0x14783860781f1c3c 0x851e0e181e07c70f

def z127 : W := mkw 0x0410035662042730 0xc10400d5988109cc 0xfc70075e661c0332 0xbf1c01d7998700cc

def z128 : W := mkw 0x0010035022042730 0x800400d4088109cc 0xfc702750661cff33 0xbf1c09d419873fcc

def z129 : W := mkw 0x134cd80001d34800 0x04d336000074d200 0x0388d80001e30000 0x40e236000078c000

def z130 : W := mkw 0x809007f0aa2427fe 0xa02401fc2a8909ff 0x080007f1f80003fe 0x020001fc7e0000ff

def z131 : W := mkw 0x0185c4890540c000 0x0061712241503000 0xeb87c79f87e0e003 0x7ae1f1e7e1f83800

def z132 : W := mkw 0x0184c49981006142 0x0061312660401850 0xeb87c79f8100e3c3 0x7ae1f1e7e04038f0

def z133 : W := mkw 0x0184848900000000 0x0061212240000000 0x8b87070e00000000 0x22e1c1c380000000

def z134 : W := mkw 0x0185c5800760c280 0x0061716001d830a0 0xeb87c78007e0e3c3 0x7ae1f1e001f838f0

def z135 : W := mkw 0x80000010a8002556 0xa00000042a000955 0x00000000000003fc 0x00000000000000ff

def z136 : W := mkw 0x80000010a8002556 0xa00000042a000955 0x640020f1f800ffff 0x9900083c7e003fff

def z137 : W := mkw 0x126a3800009b1800 0x049a8e000026c600 0x14783800001f1c00 0x851e0e000007c700

def z138 : W := mkw 0x1beffd9b87fbfbc3 0x06fbff66e1fefef0 0xffffff9f87ffffc3 0xffffffe7e1fffff0

def z139 : W := mkw 0x80004010a9006556 0xa00010042a401955 0x6000c0f1f900e3ff 0x5800303c7e4038ff

def z140 : W := mkw 0x009006e000000000 0x002401b800000000 0x080007e000000002 0x020001f800000000

def z141 : W := mkw 0x82484810a9936d56 0xa09212042a64db55 0xf7f8f8f1ffffffff 0xfdfe3e3c7fffffff

def z142 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bf7ff1ff8000001 0x26fdffc7fe000000

def z143 : W := mkw 0x0881459b8760e3c3 0x02205166e1d838f0 0x2800079f87e0e3c2 0x0a0001e7e1f838f0

def z144 : W := mkw 0x0bfeb7ffd22023c3 0x02ffadfff48808f0 0xdbfffffff80003c3 0xf6fffffffe0000f0

def z145 : W := mkw 0x06fb27f6660cb730 0xc1bec9fd99832dcc 0xffff27fe661cff33 0xffffc9ff99873fcc

def z146 : W := mkw 0x8184cc99a9016d56 0xa06133266a405b55 0xef8ffffff903ffff 0xfbe3fffffe40ffff

def z147 : W := mkw 0x0880059b822023c3 0x02200166e08808f0 0x0800079f800003c2 0x020001e7e00000f0

def z148 : W := mkw 0x0080058002200280 0x00200160008800a0 0x8b80070006e00000 0x22e001c001b80000

def z149 : W := mkw 0x0000010002b602a8 0x0000004000ad80aa 0x0000000006fc0000 0x0000000001bf0000

def z150 : W := mkw 0x136ff80d55dbd800 0x04dbfe035576f600 0xf7fff81ffffffc01 0xfdfffe07ffffff00

def z151 : W := mkw 0x0bfff6ffd540e143 0x02fffdbff5503850 0xdbfffffff800e003 0xf6fffffffe003800

def z152 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x9ff8076006ff003c 0xa7fe01d801bfc00f

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x000800a0010300cc 0x400200280040c033

def z154 : W := mkw 0x8000080028010c14 0xa00002000a004305 0x0000380078001c00 0x00000e001e000700

def z155 : W := mkw 0x82c84ca089b348ce 0x20b21328226cd233 0x0388d8a199e300cc 0x40e236286678c033

def z156 : W := mkw 0x0105800004408000 0x0041600001102000 0x8387000006e00000 0x20e1c00001b80000

def z157 : W := mkw 0x0105c0108540e142 0x0041700421503850 0xe387c09187e0e3c3 0x78e1f02461f838f0

def z158 : W := mkw 0x02c804a000b20088 0x00b20128002c8022 0x038800a001e300cc 0x40e200280078c033

def z159 : W := mkw 0x80000010a8002556 0xa00000042a000955 0x640800f1f90303fe 0xd902003c7e40c0ff

def z160 : W := mkw 0x0bddc7fb8760e3c3 0x02f771fee1d838f0 0xfbffc7ff87e0e3c3 0xfefff1ffe1f838f0

def z161 : W := mkw 0x009006ed50000000 0x002401bb54000000 0x080007fff8000002 0x020001fffe000000

def z162 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8e007ffffff 0xfdfffe3801ffffff

def z163 : W := mkw 0x0410035662042730 0xc10400d5988109cc 0x0800075e60000332 0x020001d7980000cc

def z164 : W := mkw 0x0c9007dfe22427f3 0xc32401f7f88909fc 0x080007dfe00003f2 0x020001f7f80000fc

def z165 : W := mkw 0x177ffb5667dfff30 0xc5dffed599f7ffcc 0xffffff5e67ffff33 0xffffffd799ffffcc

def z166 : W := mkw 0x167b3b56669fbf30 0xc59eced599a7efcc 0xfc7f3f5e661fff33 0xbf1fcfd79987ffcc

def z167 : W := mkw 0x036eb00d50000000 0x00dbac0354000000 0xd3fff81ff8000001 0xf4fffe07fe000000

def z168 : W := mkw 0x0ffff7fff76cf7f3 0xc3fffdfffddb3dfc 0xfffffffffffcfff3 0xffffffffffff3ffc

def z169 : W := mkw 0x008004a910000000 0x0020012a44000000 0x000000a198000000 0x0000002866000000

def z170 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x9bf0070006fc0000 0x26fc01c001bf0000

def z171 : W := mkw 0x83fefefdf9016d56 0xa0ffbfbf7e405b55 0xdbfffffff800fc03 0xf6fffffffe003f00

def z172 : W := mkw 0x167a3a44609f1c30 0xc59e8e911827c70c 0x14783840601f1c30 0x851e0e101807c70c

def z173 : W := mkw 0x0105c8000541c800 0x0041720001507200 0xe78ff80007e3fc01 0xf9e3fe0001f8ff00

def z174 : W := mkw 0x0000000000000000 0x0000000000000000 0x040800600003003c 0x810200180000c00f

def z175 : W := mkw 0x002321120608b300 0x0008c84481822cc0 0xfc77271e061cff03 0xbf1dc9c781873fc0

def z176 : W := mkw 0x1000480001d34800 0x040012000074d200 0x0000000001e30000 0x000000000078c000

def z177 : W := mkw 0x1bcddd9b87f3ebc3 0x06f37766e1fcfaf0 0xeb8fdf9f87e3e3c3 0x7ae3f7e7e1f8f8f0

def z178 : W := mkw 0x06fb27e646be92a8 0x41bec9f991afa4aa 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z179 : W := mkw 0x0000001020002510 0x8000000408000944 0x0000005060000332 0x00000014180000cc

def z180 : W := mkw 0x8000080028010c14 0xa00002000a004305 0x0408386078031c3c 0x81020e181e00c70f

def z181 : W := mkw 0x137ffb4007dfda20 0x04dffed001f7f688 0xffffff4007ffff33 0xffffffd001ffffcc

def z182 : W := mkw 0x8000080028010c14 0xa00002000a004305 0x4408f8f1f8031c3f 0xd1023e3c7e00c70f

def z183 : W := mkw 0x01b6a6cd40000000 0x006da9b350000000 0xdbf7e7dfe0000003 0xf6fdf9f7f8000000

def z184 : W := mkw 0x0010034002b602a8 0x000400d000ad80aa 0xfc70074007ff03fe 0xbf1c01d001ffc0ff

def z185 : W := mkw 0x04010102060c9220 0x4100404081832488 0x00000000061c0000 0x0000000001870000

def z186 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xab87070e07e0e3c0 0x2ae1c1c381f838f0

def z187 : W := mkw 0x0db7e7dfe76cf7f3 0xc36df9f7f9db3dfc 0xfff7e7dfe7fcfff3 0xfffdf9f7f9ff3ffc

def z188 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbf7c79f80000003 0x76fdf1e7e0000000

def z189 : W := mkw 0x02d806e000b600a8 0x00b601b8002d802a 0x17f800e001ff00fc 0xc5fe0038007fc03f

def z190 : W := mkw 0x0248480001934800 0x009212000064d200 0xf7f8f80007fffc01 0xfdfe3e0001ffff00

def z191 : W := mkw 0x02d806e000960028 0x00b601b80025800a 0xdff807e0001f003e 0xf7fe01f80007c00f

def z192 : W := mkw 0x0023200004089000 0x0008c80001022400 0x90770000061c0000 0x241dc00001870000

def z193 : W := mkw 0x042320166408b510 0xc108c80599022d44 0x0007201e6000fc01 0x0001c80798003f00

def z194 : W := mkw 0x080141128760e3c3 0x02005044a1d838f0 0xe807071e07e0e3c3 0x3a01c1c781f838f0

def z195 : W := mkw 0x008004a000200088 0x0020012800080022 0x000000a0000000cc 0x0000002800000033

def z196 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0x9877070e061c0000 0x261dc1c381870000

def z197 : W := mkw 0x0985cd9b8761ebc3 0x02617366e1d87af0 0xef8fff9f87e3ffc3 0xfbe3ffe7e1f8fff0

def z198 : W := mkw 0x0bfff7ffd760e3c3 0x02fffdfff5d838f0 0xfbf7c79f87e0e3c3 0x7efdf1e7e1f838f0

def z199 : W := mkw 0x0022200000081000 0x0008880000020400 0x14702000001c1c00 0x851c080000070700

def z200 : W := mkw 0x1befb58b06fa9281 0x06fbed62c1bea4a0 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z201 : W := mkw 0x8000480029014c14 0xa00012000a405305 0x6408f8607903fc3d 0xd9023e181e40ff0f

def z202 : W := mkw 0x0c336356e76cf7f3 0xc30cd8d5b9db3dfc 0xfc77275e67fcfff3 0xbf1dc9d799ff3ffc

def z203 : W := mkw 0x90014810addbfd56 0xa40052042b76ff55 0x6408f8f1ffffffff 0xd9023e3c7fffffff

def z204 : W := mkw 0x02c805a002b20288 0x00b2016800ac80a2 0xeb8807a007e303ce 0x7ae201e801f8c0f3

def z205 : W := mkw 0x8985cd9b8f61ebc7 0x22617366e3d87af1 0xeb8fdfbf9fe3e3cf 0x7ae3f7efe7f8f8f3

def z206 : W := mkw 0x8905c81bad41ed57 0xa2417206eb507b55 0x640ff8fff903ffff 0xd903fe3ffe40ffff

def z207 : W := mkw 0x0000480001014800 0x0000120000405200 0x6408f8e00103ffff 0xd9023e380040ffff

def z208 : W := mkw 0x0d85c59ba76cf7f3 0xc3617166e9db3dfc 0xef87c79f87fcfff3 0x7be1f1e7e1ff3ffc

def z209 : W := mkw 0x036eb00000000000 0x00dbac0000000000 0x93f7000000000000 0x24fdc00000000000

def z210 : W := mkw 0x84100356ea042776 0xe10400d5ba8109dd 0x080007fff80003fe 0x020001fffe0000ff

def z211 : W := mkw 0x13effca005fbd888 0x04fbff28017ef622 0xf7fff8a007fffccd 0xfdfffe2801ffff33

def z212 : W := mkw 0x1127f8000549d800 0x0449fe0001527600 0xf477f800061cfc01 0xbd1dfe0001873f00

def z213 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x93f7f80006fcfc01 0x24fdfe0001bf3f00

def z214 : W := mkw 0x0127e0000548d000 0x0049f80001523400 0xf7f7e00007fcfc01 0xfdfdf80001ff3f00

def z215 : W := mkw 0x0904c00981404043 0x0241300260501010 0x0000c00180000000 0x0000300060000000

def z216 : W := mkw 0x0bddc7fb87f6e3eb 0x02f771fee1fdb8fa 0xfbf7c79f87fce3c3 0x7efdf1e7e1ff38f0

def z217 : W := mkw 0x02d806e000000000 0x00b601b800000000 0xdbf807e000000002 0xf6fe01f800000000

def z218 : W := mkw 0x0000400001004000 0x0000100000401000 0x6000c0000100e001 0x5800300000403800

def z219 : W := mkw 0x0000401081006142 0x0000100420401850 0x6000c0918100e3c3 0x58003024604038f0

def z220 : W := mkw 0x0022200440000000 0x0008880110000000 0x0007201e60000001 0x0001c80798000000

def z221 : W := mkw 0x026b2000049a9000 0x009ac8000126a400 0xf7ff200007fffc01 0xfdffc80001ffff00

def z222 : W := mkw 0x0000480001014800 0x0000120000405200 0x0000f8000000fc01 0x00003e0000003f00

def z223 : W := mkw 0x0410024460040430 0xc10400911801010c 0x0000004060000030 0x000000101800000c

def z224 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0xf7f7200006fcfc01 0xbdfdc80001bf3f00

def z225 : W := mkw 0x8984cc89896148c7 0x2261332262585231 0x0388d8a199e300cc 0x40e236286678c033

def z226 : W := mkw 0x0136b24d50000000 0x004dac9354000000 0xd877ff5ff8000003 0xb61dffd7fe000000

def z227 : W := mkw 0x0000480001014800 0x0000120000405200 0x0008d80001030000 0x400236000040c000

def z228 : W := mkw 0x8880059baa2027d7 0xa2200166ea8809f5 0x080007fff80003fe 0x020001fffe0000ff

def z229 : W := mkw 0x134dd80005dbd800 0x04d376000176f600 0x2788d80007fffc00 0x49e2360001ffff00

def z230 : W := mkw 0x04110356660cb730 0xc10440d599832dcc 0x2c00075e661cff32 0x0b0001d799873fcc

def z231 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bffdfaf98000000 0x66fff7ebe6000000

def z232 : W := mkw 0x0104800900000000 0x0041200240000000 0x0007c01f80000001 0x0001f007e0000000

def z233 : W := mkw 0x13ffffe007ffdaa8 0x04fffff801fff6aa 0xffffff0007fffc01 0xffffffc001ffff00

def z234 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff8070007ff0000 0xfffe01c001ffc000

def z235 : W := mkw 0x03feb6ed50960028 0x00ffadbb5425800a 0xdffffffff81f003f 0xf7fffffffe07c00f

def z236 : W := mkw 0x13ccdca001f34888 0x04f33728007cd222 0x0388d8a001e300cc 0x40e236280078c033

def z237 : W := mkw 0x0bcdd5bb9760e3c3 0x02f3756ee5d838f0 0xeb8fdfbf9fe0e3c3 0x7ae3f7efe7f838f0

def z238 : W := mkw 0x03cc94a910000000 0x00f3252a44000000 0x0380000000000000 0x00e0000000000000

def z239 : W := mkw 0x0bfff7ffd760e3c3 0x02fffdfff5d838f0 0xfbffffffffe0e3c3 0xfefffffffff838f0

def z240 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0008d8f1f90303fe 0x4002363c7e40c0ff

def z241 : W := mkw 0x0985859b0660a381 0x02616166c19828e0 0xeb87071e06e0e303 0x3ae1c1c781b838c0

def z242 : W := mkw 0x043322566408b510 0xc10cc89599022d44 0xd877275e6000fc03 0xb61dc9d798003f00

def z243 : W := mkw 0x137ffa6455dbd800 0x04dffe991576f600 0xf7fff8607ffffc01 0xfdfffe181fffff00

def z244 : W := mkw 0x0032225460002510 0x800c889518000944 0xfc77275e6000ff33 0xbf1dc9d798003fcc

def z245 : W := mkw 0x0000000000960028 0x000000000025800a 0x04000000001f003c 0x010000000007c00f

def z246 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x2380c08187e0e3c0 0x48e0302061f838f0

def z247 : W := mkw 0x1105c80005dbd800 0x044172000176f600 0xe787c00007fffc01 0x79e1f00001ffff00

def z248 : W := mkw 0x03feb6e000000000 0x00ffadb800000000 0xdbffffe000000003 0xf6fffff800000000

def z249 : W := mkw 0x02d806e000000000 0x00b601b800000000 0xdbf8fff1f8000003 0xf6fe3ffc7e000000

def z250 : W := mkw 0x03eeb48900000000 0x00fbad2240000000 0xdbffff9f80000003 0xf6ffffe7e0000000

def z251 : W := mkw 0x0105c0000540c000 0x0041700001503000 0x0007c0000000e001 0x0001f00000003800

def z252 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb8fffffffe0e3c3 0xfae3fffffff838f0

def z253 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bff3f6e78000000 0xa6ffcfdb9e000000

def z254 : W := mkw 0x126a7800019b5800 0x049a9e000066d600 0x7478f800011ffc01 0xdd1e3e000047ff00

def z255 : W := mkw 0x036eb00000000000 0x00dbac0000000000 0xd3fff8f1f8000003 0xf4fffe3c7e000000

def z256 : W := mkw 0x04232116660cb730 0xc108c84599832dcc 0x2407201e661cff31 0x0901c80799873fcc

def z257 : W := mkw 0x0985c49b8540e143 0x02617126e1503850 0xcb87c79f8000e003 0x72e1f1e7e0003800

def z258 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bf7070e00000000 0x26fdc1c380000000

def z259 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x240000000103fffc 0x090000000040ffff

def z260 : W := mkw 0x067b2356669eb730 0xc19ec8d599a7adcc 0xffff275e67ffff33 0xffffc9d799ffffcc

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x6408000001030000 0xd90200000040c000

def z262 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xbc77070e061cff30 0x2f1dc1c381873fcc

def z263 : W := mkw 0x13dcdfe003f74aa8 0x04f737f800fdd2aa 0xfff8dfe007ff03fe 0xfffe37f801ffc0ff

def z264 : W := mkw 0x0537b35f760cb730 0xc14decd7dd832dcc 0xfc77ff5ffe1cff33 0xbf1dffd7ff873fcc

def z265 : W := mkw 0x0995c7db8764e3e3 0x026571f6e1d938f8 0xfff7c7df87fce3f3 0xfffdf1f7e1ff38fc

def z266 : W := mkw 0x8105c810ad41ed56 0xa04172042b507b55 0xe78ff8f1ffe3ffff 0xf9e3fe3c7ff8ffff

def z267 : W := mkw 0x036eb00000920000 0x00dbac0000248000 0xf7fff80007ff0001 0xfdfffe0001ffc000

def z268 : W := mkw 0x1537fb56674dff30 0xc54dfed599d37fcc 0xfc77ff5e661cff33 0xbf1dffd799873fcc

def z269 : W := mkw 0x02c804a000b20088 0x00b20128002c8022 0x678800e001e303fe 0xd9e200380078c0ff

def z270 : W := mkw 0x84332b566e0dbf34 0xe10ccad59b836fcd 0xfc7f3f7e7e1fff3f 0xbf1fcfdf9f87ffcf

def z271 : W := mkw 0x000101120600a300 0x00004044818028c0 0x200000000600e300 0x08000000018038c0

def z272 : W := mkw 0x0881059b8620a3c3 0x02204166e18828f0 0xe807079f8600e3c3 0x3a01c1e7e18038f0

def z273 : W := mkw 0x0032224440000000 0x000c889110000000 0xd87ffffff8000003 0xf61ffffffe000000

def z274 : W := mkw 0x03feb7ed52040220 0x00ffadfb54810088 0xfffffffffe1c0333 0xffffffffff8700cc

def z275 : W := mkw 0x02d807e002200280 0x00b601f8008800a0 0xfbf807e007e003c2 0xfefe01f801f800f0

def z276 : W := mkw 0x80000010a8002556 0xa00000042a000955 0x00000011f8000000 0x000000047e000000

def z277 : W := mkw 0x0984848900600081 0x0261212240180020 0x0380000000e00000 0x00e0000000380000

def z278 : W := mkw 0x041103566604a730 0xc10440d5998129cc 0xe807075e6600e333 0x3a01c1d7998038cc

def z279 : W := mkw 0x0184848900000000 0x0061212240000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z281 : W := mkw 0x0010034002040220 0x000400d000810088 0xfc700740061c0332 0xbf1c01d0018700cc

def z282 : W := mkw 0x0400001660002510 0xc100000598000944 0x0000001e60000000 0x0000000798000000

def z283 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef87c79f87e3ffff 0x7be1f1e7e1f8ffff

def z284 : W := mkw 0x83feb6fdf8002556 0xa0ffadbf7e000955 0xdbfffffff80003ff 0xf6fffffffe0000ff

def z285 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x6400f851f800ff33 0x99003e147e003fcc

def z286 : W := mkw 0x0880059b822023c3 0x02200166e08808f0 0xeb80079f87e003c2 0x7ae001e7e1f800f0

def z287 : W := mkw 0x019486ed50000000 0x006521bb54000000 0xcb87c7fff8000003 0x72e1f1fffe000000

def z288 : W := mkw 0x03cc94a910000000 0x00f3252a44000000 0x4388f8f1f8000003 0xd0e23e3c7e000000

def z289 : W := mkw 0x0001010206008200 0x0000404081802080 0x8807070e06000000 0x2201c1c381800000

def z290 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xdbf807e006fc0002 0xf6fe01f801bf0000

def z291 : W := mkw 0x0258026000960028 0x009600980025800a 0x747800e0011f03fe 0xdd1e00380047c0ff

def z292 : W := mkw 0x04336b56670dff30 0xc10cdad599c37fcc 0xfc7fff5e671fff33 0xff1fffd799c7ffcc

def z293 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x9877075e661c0332 0x261dc1d7998700cc

def z294 : W := mkw 0x01b6b6ed50000000 0x006dadbb54000000 0x0807fffff8000003 0x0201fffffe000000

def z295 : W := mkw 0x0bcdc59b87f2e3c3 0x02f37166e1fcb8f0 0xffffc79f87ffe3c3 0xfffff1e7e1fff8f0

def z296 : W := mkw 0x137ffa4445dbd800 0x04dffe911176f600 0xffffff5e67fffc03 0xffffffd799ffff00

def z297 : W := mkw 0x07feb7ff72042730 0xc1ffadffdc8109cc 0xdbfffffff8000333 0xf6fffffffe0000cc

def z298 : W := mkw 0x13ffb6ed54da9000 0x04ffedbb5536a400 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z299 : W := mkw 0x02c8058002b20280 0x00b2016000ac80a0 0xfff8078007ff03c2 0xfffe01e001ffc0f0

def z300 : W := mkw 0x027a326450960028 0x009e8c991425800a 0x14783860781f003c 0x851e0e181e07c00f

def z301 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x640020506103ffff 0x990008141840ffff

def z302 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xb7f7000007fffc00 0x2dfdc00001ffff00

def z303 : W := mkw 0x06fa27e462be16b8 0xc1be89f918af85ae 0xfff827e067ff1ffe 0xfffe09f819ffc7ff

def z304 : W := mkw 0x84236816ed09fd56 0xe108da05bb427f55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z305 : W := mkw 0x0db7a7df666cb7b1 0xc36de9f7d99b2dec 0xfff7275e66fcff33 0xbffdc9d799bf3fcc

def z306 : W := mkw 0x03feb7ed52b602a8 0x00ffadfb54ad80aa 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z307 : W := mkw 0x04322254600c3530 0xc10c889518030d4c 0x74702050601cff33 0x9d1c081418073fcc

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000f811f8000001 0x00003e047e000000

def z309 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x1c7807e0001f03fe 0x871e01f80007c0ff

def z310 : W := mkw 0x0010024000040020 0x0004009000010008 0x14700040001c0030 0x851c00100007000c

def z311 : W := mkw 0x00332340060c9220 0x000cc8d001832488 0xfc772740061cff33 0xbf1dc9d001873fcc

def z312 : W := mkw 0x0985c58b8760c2c3 0x02617162e1d830b0 0x8b87c78f87e000c0 0x62e1f1e3e1f80030

def z313 : W := mkw 0x0905800b04408001 0x02416002c1102000 0x0007000e00000000 0x0001c00380000000

def z314 : W := mkw 0x0984859b822023c3 0x02612166e08808f0 0xcb87c79f800003c3 0x72e1f1e7e00000f0

def z315 : W := mkw 0x0258034002960220 0x009600d000a58088 0xfff8074007ff0332 0xfffe01d001ffc0cc

def z316 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x9bf807a007ff00cc 0x66fe01e801ffc033

def z317 : W := mkw 0x126a3000009a1000 0x049a8c0000268400 0x10700000001c0000 0x041c000000070000

def z318 : W := mkw 0x0410035662042730 0xc10400d5988109cc 0x6c00275e6000ff33 0x9b0009d798003fcc

def z319 : W := mkw 0x13fffeed5549d800 0x04ffffbb55527600 0xdbfffffff800fc03 0xf6fffffffe003f00

def z320 : W := mkw 0x02d806ed50000000 0x00b601bb54000000 0xdbf807fff8000002 0xf6fe01fffe000000

def z321 : W := mkw 0x80014912af01ef56 0xa0005244abc07bd5 0xec0fffffff03ffff 0xfb03ffffffc0ffff

def z322 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0xfc77270e061cfc01 0xbf1dc9c381873f00

def z323 : W := mkw 0x0000010002200280 0x00000040008800a0 0x2000000007e003c0 0x0800000001f800f0

def z324 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfffffffff90303ff 0xfffffffffe40c0ff

def z325 : W := mkw 0x0000010002b602a8 0x0000004000ad80aa 0x640800e007ff03fe 0xd902003801ffc0ff

def z326 : W := mkw 0x0bdd87eb06f682a9 0x02f761fac1bda0aa 0xffff07ee07ff03fe 0xffffc1fb81ffc0ff

def z327 : W := mkw 0x01a6b48d50000000 0x0069ad2354000000 0xcb87ff9ff8000003 0x72e1ffe7fe000000

def z328 : W := mkw 0x02fa27e442b602a8 0x00be89f910ad80aa 0xffff27fe67ff03ff 0xffffc9ff99ffc0ff

def z329 : W := mkw 0x0984c489816040c3 0x0261312260581030 0xcb87c79f81e000c3 0x72e1f1e7e0780030

def z330 : W := mkw 0x1001480005dbd800 0x040052000176f600 0x6408f80007fffc01 0xd9023e0001ffff00

def z331 : W := mkw 0x04322244600c1430 0xc10c88911803050c 0xdc77275e601c1c33 0xb71dc9d79807070c

def z332 : W := mkw 0x0984c499816061c3 0x0261312660581870 0x6380c09181e0e3c3 0x58e03024607838f0

def z333 : W := mkw 0x04322356620c3730 0xc10c88d598830dcc 0x1c70275e601c1f32 0x871c09d7980707cc

def z334 : W := mkw 0x134cd80001d34800 0x04d336000074d200 0xf7f8d80007ff0000 0xfdfe360001ffc000

def z335 : W := mkw 0x00804590832063c2 0x0020116420c818f0 0xeb80c79187e0e3c3 0x7ae031e461f838f0

def z336 : W := mkw 0x82d84ff0abb76ffe 0xa0b613fc2aeddbff 0xfff807e007fffffe 0xfffe01f801ffffff

def z337 : W := mkw 0x1127f80005dbd800 0x0449fe000176f600 0x2407f80007fffc01 0x0901fe0001ffff00

def z338 : W := mkw 0x049007f6622427b8 0xc12401fd988909ee 0x080007fe600003fe 0x020001ff980000ff

def z339 : W := mkw 0x84014912af0dff76 0xe1005244abc37fdd 0x6408f8f1ff1fffff 0xd9023e3c7fc7ffff

def z340 : W := mkw 0x03fff6ed5540c000 0x00fffdbb55503000 0xfbffffffffe0e003 0xfefffffffff83800

def z341 : W := mkw 0x0bdcc7e983f642eb 0x02f731fa60fd90ba 0xfff8c7e187ff03fe 0xfffe31f861ffc0ff

def z342 : W := mkw 0x06fb27e646be92a8 0x41bec9f991afa4aa 0xffff07ee07ff03fe 0xffffc1fb81ffc0ff

def z343 : W := mkw 0x1bccdc8981f348c3 0x06f33722607cd230 0x0388d88181e300c0 0x40e236206078c030

def z344 : W := mkw 0x134dd80005d3c800 0x04d376000174f200 0xe38fd80007e3e001 0x78e3f60001f8f800

def z345 : W := mkw 0x042320166408b510 0xc108c80599022d44 0x6407205e6000ff33 0x9901c81798003fcc

def z346 : W := mkw 0x136eb800009b1800 0x04dbae000026c600 0xd7fff800001f1c01 0xf5fffe000007c700

def z347 : W := mkw 0x009007e002b602a8 0x002401f800ad80aa 0x2c0007e007ff03fe 0x0b0001f801ffc0ff

def z348 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbffff0e00000001 0xf6ffffc380000000

def z349 : W := mkw 0x0010024440000000 0x0004009110000000 0x0800075e60000002 0x020001d798000000

def z350 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7ffffffe1cff33 0xff1fffffff873fcc

def z351 : W := mkw 0x0248000000000000 0x0092000000000000 0xd3f8000000000000 0xf4fe000000000000

def z352 : W := mkw 0x1bffffffd7fbfbc3 0x06fffffff5fefef0 0xffffffffffffffc3 0xfffffffffffffff0

def z353 : W := mkw 0x037eb26450000000 0x00dfac9914000000 0xd3fff86078000001 0xf4fffe181e000000

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0xc807071e00000003 0x3201c1c780000000

def z355 : W := mkw 0x0032224440000000 0x000c889110000000 0x9877070e00000000 0x261dc1c380000000

def z356 : W := mkw 0x03feb7e002b602a8 0x00ffadf800ad80aa 0xffffffe007ff03ff 0xfffffff801ffc0ff

def z357 : W := mkw 0x02fa36ed50000000 0x00be8dbb54000000 0x18783ffff8000002 0x861e0ffffe000000

def z358 : W := mkw 0x80904ff0ab256ffe 0xa02413fc2ac95bff 0x6c08fff1f903ffff 0xdb023ffc7e40ffff

def z359 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x93ffd80007ff0000 0x64fff60001ffc000

def z360 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff0074006fc0332 0xbffc01d001bf00cc

def z361 : W := mkw 0x0985859b8660a3c3 0x02616166e19828f0 0x8b87079f86e003c2 0x22e1c1e7e1b800f0

def z362 : W := mkw 0x1104d80001414800 0x0441360000505200 0x0000d80000000000 0x0000360000000000

def z363 : W := mkw 0x0984c589836042c3 0x0261316260d810b0 0xeb80c78187e003c2 0x7ae031e061f800f0

def z364 : W := mkw 0x02d806e000000000 0x00b601b800000000 0xfff807e0010303fe 0xfffe01f80040c0ff

def z365 : W := mkw 0x0000000020000410 0x8000000008000104 0x0400204060001c30 0x810008101800070c

def z366 : W := mkw 0x177fb34646de9220 0x45dfecd191b7a488 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z367 : W := mkw 0x0000480001014800 0x0000120000405200 0x240000000103fc00 0x090000000040ff00

def z368 : W := mkw 0x0000000d50000000 0x0000000354000000 0x0000001ff8000000 0x00000007fe000000

def z369 : W := mkw 0x03feb7ed52200280 0x00ffadfb548800a0 0xfbffffffffe003c3 0xfefffffffff800f0

def z370 : W := mkw 0x926a7810a99b7d56 0xa49a9e042a66df55 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z371 : W := mkw 0x134c900000d20000 0x04d3240000348000 0x0380000000e00000 0x00e0000000380000

def z372 : W := mkw 0x02d806e000000000 0x00b601b800000000 0x9bf0070000000000 0x26fc01c000000000

def z373 : W := mkw 0x827a7a74f9016d56 0xa09e9e9d3e405b55 0x7478f8f1f903ffff 0xdd1e3e3c7e40ffff

def z374 : W := mkw 0x177ffa4465dfdc30 0xc5dffe911977f70c 0xf7fff84067fffc31 0xfdfffe1019ffff0c

def z375 : W := mkw 0x001103520604a320 0x000440d4818128c8 0xfc77075e061ce333 0xbf1dc1d7818738cc

def z376 : W := mkw 0x80236810ad09fd56 0xa008da042b427f55 0xf47ff8f1ff1fffff 0xfd1ffe3c7fc7ffff

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400004000000332 0x99000010000000cc

def z378 : W := mkw 0x036fb00004089000 0x00dbec0001022400 0xf7fff800061cfc01 0xfdfffe0001873f00

def z379 : W := mkw 0x8000480089014846 0x2000120022405211 0x4008f8f1f90300cf 0xd0023e3c7e40c033

def z380 : W := mkw 0x8000481089016946 0x2000120422405a51 0x6008d8b19903e3cf 0x5802362c6640f8f3

def z381 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbf7275e60000003 0xb6fdc9d798000000

def z382 : W := mkw 0x84332356ee0cb776 0xe10cc8d5bb832ddd 0xfc7727fffe1cffff 0xbf1dc9ffff873fff

def z383 : W := mkw 0x82d84ef0a9016d56 0xa0b613bc2a405b55 0xfff8fff1f903ffff 0xfffe3ffc7e40ffff

def z384 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x4008f8f1f800fc03 0xd0023e3c7e003f00

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0xe380000007e00000 0x78e0000001f80000

def z386 : W := mkw 0x13ccdca911d34800 0x04f3372a4474d200 0x0388d8a199e30000 0x40e236286678c000

def z387 : W := mkw 0x1248180000930800 0x049206000024c200 0x0008180000030000 0x000206000000c000

def z388 : W := mkw 0x0000400081004042 0x0000100020401010 0x0000c081810000c0 0x4000302060400030

def z389 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xef8fc7ff87e3e3ff 0xfbe3f1ffe1f8f8ff

def z390 : W := mkw 0x0000001020002510 0x8000000408000944 0x240000000000ff30 0x0900000000003fcc

def z391 : W := mkw 0x027a326450000000 0x009e8c9914000000 0x5078f8f1f8000003 0xd41e3e3c7e000000

def z392 : W := mkw 0x1001490007ffdaa8 0x0400524001fff6aa 0x2400000007fffffc 0x0900000001ffffff

def z393 : W := mkw 0x809006fdf8002556 0xa02401bf7e000955 0x080007fff80003fe 0x020001fffe0000ff

def z394 : W := mkw 0x13febeed509b1800 0x04ffafbb5426c600 0xdffffffff81f1c03 0xf7fffffffe07c700

def z395 : W := mkw 0x067b2376669eb738 0xc19ec8dd99a7adce 0xfc7f277e661fff3f 0xbf1fc9df9987ffcf

def z396 : W := mkw 0x0001000004089000 0x0000400001022400 0x24000000061cfc00 0x0900000001873f00

def z397 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0408f871f803fc3d 0x81023e1c7e00ff0f

def z398 : W := mkw 0x04332356460cb320 0x410cc8d591832cc8 0xf877071e061ce303 0x3e1dc1c7818738c0

def z399 : W := mkw 0x82d807f0aab627fe 0xa0b601fc2aad89ff 0xfff807f1ffff03fe 0xfffe01fc7fffc0ff

def z400 : W := mkw 0x0010026000040028 0x000400980001000a 0x000000600000003c 0x000000180000000f

def z401 : W := mkw 0x04b327ff760cb730 0xc12cc9ffdd832dcc 0xfc7727fffe1cff33 0xbf1dc9ffff873fcc

def z402 : W := mkw 0x06d807f662b627b8 0xc1b601fd98ad89ee 0xfff807fe67ff03fe 0xfffe01ff99ffc0ff

def z403 : W := mkw 0x13fffee005dbd800 0x04ffffb80176f600 0xffffffe007fffc03 0xfffffff801ffff00

def z404 : W := mkw 0x136ef80001d34800 0x04dbbe000074d200 0xd3fff80001e30001 0xf4fffe000078c000

def z405 : W := mkw 0x03dc87e902b602a8 0x00f721fa40ad80aa 0xffffc7ff87ff03ff 0xfffff1ffe1ffc0ff

def z406 : W := mkw 0x8000000088000046 0x2000000022000011 0x000000a1980000cc 0x0000002866000033

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x24000000010303fc 0x090000000040c0ff

def z408 : W := mkw 0x0c014112a76cf7f3 0xc3005044a9db3dfc 0x2400000007fcfff0 0x0900000001ff3ffc

def z409 : W := mkw 0x03fefeed51014800 0x00ffbfbb54405200 0xfffffffff903fc03 0xfffffffffe40ff00

def z410 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x240000f1f903fffe 0x0900003c7e40ffff

def z411 : W := mkw 0x0000480001014800 0x0000120000405200 0x6408f8f1f903fc03 0xd9023e3c7e40ff00

def z412 : W := mkw 0x0010034002040220 0x000400d000810088 0xfc7807e0071f03fe 0xff1e01f801c7c0ff

def z413 : W := mkw 0x02d847f083b663ea 0x00b611fc20ed98fa 0xfff8c7f187ffe3ff 0xfffe31fc61fff8ff

def z414 : W := mkw 0x02fa26e440000000 0x00be89b910000000 0xdbff27fe60000003 0xf6ffc9ff98000000

def z415 : W := mkw 0x836ef810a9016d56 0xa0dbbe042a405b55 0xf7fff8f1f903ffff 0xfdfffe3c7e40ffff

def z416 : W := mkw 0x07ffb7ef560c9220 0x41ffedfbd5832488 0x9bf7070e061c0000 0x26fdc1c381870000

def z417 : W := mkw 0x8000480089014846 0x2000120022405211 0x6408d8e1990303fe 0xd90236386640c0ff

def z418 : W := mkw 0x84104b56eb056f76 0xe10412d5bac15bdd 0x6c08fffff903ffff 0xdb023ffffe40ffff

def z419 : W := mkw 0x0010034002040220 0x000400d000810088 0x98700700061c0000 0x261c01c001870000

def z420 : W := mkw 0x000101122600a710 0x80004044898029c4 0xec07275e6600ff33 0xbb01c9d799803fcc

def z421 : W := mkw 0x080141128760e3c3 0x02005044a1d838f0 0x6000c09187e0e3c3 0x5800302461f838f0

def z422 : W := mkw 0x934cd810a9d36d56 0xa4d336042a74db55 0x6788f8f1f9e3ffff 0xd9e23e3c7e78ffff

def z423 : W := mkw 0x8905c81bad41ed57 0xa2417206eb507b55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z424 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x6000f891f900ffc3 0x58003e247e403ff0

def z425 : W := mkw 0x0000401081006142 0x0000100420401850 0x0000c0118000e001 0x0000300460003800

def z426 : W := mkw 0x1b6ff91287fbfbc3 0x06dbfe44a1fefef0 0xf7fff80007ffffc1 0xfdfffe0001fffff0

def z427 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x9bf007e006fc03fe 0x26fc01f801bf00ff

def z428 : W := mkw 0x1249480005dbd800 0x049252000176f600 0xf7f8000007fffc00 0xfdfe000001ffff00

def z429 : W := mkw 0x176ff91227dfff30 0xc5dbfe4489f7ffcc 0xf7fff80007ffff31 0xfdfffe0001ffffcc

def z430 : W := mkw 0x0ad947f287f6e3eb 0x02b651fca1fdb8fa 0xfff807e007ffe3fe 0xfffe01f801fff8ff

def z431 : W := mkw 0x93fffff0affffffe 0xa4fffffc2bffffff 0xfffffff1ffffffff 0xfffffffc7fffffff

def z432 : W := mkw 0x0248010002b602a8 0x0092004000ad80aa 0xf7f8000007ff03fc 0xfdfe000001ffc0ff

def z433 : W := mkw 0x0905c01b8540e143 0x02417006e1503850 0x6007c09f8100e3c3 0x5801f027e04038f0

def z434 : W := mkw 0x0000001020002510 0x8000000408000944 0x6408f8f1f800ff33 0xd9023e3c7e003fcc

def z435 : W := mkw 0x02d807f022b627b8 0x80b601fc08ad89ee 0xfff827f067ffffff 0xfffe09fc19ffffff

def z436 : W := mkw 0x936ff8002ddbdc14 0xa4dbfe000b76f705 0xf7fff8607ffffc3d 0xfdfffe181fffff0f

def z437 : W := mkw 0x0080048000200080 0x0020012000080020 0x0380008001e000c0 0x40e0002000780030

def z438 : W := mkw 0x04332256640cb530 0xc10cc89599032d4c 0x1477205e601cfc31 0x851dc81798073f0c

def z439 : W := mkw 0x04336356e70cf772 0xc10cd8d5b9c33ddc 0xfc77e7dfe71cfff3 0xff1df9f7f9c73ffc

def z440 : W := mkw 0x04110352260cb730 0xc10440d489832dcc 0xfc700740061cff32 0xbf1c01d001873fcc

def z441 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x640800e00103fffe 0xd90200380040ffff

def z442 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e0000003fe 0x00000038000000ff

def z443 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x0807275e6000ff33 0x0201c9d798003fcc

def z444 : W := mkw 0x000141128700e342 0x00005044a1c038d0 0xe807c79f8700e3c3 0x7a01f1e7e1c038f0

def z445 : W := mkw 0x82c84cb0a9b36dde 0xa0b2132c2a6cdb77 0x6788f8f1f9e3ffff 0xd9e23e3c7e78ffff

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x6408f8f1f90303ff 0xd9023e3c7e40c0ff

def z447 : W := mkw 0x0905c11b8740e343 0x02417046e1d038d0 0xe807c71f8600e303 0x3a01f1c7e18038c0

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000c09180000003 0x5000302460000000

def z449 : W := mkw 0x0985c58b0760c281 0x02617162c1d830a0 0xeb87c70e07e0e001 0x7ae1f1c381f83800

def z450 : W := mkw 0x100148000549d800 0x0400520001527600 0x000000000000fc00 0x0000000000003f00

def z451 : W := mkw 0x03feb7ed52b602a8 0x00ffadfb54ad80aa 0xdbfffffffefc0003 0xf6ffffffffbf0000

def z452 : W := mkw 0x80326a54e9016d56 0xa00c9a953a405b55 0xfc7ffffff903ffff 0xff1ffffffe40ffff

def z453 : W := mkw 0x036ef80001014800 0x00dbbe0000405200 0xf7fff8000103fc01 0xfdfffe000040ff00

def z454 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x147ff800001ffc01 0x851ffe000007ff00

def z455 : W := mkw 0x1127f8000549d800 0x0449fe0001527600 0x640ff8000103fc01 0xd903fe000040ff00

def z456 : W := mkw 0x0db7a7cf466c92a1 0x436de9f3d19b24a8 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z457 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x0b8807e001e303fe 0x42e201f80078c0ff

def z458 : W := mkw 0x82d84fe08bb74aee 0x20b613f822edd2bb 0xfff8dfe19fff03fe 0xfffe37f867ffc0ff

def z459 : W := mkw 0x136ff00005dad000 0x04dbfc000176b400 0xf3f7c00007fce001 0x7cfdf00001ff3800

def z460 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x9877271e661cfc01 0x261dc9c799873f00

def z461 : W := mkw 0x0905c1128760e3c3 0x02417044a1d838f0 0xe387c00007e0e3c1 0x78e1f00001f838f0

def z462 : W := mkw 0x13ffb7e006fe92a8 0x04ffedf801bfa4aa 0xffff07e007ff03fe 0xffffc1f801ffc0ff

def z463 : W := mkw 0x04232112260cb730 0xc108c84489832dcc 0xf4772000061cff31 0xbd1dc80001873fcc

def z464 : W := mkw 0x80000010a8002556 0xa00000042a000955 0x4008f8f1f80003ff 0xd0023e3c7e0000ff

def z465 : W := mkw 0x0880058b02200281 0x02200162c08800a0 0x0800070e00000000 0x020001c380000000

def z466 : W := mkw 0x8985c59baf60e7d7 0xa2617166ebd839f5 0xeb87c7ffffe0e3ff 0x7ae1f1fffff838ff

def z467 : W := mkw 0x1fffffdfe7fffff3 0xc7fffff7f9fffffc 0xffffffdfe7fffff3 0xfffffff7f9fffffc

def z468 : W := mkw 0x0905c11b8760e3c3 0x02417046e1d838f0 0x2007c01f87e0e3c1 0x0801f007e1f838f0

def z469 : W := mkw 0x008105920620a380 0x00204164818828e0 0xeb87079e07e0e3c3 0x7ae1c1e781f838f0

def z470 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x6408f8000103fffd 0xd9023e000040ffff

def z471 : W := mkw 0x0bffb7ef56608281 0x02ffedfbd59820a0 0xdbfffffffee00003 0xf6ffffffffb80000

def z472 : W := mkw 0x1beff59b87faf3c3 0x06fbfd66e1febcf0 0xfbf7c79f87fce3c3 0x7efdf1e7e1ff38f0

def z473 : W := mkw 0x0032234442040220 0x000c88d110810088 0xfc77275e661c0333 0xbf1dc9d7998700cc

def z474 : W := mkw 0x936ff810addbfd56 0xa4dbfe042b76ff55 0xf7fff80007fffffd 0xfdfffe0001ffffff

def z475 : W := mkw 0x84326a54e90d7d76 0xe10c9a953a435f5d 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z476 : W := mkw 0x1beffd8b07fbda81 0x06fbff62c1fef6a0 0xffffff0e07fffc01 0xffffffc381ffff00

def z477 : W := mkw 0x137ffa6005dfd828 0x04dffe980177f60a 0xf7fff86007fffc3d 0xfdfffe1801ffff0f

def z478 : W := mkw 0x03feb6fd70002510 0x80ffadbf5c000944 0xfffffffff800ff33 0xfffffffffe003fcc

def z479 : W := mkw 0x0248002000920008 0x0092000800248002 0x000800200003000c 0x000200080000c003

def z480 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x34702040661cff30 0x8d1c081019873fcc

def z481 : W := mkw 0x02fa37e452b602a8 0x00be8df914ad80aa 0xfff83fe07fff03fe 0xfffe0ff81fffc0ff

def z482 : W := mkw 0x04b327d6662cb7b0 0xc12cc9f5998b2dec 0xfff727de67fcfff3 0xfffdc9f799ff3ffc

def z483 : W := mkw 0x0801411287f6e3eb 0x02005044a1fdb8fa 0x2400000007ffe3fc 0x0900000001fff8ff

def z484 : W := mkw 0x1801491287fbfbc3 0x06005244a1fefef0 0x2400000007ffffc0 0x0900000001fffff0

def z485 : W := mkw 0x0000010002000200 0x0000004000800080 0xe800070006000302 0x3a0001c0018000c0

def z486 : W := mkw 0x02c804a000000000 0x00b2012800000000 0x038800a000000000 0x40e2002800000000

def z487 : W := mkw 0x080140128540e143 0x02005004a1503850 0x000000000000e000 0x0000000000003800

def z488 : W := mkw 0x03dc86e900000000 0x00f721ba40000000 0xdbffc7ff80000003 0xf6fff1ffe0000000

def z489 : W := mkw 0x02d807ed52b602a8 0x00b601fb54ad80aa 0xfff807ffffff03fe 0xfffe01ffffffc0ff

def z490 : W := mkw 0x009007e0022402a8 0x002401f8008900aa 0x0800070000000000 0x020001c000000000

def z491 : W := mkw 0x06fb27f666beb7b8 0xc1bec9fd99afadee 0xfff7275e66fcff33 0xbffdc9d799bf3fcc

def z492 : W := mkw 0x067b3376760cb730 0xc19eccdd9d832dcc 0xfc7f3f7e7e1cff33 0xbf1fcfdf9f873fcc

def z493 : W := mkw 0x000140000540c000 0x0000500001503000 0x2000000007e0e000 0x0800000001f83800

def z494 : W := mkw 0x0000401081006142 0x0000100420401850 0x200000000100e3c0 0x08000000004038f0

def z495 : W := mkw 0x09a7e59b8768f3c3 0x0269f966e1da3cf0 0xfff7e79f87fcffc3 0xfffdf9e7e1ff3ff0

def z496 : W := mkw 0x1b6ff81b85dbf943 0x06dbfe06e176fe50 0xf7fff81f87fffc01 0xfdfffe07e1ffff00

def z497 : W := mkw 0x12d94fe007ffdaa8 0x04b653f801fff6aa 0xfff807e007fffffe 0xfffe01f801ffffff

def z498 : W := mkw 0x977ffb56efdfff76 0xe5dffed5bbf7ffdd 0xffffffffffffffff 0xffffffffffffffff

def z499 : W := mkw 0x80004910abb76ffe 0xa00012442aeddbff 0x2400000007fffffc 0x0900000001ffffff

def z500 : W := mkw 0x0184848900000000 0x0061212240000000 0x0380c08180000000 0x40e0302060000000

def z501 : W := mkw 0x02d84fe003b74aa8 0x00b613f800edd2aa 0xfff8ffe007ffffff 0xfffe3ff801ffffff

def z502 : W := mkw 0x82584a70a9976d7e 0xa096129c2a65db5f 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z503 : W := mkw 0x0105c1120740e300 0x0041704481d038c0 0xeb87c71e07e0e303 0x7ae1f1c781f838c0

def z504 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfbf0078007fc03c2 0x7efc01e001ff00f0

def z505 : W := mkw 0x03eeb4ad50000000 0x00fbad2b54000000 0x038ff8bff8000001 0x40e3fe2ffe000000

def z506 : W := mkw 0x07feb6ed700c1430 0xc1ffadbb5c03050c 0xdffffffff81c1c33 0xf7fffffffe07070c

def z507 : W := mkw 0x8000081028012d14 0xa00002040a004b45 0x640838707803ff3f 0x99020e1c1e00ffcf

def z508 : W := mkw 0x0ad807fb82b623eb 0x02b601fee0ad88fa 0xfff807ff87ff03fe 0xfffe01ffe1ffc0ff

def z509 : W := mkw 0x0bccc4a981f240cb 0x02f3312a607c9032 0x0388c0a181e300cc 0x40e230286078c033

def z510 : W := mkw 0x126b780005dbd800 0x049ade000176f600 0x3478380007fffc00 0x8d1e0e0001ffff00

def z511 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0xd877275e661c0003 0xb61dc9d799870000

def z512 : W := mkw 0x17ffffff77dfff30 0xc5ffffffddf7ffcc 0xffffffffffffff33 0xffffffffffffffcc

def z513 : W := mkw 0x827a3a6478010c14 0xa09e8e991e004305 0x1478386078031c3c 0x851e0e181e00c70f

def z514 : W := mkw 0x136ff91207dbfb00 0x04dbfe4481f6fec0 0xffffff1e07ffff03 0xffffffc781ffffc0

def z515 : W := mkw 0x9beffd9baffbffd7 0xa6fbff66ebfefff5 0xffffffffffffffff 0xffffffffffffffff

def z516 : W := mkw 0x8126f81df9016d56 0xa049be077e405b55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z517 : W := mkw 0x04322244400c1020 0x410c889110030408 0x10700000001c0000 0x041c000000070000

def z518 : W := mkw 0x8bffffffff61efd7 0xa2ffffffffd87bf5 0xffffffffffe3ffff 0xfffffffffff8ffff

def z519 : W := mkw 0x0bfef6edd16040c3 0x02ffbdbb74581030 0xdbfffffff9e000c3 0xf6fffffffe780030

def z520 : W := mkw 0x8000480089014846 0x2000120022405211 0x0000d80198000000 0x0000360066000000

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000080010003c2 0x58000020004000f0

def z522 : W := mkw 0x1023680005dbd800 0x0408da000176f600 0xf477200007fffc01 0xbd1dc80001ffff00

def z523 : W := mkw 0x027a326450000000 0x009e8c9914000000 0xd87f3f7e78000003 0xb61fcfdf9e000000

def z524 : W := mkw 0x03eeb4a910000000 0x00fbad2a44000000 0xd3fff8a198000001 0xf4fffe2866000000

def z525 : W := mkw 0x86fb6ff6efbffffe 0xe1bedbfdbbefffff 0xffffffffffffffff 0xffffffffffffffff

def z526 : W := mkw 0x8000080028010c14 0xa00002000a004305 0x0400000000031c3c 0x010000000000c70f

def z527 : W := mkw 0x009006ed50000000 0x002401bb54000000 0x0800070e00000000 0x020001c380000000

def z528 : W := mkw 0x042320166408b510 0xc108c80599022d44 0xf477201e661cfc01 0xbd1dc80799873f00

def z529 : W := mkw 0x0432235662042730 0xc10c88d5988109cc 0xd877275e60000333 0xb61dc9d7980000cc

def z530 : W := mkw 0x0da7e59fe768f7d3 0xc369f967f9da3df4 0xeb87e79fe7e0ffc3 0x7ae1f9e7f9f83ff0

def z531 : W := mkw 0x0258026000000000 0x0096009800000000 0x1078006000000000 0x841e001800000000

def z532 : W := mkw 0x03cc94a910b20088 0x00f3252a442c8022 0x0388d8a199e300cc 0x40e236286678c033

def z533 : W := mkw 0x0905c01b8540e143 0x02417006e1503850 0xe387c01f87e0e001 0x78e1f007e1f83800

def z534 : W := mkw 0x0032224440000000 0x000c889110000000 0x1070204060000000 0x841c081018000000

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000205060000003 0x9000081418000000

def z536 : W := mkw 0x0000011202002300 0x00000044808008c0 0x0800071e00000302 0x020001c7800000c0

def z537 : W := mkw 0x0410034642040220 0x410400d190810088 0x0800070e00000000 0x020001c380000000

def z538 : W := mkw 0x8000000028000414 0xa00000000a000105 0x000000607800003c 0x000000181e00000f

def z539 : W := mkw 0x04322344620c1630 0xc10c88d11883058c 0xfc702740661c1f32 0xbf1c09d0198707cc

def z540 : W := mkw 0x8000480089014846 0x2000120022405211 0x00000000010300cc 0x000000000040c033

def z541 : W := mkw 0x0126b00000000000 0x0049ac0000000000 0x0007f80000000001 0x0001fe0000000000

def z542 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0008f8b1f903fccd 0x40023e2c7e40ff33

def z543 : W := mkw 0x0022200000000000 0x0008880000000000 0xd077200000000001 0xb41dc80000000000

def z544 : W := mkw 0x0080048900000000 0x0020012240000000 0x0800079f80000002 0x020001e7e0000000

def z545 : W := mkw 0x0033224444089000 0x000cc89111022400 0xfc77275e661cfc03 0xbf1dc9d799873f00

def z546 : W := mkw 0x0080058002200280 0x00200160008800a0 0x08000780000003c2 0x020001e0000000f0

def z547 : W := mkw 0x1127f8000549d800 0x0449fe0001527600 0xe387f80007e0fc01 0x78e1fe0001f83f00

def z548 : W := mkw 0x02d806e000b20088 0x00b601b8002c8022 0xdbf807e001e300ce 0xf6fe01f80078c033

def z549 : W := mkw 0x0000401081006142 0x0000100420401850 0x6008f8f1f900e3c3 0xd8023e3c7e4038f0

def z550 : W := mkw 0x08000112822023c3 0x02000044a08808f0 0x00000000000003c0 0x00000000000000f0

def z551 : W := mkw 0x02d806e000920000 0x00b601b800248000 0xfff807e007ff0002 0xfffe01f801ffc000

def z552 : W := mkw 0x037eb24440000000 0x00dfac9110000000 0xdbffff5e60000003 0xf6ffffd798000000

def z553 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x000000000000fc00 0x0000000000003f00

def z554 : W := mkw 0x0000001020002510 0x8000000408000944 0x000020106000fc01 0x0000080418003f00

def z555 : W := mkw 0x8984cc99a9616dd7 0xa26133266a585b75 0x6788f8f1f9e3ffff 0xd9e23e3c7e78ffff

def z556 : W := mkw 0x136ff81085dbf942 0x04dbfe042176fe50 0xf7fff89187ffffc3 0xfdfffe2461fffff0

def z557 : W := mkw 0x0248000000920000 0x0092000000248000 0x14780000001f0000 0x851e00000007c000

def z558 : W := mkw 0x0104c00001404000 0x0041300000501000 0x0380c00001e00000 0x40e0300000780000

def z559 : W := mkw 0x0080058002200280 0x00200160008800a0 0xef8807e007e303fe 0xfbe201f801f8c0ff

def z560 : W := mkw 0x03dc97e912b602a8 0x00f725fa44ad80aa 0xfff8dfe19fff03fe 0xfffe37f867ffc0ff

def z561 : W := mkw 0x1beffc8985fbd8c3 0x06fbff22617ef630 0xf7fff88187fffcc1 0xfdfffe2061ffff30

def z562 : W := mkw 0x0423200644089000 0x4108c80191022400 0x0007000e00000000 0x0001c00380000000

def z563 : W := mkw 0x126a3800009b1800 0x049a8e000026c600 0xf7f8380007ff1c00 0xfdfe0e0001ffc700

def z564 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xcb87c79f86e00003 0x72e1f1e7e1b80000

def z565 : W := mkw 0x0010034002040220 0x000400d000810088 0x0800074000000332 0x020001d0000000cc

def z566 : W := mkw 0x13ffb7e006fe92a8 0x04ffedf801bfa4aa 0x9bf7070006fc0000 0x26fdc1c001bf0000

def z567 : W := mkw 0x0185859b0600a300 0x00616166c18028c0 0xeb87c79f8600e303 0x7ae1f1e7e18038c0

def z568 : W := mkw 0x040100122408b510 0xc100400489022d44 0x000000000000fc00 0x0000000000003f00

def z569 : W := mkw 0x0d37e35fe74cf773 0xc34df8d7f9d33ddc 0xfc77e75fe61cff33 0xbf1df9d7f9873fcc

def z570 : W := mkw 0x05b7a7df660cb730 0xc16de9f7d9832dcc 0xfff7e7dfe61cff33 0xfffdf9f7f9873fcc

def z571 : W := mkw 0x1001000004da9000 0x040040000136a400 0x0000000006fc0000 0x0000000001bf0000

def z572 : W := mkw 0x002320102408b510 0x8008c80409022d44 0xf4772050661cff33 0xbd1dc81419873fcc

def z573 : W := mkw 0x02fa36e450000000 0x00be8db914000000 0xdbf83fe078000002 0xf6fe0ff81e000000

def z574 : W := mkw 0x1bfffffb87fffbeb 0x06fffffee1fffefa 0xffffffff87ffffff 0xffffffffe1ffffff

def z575 : W := mkw 0x09b7e7dfc760e3c3 0x026df9f7f1d838f0 0xfbf7e7dfe7e0e3c3 0xfefdf9f7f9f838f0

def z576 : W := mkw 0x0d27e01fe548f553 0xc349f807f9523d54 0x0007e01fe000fc01 0x0001f807f8003f00

def z577 : W := mkw 0x009006ed50000000 0x002401bb54000000 0x4808fffff8000003 0xd2023ffffe000000

def z578 : W := mkw 0x13effd8007fbda80 0x04fbff6001fef6a0 0xffffff8007ffffc3 0xffffffe001fffff0

def z579 : W := mkw 0x034c900000000000 0x00d3240000000000 0x0388d80000000000 0x40e2360000000000

def z580 : W := mkw 0x027a326450000000 0x009e8c9914000000 0x1070000000000000 0x041c000000000000

def z581 : W := mkw 0x0000401081006142 0x0000100420401850 0x6408c0f18103e3ff 0xd902303c6040f8ff

def z582 : W := mkw 0x83fefffdfbb76ffe 0xa0ffbfff7eeddbff 0xffffffffffffffff 0xffffffffffffffff

def z583 : W := mkw 0x84336b56ef0dff76 0xe10cdad5bbc37fdd 0xfc77ff5ffe1cff33 0xbf1dffd7ff873fcc

def z584 : W := mkw 0x80004800a9014c56 0xa00012002a405315 0x0408f8e1f9031cfc 0xc1023e387e40c73f

def z585 : W := mkw 0x90014810addbfd56 0xa40052042b76ff55 0x2400000007fffffc 0x0900000001ffffff

def z586 : W := mkw 0x1022380000091800 0x04088e0000024600 0x0000380000001c00 0x00000e0000000700

def z587 : W := mkw 0x089007ffd22023c3 0x022401fff48808f0 0x080007fff80003c2 0x020001fffe0000f0

def z588 : W := mkw 0x0880459b832063c3 0x02201166e0c818f0 0x6800c79f8100e3c3 0x5a0031e7e04038f0

def z589 : W := mkw 0x0000000000b20088 0x00000000002c8022 0x0000000001e300cc 0x000000000078c033

def z590 : W := mkw 0x0000000000920000 0x0000000000248000 0x2400000007ff0000 0x0900000001ffc000

def z591 : W := mkw 0x1985cd9b87fbfbc3 0x06617366e1fefef0 0xef87c79f87ffffc3 0x7be1f1e7e1fffff0

def z592 : W := mkw 0x02c804a000b20088 0x00b20128002c8022 0xf7f800a007ff00cc 0xfdfe002801ffc033

def z593 : W := mkw 0x037eb26d50000000 0x00dfac9b54000000 0x107ff87ff8000001 0x841ffe1ffe000000

def z594 : W := mkw 0x83ccdca999014846 0x20f3372a66405211 0x0388d8a1990300cc 0x40e236286640c033

def z595 : W := mkw 0x0985c4898560c0c3 0x0261712261583030 0xe387c08187e0e0c1 0x78e1f02061f83830

def z596 : W := mkw 0x13ffb6ed54da9000 0x04ffedbb5536a400 0xdbfffffffefc0003 0xf6ffffffffbf0000

def z597 : W := mkw 0x003323564600a300 0x000cc8d5918028c0 0xf877275e6600e303 0xbe1dc9d7998038c0

def z598 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x2400f811f903fffd 0x09003e047e40ffff

def z599 : W := mkw 0x88804d9bab216fd7 0xa2201366eac85bf5 0x6c08fffff903ffff 0xdb023ffffe40ffff

def z600 : W := mkw 0x0126b00d50000000 0x0049ac0354000000 0x0007000e00000000 0x0001c00380000000

def z601 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0xfc77074e061c0332 0xbf1dc1d3818700cc

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008f80000000001 0xd0023e0000000000

def z603 : W := mkw 0x13fffeed55dbd800 0x04ffffbb5576f600 0xffffff0e07fffc01 0xffffffc381ffff00

def z604 : W := mkw 0x0080048000000000 0x0020012000000000 0xcb80078000000002 0x72e001e000000000

def z605 : W := mkw 0x936ff810addbfd56 0xa4dbfe042b76ff55 0xf7fff811fffffc01 0xfdfffe047fffff00

def z606 : W := mkw 0x13effca915dbd800 0x04fbff2a4576f600 0xf7fff8a19ffffc01 0xfdfffe2867ffff00

def z607 : W := mkw 0x03feb7ed522402a8 0x00ffadfb548900aa 0xdbfffffff80003ff 0xf6fffffffe0000ff

def z608 : W := mkw 0x04010112260cb730 0xc100404489832dcc 0x64002050661cff33 0x9900081419873fcc

def z609 : W := mkw 0x04b327f6662cb7b8 0xc12cc9fd998b2dee 0xfc7727fe661cffff 0xbf1dc9ff99873fff

def z610 : W := mkw 0x08004000816040c3 0x0200100020581030 0x0000000001e000c0 0x0000000000780030

def z611 : W := mkw 0x009007e0022402a8 0x002401f8008900aa 0xfc7007e0061c03fe 0xbf1c01f8018700ff

def z612 : W := mkw 0x0fffe7ffe7fef7fb 0xc3fff9fff9ffbdfe 0xffffe7ffe7ffffff 0xfffff9fff9ffffff

def z613 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0xd3fff80006fc0001 0xf4fffe0001bf0000

def z614 : W := mkw 0x0800001b80002143 0x02000006e0000850 0x0000001f80000000 0x00000007e0000000

def z615 : W := mkw 0x0010026450000000 0x0004009914000000 0x0000006078000000 0x000000181e000000

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008386078000000 0x80020e181e000000

def z617 : W := mkw 0x0bdd87eb06f682a9 0x02f761fac1bda0aa 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z618 : W := mkw 0x0080058002b602a8 0x0020016000ad80aa 0xef80078007ff03fe 0x7be001e001ffc0ff

def z619 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x13f8f8e1f8000000 0xc4fe3e387e000000

def z620 : W := mkw 0x83fefeedd9014846 0x20ffbfbb76405211 0xdbfffffff90300cf 0xf6fffffffe40c033

def z621 : W := mkw 0x03feb7ed52b602a8 0x00ffadfb54ad80aa 0xffff07ee07ff03fe 0xffffc1fb81ffc0ff

def z622 : W := mkw 0x03ffb6ed54089000 0x00ffedbb55022400 0xfffffffffe1cfc03 0xffffffffff873f00

def z623 : W := mkw 0x03ddc7e007f6c2a8 0x00f771f801fdb0aa 0xffffc7e007ffe3ff 0xfffff1f801fff8ff

def z624 : W := mkw 0x06d907f226beb7b8 0xc1b641fc89afadee 0xfff807e007fffffe 0xfffe01f801ffffff

def z625 : W := mkw 0x036ff0000540c000 0x00dbfc0001503000 0xf3fff80007e0e001 0xfcfffe0001f83800

def z626 : W := mkw 0x12fa3fe002bf1aa8 0x04be8ff800afc6aa 0xfff83fe007ff1ffe 0xfffe0ff801ffc7ff

def z627 : W := mkw 0x9127f810ad49fd56 0xa449fe042b527f55 0x640ff8f1f903ffff 0xd903fe3c7e40ffff

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000f1f8000002 0x0000003c7e000000

def z629 : W := mkw 0x03dc96ed50000000 0x00f725bb54000000 0x0b88dffff8000002 0x42e237fffe000000

def z630 : W := mkw 0x089007fb822423eb 0x022401fee08908fa 0x080007ff800003fe 0x020001ffe00000ff

def z631 : W := mkw 0x09a7f59fd760e3c3 0x0269fd67f5d838f0 0xeb87ff9fffe0e3c3 0x7ae1ffe7fff838f0

def z632 : W := mkw 0x80804d90ab216fd6 0xa02013642ac85bf5 0xef88fff1ffe3ffff 0xfbe23ffc7ff8ffff

def z633 : W := mkw 0x04000000200c1430 0xc10000000803050c 0x04000000001c1c30 0x010000000007070c

def z634 : W := mkw 0x009007e0022402a8 0x002401f8008900aa 0x6c0807e0010303fe 0xdb0201f80040c0ff

def z635 : W := mkw 0x03dc96e910000000 0x00f725ba44000000 0xdbf8dfe198000002 0xf6fe37f866000000

def z636 : W := mkw 0x82580a6028970c3c 0xa09602980a25c30f 0x14783860781f1c3c 0x851e0e181e07c70f

def z637 : W := mkw 0x13effc8905dbd800 0x04fbff224176f600 0xffffff9f87fffc03 0xffffffe7e1ffff00

def z638 : W := mkw 0x04332244640c9430 0xc10cc8911903250c 0xf4772040661cfc31 0xbd1dc81019873f0c

def z639 : W := mkw 0x0010024000000000 0x0004009000000000 0xd870074000000002 0xb61c01d000000000

def z640 : W := mkw 0x136ff90007ffdaa8 0x04dbfe4001fff6aa 0xf7fff80007fffffd 0xfdfffe0001ffffff

def z641 : W := mkw 0x0126b00d50000000 0x0049ac0354000000 0x400ff8fff8000003 0xd003fe3ffe000000

def z642 : W := mkw 0x1401491227dfff30 0xc500524489f7ffcc 0x2400000007ffff30 0x0900000001ffffcc

def z643 : W := mkw 0x0995c7fb8764e3eb 0x026571fee1d938fa 0xeb87c7ff87e0e3ff 0x7ae1f1ffe1f838ff

def z644 : W := mkw 0x0000481081016942 0x0000120420405a50 0x6408f8918103ffc3 0xd9023e246040fff0

def z645 : W := mkw 0x0022300450000000 0x00088c0114000000 0x0000380078000000 0x00000e001e000000

def z646 : W := mkw 0x0422200460081410 0xc108880118020504 0x0000200060001c00 0x0000080018000700

def z647 : W := mkw 0x0248102010000000 0x0092040804000000 0x0008182018000000 0x0002060806000000

def z648 : W := mkw 0x03ffb7ff5600a300 0x00ffedffd58028c0 0xfbfffffffe00e303 0xfeffffffff8038c0

def z649 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x0807c79f8000e3c3 0x0201f1e7e00038f0

def z650 : W := mkw 0x077fb356660cb730 0xc1dfecd599832dcc 0xffffff5e661cff33 0xffffffd799873fcc

def z651 : W := mkw 0x93fffefdfddbfd56 0xa4ffffbf7f76ff55 0xffffffffffffffff 0xffffffffffffffff

def z652 : W := mkw 0x136ff8000549d800 0x04dbfe0001527600 0xd3fff8000000fc01 0xf4fffe0000003f00

def z653 : W := mkw 0x177ffb4647dfda20 0x45dffed191f7f688 0xffffff0e07fffc01 0xffffffc381ffff00

def z654 : W := mkw 0x0537e356674cf730 0xc14df8d599d33dcc 0xfff7e75e67fcff33 0xfffdf9d799ff3fcc

def z655 : W := mkw 0x0104900910000000 0x0041240244000000 0x0000d80198000000 0x0000360066000000

def z656 : W := mkw 0x02c805a002b602a8 0x00b2016800ad80aa 0x278800a007ff03fc 0x49e2002801ffc0ff

def z657 : W := mkw 0x0527b01f7408b510 0xc149ec07dd022d44 0x0007f81ff800fc01 0x0001fe07fe003f00

def z658 : W := mkw 0x0984c59b836063c3 0x02613166e0d818f0 0x0b80c79f81e003c2 0x42e031e7e07800f0

def z659 : W := mkw 0x13fefeed51d34800 0x04ffbfbb5474d200 0xdbfffffff9e30003 0xf6fffffffe78c000

def z660 : W := mkw 0x0248000000920000 0x0092000000248000 0x93f0000006fc0000 0x24fc000001bf0000

def z661 : W := mkw 0x127a3a60009f1828 0x049e8e980027c60a 0x14783860001f1c3c 0x851e0e180007c70f

def z662 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0xf7ff000007ff0000 0xfdffc00001ffc000

def z663 : W := mkw 0x00b226ed50000000 0x002c89bb54000000 0xd87727fff8000003 0xb61dc9fffe000000

def z664 : W := mkw 0x926a3800289b1c14 0xa49a8e000a26c705 0x14783860781f1c3c 0x851e0e181e07c70f

def z665 : W := mkw 0x009007c0022402a0 0x002401f0008900a8 0xfff007c007fc03f2 0xfffc01f001ff00fc

def z666 : W := mkw 0x08800489802000c3 0x0220012260080030 0x00000081800000c0 0x0000002060000030

def z667 : W := mkw 0x0cb327dfe62cb7f3 0xc32cc9f7f98b2dfc 0xfc7727dfe61cfff3 0xbf1dc9f7f9873ffc

def z668 : W := mkw 0x04332346660c9630 0xc10cc8d19983258c 0x9c77274e661c1c30 0xa71dc9d39987070c

def z669 : W := mkw 0x0bcdc5bb87f2e3cb 0x02f3716ee1fcb8f2 0xeb8fc7bf87e3e3cf 0x7ae3f1efe1f8f8f3

def z670 : W := mkw 0x0400011222042730 0xc1000044888109cc 0x0000000000000330 0x00000000000000cc

def z671 : W := mkw 0x02d907f206b6a3a8 0x00b641fc81ada8ea 0xffff07fe07ffe3ff 0xffffc1ff81fff8ff

def z672 : W := mkw 0x136ff81025dbfd10 0x84dbfe040976ff44 0xf7fff85067ffff33 0xfdfffe1419ffffcc

def z673 : W := mkw 0x0401011226beb7b8 0xc100404489afadee 0x2400000007fffffc 0x0900000001ffffff

def z674 : W := mkw 0x83febeed78010c14 0xa0ffafbb5e004305 0xdffffffff8031c3f 0xf7fffffffe00c70f

def z675 : W := mkw 0x176ff81665dbfd10 0xc5dbfe059976ff44 0xf7fff81e67fffc01 0xfdfffe0799ffff00

def z676 : W := mkw 0x04010112260cb730 0xc100404489832dcc 0xec07071e061cff33 0x3b01c1c781873fcc

def z677 : W := mkw 0x1927f81b8549f943 0x0649fe06e1527e50 0x0007f81f8000fc01 0x0001fe07e0003f00

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4700000061c0000 0xbd1c000001870000

def z679 : W := mkw 0x80104b50ab056f76 0xa00412d42ac15bdd 0xfc78fff1ff1fffff 0xff1e3ffc7fc7ffff

def z680 : W := mkw 0x8000080028010c14 0xa00002000a004305 0x640838e079031ffe 0xd9020e381e40c7ff

def z681 : W := mkw 0x14336b5667dfff30 0xc50cdad599f7ffcc 0xfc77275e67ffff33 0xbf1dc9d799ffffcc

def z682 : W := mkw 0x0db7e7dfc76cf3e3 0x436df9f7f1db3cf8 0xfbf7c79f87fce3c3 0x7efdf1e7e1ff38f0

def z683 : W := mkw 0x0000001020002510 0x8000000408000944 0x640820f06103ffff 0xd902083c1840ffff

def z684 : W := mkw 0x0023200004089000 0x0008c80001022400 0x000720000000fc01 0x0001c80000003f00

def z685 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0000f8f1f800ffff 0x00003e3c7e003fff

def z686 : W := mkw 0x03cc94a910000000 0x00f3252a44000000 0xcb8fdfbf98000003 0x72e3f7efe6000000

def z687 : W := mkw 0x042321166608b710 0xc108c84599822dc4 0xe807271e6600ff03 0x3a01c9c799803fc0

def z688 : W := mkw 0x1127b00004489000 0x0449ec0001122400 0x0007000000000000 0x0001c00000000000

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008d8a198000000 0x4002362866000000

def z690 : W := mkw 0x88014912af61efd7 0xa2005244abd87bf5 0x6408f8f1ffe3ffff 0xd9023e3c7ff8ffff

def z691 : W := mkw 0x0995c7ffd760e3c3 0x026571fff5d838f0 0xeb87c7ffffe0e3c3 0x7ae1f1fffff838f0

def z692 : W := mkw 0x0248000000920000 0x0092000000248000 0x0388000001e30000 0x40e200000078c000

def z693 : W := mkw 0x0bccd4a9916040c3 0x02f3352a64581030 0x0388d8a199e000c0 0x40e2362866780030

def z694 : W := mkw 0x83ccdcb9b9016d56 0xa0f3372e6e405b55 0x6788f8f1f903ffff 0xd9e23e3c7e40ffff

def z695 : W := mkw 0x0433235666beb7b8 0xc10cc8d599afadee 0xfc77275e67ffffff 0xbf1dc9d799ffffff

def z696 : W := mkw 0x8000480089014846 0x2000120022405211 0x6408f8a19903fccd 0xd9023e286640ff33

def z697 : W := mkw 0x80000810a8012d56 0xa00002042a004b55 0x040838f1f8031ffe 0x81020e3c7e00c7ff

def z698 : W := mkw 0x0258036002b602a8 0x009600d800ad80aa 0x3478006007ff03fc 0x8d1e001801ffc0ff

def z699 : W := mkw 0x07ffb7ff760cb730 0xc1ffedffdd832dcc 0xfff7275e661cff33 0xbffdc9d799873fcc

def z700 : W := mkw 0x0001000004008000 0x0000400001002000 0xe00700000600e001 0x3801c00001803800

def z701 : W := mkw 0x0258036002960228 0x009600d800a5808a 0xfc780760061f033e 0xbf1e01d80187c0cf

def z702 : W := mkw 0x126b3800049b9800 0x049ace000126e600 0xf47f3800061ffc01 0xbd1fce000187ff00

def z703 : W := mkw 0x1527f8166549fd10 0xc549fe0599527f44 0x0007f81e6000fc01 0x0001fe0798003f00

def z704 : W := mkw 0x0000001080002142 0x0000000420000850 0x00000091800003c2 0x00000024600000f0

def z705 : W := mkw 0x07ffb7ef560c9220 0x41ffedfbd5832488 0xdbfffffffe1c0003 0xf6ffffffff870000

def z706 : W := mkw 0x84236816ed09fd56 0xe108da05bb427f55 0x640ff8fff903ffff 0xd903fe3ffe40ffff

def z707 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef87ff9fffe3ffff 0x7be1ffe7fff8ffff

def z708 : W := mkw 0x088145928760e3c3 0x02205164a1d838f0 0xeb87079e07e0e3c3 0x7ae1c1e781f838f0

def z709 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xf877271e661cff03 0x3e1dc9c799873fc0

def z710 : W := mkw 0x82d84ff0abb76ffe 0xa0b613fc2aeddbff 0x9bf0ff11fefcfc01 0x26fc3fc47fbf3f00

def z711 : W := mkw 0x0248010002b602a8 0x0092004000ad80aa 0xb7f0000007ff03fc 0x2dfc000001ffc0ff

def z712 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7fffffff1fffff 0xff1fffffffc7ffff

def z713 : W := mkw 0x0985c58b8760c2c3 0x02617162e1d830b0 0xeb87c78f87e003c2 0x7ae1f1e3e1f800f0

def z714 : W := mkw 0x01a6b48d50000000 0x0069ad2354000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z715 : W := mkw 0x134dd80005dbd800 0x04d376000176f600 0xf7f8d80007fffc00 0xfdfe360001ffff00

def z716 : W := mkw 0x136ff80915dbd800 0x04dbfe024576f600 0xf7fff8019ffffc01 0xfdfffe0067ffff00

def z717 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0xfc77274e061cff33 0xbf1dc9d381873fcc

def z718 : W := mkw 0x0984848900600081 0x0261212240180020 0xcb87c79f80e00003 0x72e1f1e7e0380000

def z719 : W := mkw 0x07feb6ed500c1020 0x41ffadbb54030408 0xdbfffffff81c0003 0xf6fffffffe070000

def z720 : W := mkw 0x126a7800019b5800 0x049a9e000066d600 0xf7f8f80007fffc01 0xfdfe3e0001ffff00

def z721 : W := mkw 0x0023210206089200 0x0008c84081822480 0xfc77270e061cfc01 0xbf1dc9c381873f00

def z722 : W := mkw 0x936fb010acdab556 0xa4dbec042b36ad55 0x93f700f1fefc03fe 0x24fdc03c7fbf00ff

def z723 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbfffffff90300cf 0xf6fffffffe40c033

def z724 : W := mkw 0x82480010a8922556 0xa09200042a248955 0xf7f800f1ffff03fe 0xfdfe003c7fffc0ff

def z725 : W := mkw 0x175cdb5663d76f30 0xc5d736d598f5dbcc 0x0b88df5e61e30332 0x42e237d79878c0cc

def z726 : W := mkw 0x0b5dc27b85d6e16b 0x02d7709ee175b85a 0x147fc07f801fe03d 0x851ff01fe007f80f

def z727 : W := mkw 0x10914eed55dbd800 0x042453bb5576f600 0x2c0007fffffffc02 0x0b0001ffffffff00

def z728 : W := mkw 0x80014912af01ef56 0xa0005244abc07bd5 0x240000000703fffc 0x0900000001c0ffff

def z729 : W := mkw 0x0136b24d50000000 0x004dac9354000000 0x9877ff1ff8000001 0x261dffc7fe000000

def z730 : W := mkw 0x1249480005dbd800 0x049252000176f600 0xb7f0000007fffc00 0x2dfc000001ffff00

def z731 : W := mkw 0x0985c59ba760e7d3 0x82617166e9d839f4 0xef87c79f87e0fff3 0x7be1f1e7e1f83ffc

def z732 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xb7ff380007fffc00 0xadffce0001ffff00

def z733 : W := mkw 0x0985cd9b8761ebc3 0x02617366e1d87af0 0xef87c79f87e3ffc3 0x7be1f1e7e1f8fff0

def z734 : W := mkw 0x127a3a64509b1800 0x049e8e991426c600 0x14783800001f1c00 0x851e0e000007c700

def z735 : W := mkw 0x889007fbaa2427ff 0xa22401feea8909ff 0x080007fff80003fe 0x020001fffe0000ff

def z736 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xfff7c79f87fce3c3 0xfffdf1e7e1ff38f0

def z737 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfff7275e67fcff33 0xfffdc9d799ff3fcc

def z738 : W := mkw 0x1bccdca991f348c3 0x06f3372a647cd230 0x0388d8a199e300c0 0x40e236286678c030

def z739 : W := mkw 0x02c804a000b20088 0x00b20128002c8022 0xf7f800e007ff03fe 0xfdfe003801ffc0ff

def z740 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87071e07e0e3c3 0x3ae1c1c781f838f0

def z741 : W := mkw 0x0a7b7376d760e3c3 0x029edcddb5d838f0 0x307838607fe0e3c0 0x8c1e0e181ff838f0

def z742 : W := mkw 0x027a326450920000 0x009e8c9914248000 0x14783860781f0000 0x851e0e181e07c000

def z743 : W := mkw 0x01b6b6ed50000000 0x006dadbb54000000 0x480ffffff8000003 0xd203fffffe000000

def z744 : W := mkw 0x04332356e60cb772 0xc10cc8d5b9832ddc 0xfc7727dfe61cfff3 0xbf1dc9f7f9873ffc

def z745 : W := mkw 0x8bcccca989f348cf 0x22f3332a627cd233 0x0388d8a199e300cc 0x40e236286678c033

def z746 : W := mkw 0x867a6a74e99f7d7e 0xe19e9a9d3a67df5f 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z747 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb8fc7bf87e3e3cf 0x7ae3f1efe1f8f8f3

def z748 : W := mkw 0x003322546408b510 0x800cc89519022d44 0xfc77275e661cff33 0xbf1dc9d799873fcc

def z749 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0xfc77275e661cfc03 0xbf1dc9d799873f00

def z750 : W := mkw 0x03feb6ed50920000 0x00ffadbb54248000 0xffffffffffff03ff 0xffffffffffffc0ff

def z751 : W := mkw 0x027a326450920008 0x009e8c9914248002 0x107838607803000c 0x841e0e181e00c003

def z752 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xab87070e07e003c0 0x2ae1c1c381f800f0

def z753 : W := mkw 0x1b6ff80985dbd843 0x06dbfe026176f610 0xf7fff80187fffc01 0xfdfffe0061ffff00

def z754 : W := mkw 0x0248000000920000 0x0092000000248000 0xf7f8000007ff03fc 0xfdfe000001ffc0ff

def z755 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x93f7000006fcfc00 0x24fdc00001bf3f00

def z756 : W := mkw 0x03eeb48d50000000 0x00fbad2354000000 0xdbffff9ff8000003 0xf6ffffe7fe000000

def z757 : W := mkw 0x8105c912af41ef56 0xa0417244abd07bd5 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z758 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77ff5ffe1cff33 0xbf1dffd7ff873fcc

def z759 : W := mkw 0x0985c59ba760e7d3 0x82617166e9d839f4 0xeb87e79fe7e0ffc3 0x7ae1f9e7f9f83ff0

def z760 : W := mkw 0x036ff0000548d000 0x00dbfc0001523400 0xf7fff80007fcfc01 0xfdfffe0001ff3f00

def z761 : W := mkw 0x84336b46cf0dda66 0x610cdad1b3c37699 0x987fdfaf9f1f00cc 0x661ff7ebe7c7c033

def z762 : W := mkw 0x002321122608b710 0x8008c84489822dc4 0xfc77275e661cff33 0xbf1dc9d799873fcc

def z763 : W := mkw 0x13ccdca911d34800 0x04f3372a4474d200 0x0388d80001e30000 0x40e236000078c000

def z764 : W := mkw 0x01b6b6ed50000000 0x006dadbb54000000 0xd877fffff8000003 0xb61dfffffe000000

def z765 : W := mkw 0x88014912aff7efff 0xa2005244abfdfbff 0x2400000007fffffc 0x0900000001ffffff

def z766 : W := mkw 0x0d85c59b876cf3e3 0x43617166e1db3cf8 0xeb87c79f87fce3c3 0x7ae1f1e7e1ff38f0

def z767 : W := mkw 0x9127f81dfd49fd56 0xa449fe077f527f55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z768 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87c70e07e0e3c1 0x7ae1f1c381f838f0

def z769 : W := mkw 0x043322566408b510 0xc10cc89599022d44 0xfc77275e661cfc03 0xbf1dc9d799873f00

def z770 : W := mkw 0x00332344460c9220 0x000cc8d111832488 0xfc77275e661cff33 0xbf1dc9d799873fcc

def z771 : W := mkw 0x027a326450960028 0x009e8c991425800a 0x10783860781c0000 0x841e0e181e070000

def z772 : W := mkw 0x0127e8000549d800 0x0049fa0001527600 0xf7fff80007fffc01 0xfdfffe0001ffff00

def z773 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdffffffff803003f 0xf7fffffffe00c00f

def z774 : W := mkw 0x03feb6ed50960028 0x00ffadbb5425800a 0xdbfffffff81c0003 0xf6fffffffe070000

def z775 : W := mkw 0x01b6a6cd40000000 0x006da9b350000000 0xdbfffffff8000003 0xf6fffffffe000000

def z776 : W := mkw 0x9bccdc8989f348c7 0x26f33722627cd231 0x0388d8a199e300cc 0x40e236286678c033

def z777 : W := mkw 0x84332356ee0cb776 0xe10cc8d5bb832ddd 0xfc77275ffe1cff33 0xbf1dc9d7ff873fcc

def z778 : W := mkw 0x83fefefdf9016d56 0xa0ffbfbf7e405b55 0xbff7070e0103fffc 0x2ffdc1c38040ffff

def z779 : W := mkw 0x967a7a54e99f7d76 0xe59e9e953a67df5d 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z780 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7f27fe661cff33 0xff1fc9ff99873fcc

def z781 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xeb87070e06e00302 0x3ae1c1c381b800c0

def z782 : W := mkw 0x001103522604a730 0x800440d4898129cc 0xfc77275e661cff33 0xbf1dc9d799873fcc

def z783 : W := mkw 0x07cd95bb360cb730 0xc1f3656ecd832dcc 0x2788d8a19e1cff30 0x49e2362867873fcc

def z784 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0x8b87079f86e00002 0x22e1c1e7e1b80000

def z785 : W := mkw 0x0185c4890540c000 0x0061712241503000 0xeb87c70e07e0e001 0x7ae1f1c381f83800

def z786 : W := mkw 0x03cc94a910000000 0x00f3252a44000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z787 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef8fdfbf9fe3ffff 0x7be3f7efe7f8ffff

def z788 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xb7f7f80007fffc01 0x2dfdfe0001ffff00

def z789 : W := mkw 0x0032224440000000 0x000c889110000000 0xd877ff5ff8000003 0xb61dffd7fe000000

def z790 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xeb8fdfffffe3e3ff 0x7ae3f7fffff8f8ff

def z791 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xcb87c79f86e0e003 0x72e1f1e7e1b83800

def z792 : W := mkw 0x843323566e0cb734 0xe10cc8d59b832dcd 0xfc77277e7e1cff3f 0xbf1dc9df9f873fcf

def z793 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77275e671fffff 0xbf1dc9d799c7ffff

def z794 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff811fffffc01 0xfdfffe047fffff00

def z795 : W := mkw 0x127a3264509a1000 0x049e8c9914268400 0x10783860781c0000 0x841e0e181e070000

def z796 : W := mkw 0x936ff8008ddbd846 0x24dbfe002376f611 0xf7fff8019ffffc01 0xfdfffe0067ffff00

def z797 : W := mkw 0x136ff80d55dbd800 0x04dbfe035576f600 0xf7fff8fffffffc03 0xfdfffe3fffffff00

def z798 : W := mkw 0x0184848900000000 0x0061212240000000 0xcb87ff9ff8000003 0x72e1ffe7fe000000

def z799 : W := mkw 0x167a3a64709f1c30 0xc59e8e991c27c70c 0x14783860781f1c30 0x851e0e181e07c70c

def z800 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfffffffffe1c0003 0xffffffffff870000

def z801 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0x8b87c78f86e00000 0x62e1f1e3e1b80000

def z802 : W := mkw 0x06eb24b664bab598 0xc1bac92d992ead66 0x038f20be61e3fccd 0x40e3c82f9878ff33

def z803 : W := mkw 0x0136b24d50000000 0x004dac9354000000 0xd87ffffff8000003 0xf61ffffffe000000

def z804 : W := mkw 0x01b6b6ed50000000 0x006dadbb54000000 0xcb87fffff8000003 0x72e1fffffe000000

def z805 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xbc77271e661cff31 0x2f1dc9c799873fcc

def z806 : W := mkw 0x80814d92af21efd6 0xa0205364abc87bf5 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z807 : W := mkw 0x11b7ffe0076ddaa8 0x046dfff801db76aa 0x0807ffe00000ffff 0x0201fff800003fff

def z808 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbf7ff5ff8000003 0xb6fdffd7fe000000

def z809 : W := mkw 0x936ff8000ddbd804 0x24dbfe000376f601 0xf7fff8201ffffc0d 0xfdfffe0807ffff03

def z810 : W := mkw 0x9927f81bad49fd57 0xa649fe06eb527f55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z811 : W := mkw 0x0881059b8620a3c3 0x02204166e18828f0 0xeb87079f87e0e3c3 0x7ae1c1e7e1f838f0

def z812 : W := mkw 0x042321166608b710 0xc108c84599822dc4 0xfc77271e661cff03 0xbf1dc9c799873fc0

def z813 : W := mkw 0x84332356ee0cb776 0xe10cc8d5bb832ddd 0xfc77275e661cffff 0xbf1dc9d799873fff

def z814 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7f3f7e7e1cff33 0xbf1fcfdf9f873fcc

def z815 : W := mkw 0x0985c59ba760e7d3 0x82617166e9d839f4 0xef8fffffffe0fff3 0xfbe3fffffff83ffc

def z816 : W := mkw 0x01a6b48d50000000 0x0069ad2354000000 0x0807ff9ff8000003 0x0201ffe7fe000000

def z817 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x0b8ffffff8000003 0x42e3fffffe000000

def z818 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xbff8076007ff03fc 0xaffe01d801ffc0ff

def z819 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0xbc77070e061cfc00 0x2f1dc1c381873f00

def z820 : W := mkw 0x03dc96ed50000000 0x00f725bb54000000 0xcb8fdffff8000003 0x72e3f7fffe000000

def z821 : W := mkw 0x0985859b0660a381 0x02616166c19828e0 0x8b87071e06e0e001 0x22e1c1c781b83800

def z822 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77071e061cff33 0x3f1dc1c781873fcc

def z823 : W := mkw 0x067a2274609e3538 0xc19e889d18278d4e 0x747820f0611fffff 0xdd1e083c1847ffff

def z824 : W := mkw 0x0c9007df622427b1 0xc32401f7d88909ec 0x0800075e60000332 0x020001d7980000cc

def z825 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbfffffff80003ff 0xf6fffffffe0000ff

def z826 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xb7ffd80007fffc00 0x6dfff60001ffff00

def z827 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x9bf807e007ff03fe 0x66fe01f801ffc0ff

def z828 : W := mkw 0x126b680005dbd800 0x049ada000176f600 0xf7ff200007fffc01 0xfdffc80001ffff00

def z829 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87c71f87e0e001 0x7ae1f1c7e1f83800

def z830 : W := mkw 0x027a326450000000 0x009e8c9914000000 0xd87ffffff8000003 0xf61ffffffe000000

def z831 : W := mkw 0x0985859b0660a381 0x02616166c19828e0 0xeb87079e07e0e3c3 0x7ae1c1e781f838f0

def z832 : W := mkw 0x936ff8008ddbd846 0x24dbfe002376f611 0xf7fff80007fffccd 0xfdfffe0001ffff33

def z833 : W := mkw 0x0258026000960028 0x009600980025800a 0xf7f800e007ff03fe 0xfdfe003801ffc0ff

def z834 : W := mkw 0x0c332356666cb7b1 0xc30cc8d5999b2dec 0xfc77275e66fcff33 0xbf1dc9d799bf3fcc

def z835 : W := mkw 0x04332346660c9630 0xc10cc8d19983258c 0xfc77274e661cfc31 0xbf1dc9d399873f0c

def z836 : W := mkw 0x0bfeb6ed50600081 0x02ffadbb54180020 0xdbfffffff8e00003 0xf6fffffffe380000

def z837 : W := mkw 0x1b6ff80b05dbd801 0x06dbfe02c176f600 0xf7fff80e07fffc01 0xfdfffe0381ffff00

def z838 : W := mkw 0x000101120600a300 0x00004044818028c0 0xeb87071e07e0e303 0x7ae1c1c781f838c0

def z839 : W := mkw 0x0985859b8660a3c3 0x02616166e19828f0 0xcb87c79f86e003c3 0x72e1f1e7e1b800f0

def z840 : W := mkw 0x89858d8b2e618e95 0xa2616362cb9863a5 0x8f8f3f6e7ee31c3c 0xa3e3cfdb9fb8c70f

def z841 : W := mkw 0x8d85cd9baf6dfff7 0xe3617366ebdb7ffd 0xef87c79f87ffffff 0x7be1f1e7e1ffffff

def z842 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff0074007ff03fe 0xbffc01d001ffc0ff

def z843 : W := mkw 0x008145928720e3c2 0x00205164a1c838f0 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z844 : W := mkw 0x0984848900600081 0x0261212240180020 0x8b87070e00e00000 0x22e1c1c380380000

def z845 : W := mkw 0x06d807e642b602a8 0x41b601f990ad80aa 0xfff807ee07ff03fe 0xfffe01fb81ffc0ff

def z846 : W := mkw 0x83ccdca999b348ce 0x20f3372a666cd233 0x0388d8a199e300cc 0x40e236286678c033

def z847 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0008f8f1f903ffff 0x40023e3c7e40ffff

def z848 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xef8f07ee07e303fe 0xfbe3c1fb81f8c0ff

def z849 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0x37f800e007ff03fc 0xcdfe003801ffc0ff

def z850 : W := mkw 0x8184cd99ab216fd6 0xa06133666ac85bf5 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z851 : W := mkw 0x0984c59b836063c3 0x02613166e0d818f0 0xcb87c79f81e003c3 0x72e1f1e7e07800f0

def z852 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x8b87c79f87e003c2 0x62e1f1e7e1f800f0

def z853 : W := mkw 0x04322254600c3530 0xc10c889518030d4c 0xfc77275e601cff33 0xbf1dc9d798073fcc

def z854 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xef8fc79f87e3e3c3 0xfbe3f1e7e1f8f8f0

def z855 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef87c7ffffe3ffff 0x7be1f1fffff8ffff

def z856 : W := mkw 0x037eb26d50000000 0x00dfac9b54000000 0xd87fff7ff8000003 0xb61fffdffe000000

def z857 : W := mkw 0x0985858b866082c3 0x02616162e19820b0 0x8b87078f86e000c0 0x22e1c1e3e1b80030

def z858 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xef8fffffffe3e3ff 0xfbe3fffffff8f8ff

def z859 : W := mkw 0x0105c0000540c000 0x0041700001503000 0xeb87c71e07e0e003 0x7ae1f1c781f83800

def z860 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77074e061cff32 0xbf1dc1d381873fcc

def z861 : W := mkw 0x03feb6ed50920008 0x00ffadbb54248002 0xdbfffffff803000f 0xf6fffffffe00c003

def z862 : W := mkw 0x034dc80005d3c800 0x00d372000174f200 0xf7fff80007fffc01 0xfdfffe0001ffff00

def z863 : W := mkw 0x0d85c59ba768f7d3 0xc3617166e9da3df4 0xeb87c79f87e0ffc3 0x7ae1f1e7e1f83ff0

def z864 : W := mkw 0x0985c58b8760c2c3 0x02617162e1d830b0 0xcb87c79f87e000c3 0x72e1f1e7e1f80030

def z865 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bffdffff8000002 0x66fff7fffe000000

def z866 : W := mkw 0x01b6b6cd50000000 0x006dadb354000000 0xdbf7ffdff8000003 0xf6fdfff7fe000000

def z867 : W := mkw 0x0248480001934800 0x009212000064d200 0xf7f8000007fffc00 0xfdfe000001ffff00

def z868 : W := mkw 0x0985c59b8764e3eb 0x02617166e1d938fa 0xeb87c79f87e0e3ff 0x7ae1f1e7e1f838ff

def z869 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff88007ffffc3 0xfdfffe2001fffff0

def z870 : W := mkw 0x0184848900000000 0x0061212240000000 0xeb87c79f87e00003 0x7ae1f1e7e1f80000

def z871 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef8fff9fffe3ffc3 0xfbe3ffe7fff8fff0

def z872 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff8ffe007ff03ff 0xfffe3ff801ffc0ff

def z873 : W := mkw 0x019486ed50000000 0x006521bb54000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z874 : W := mkw 0x827a7a74f9976d7e 0xa09e9e9d3e65db5f 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z875 : W := mkw 0x0258034002b602a8 0x009600d000ad80aa 0xfff8074007ff03fe 0xfffe01d001ffc0ff

def z876 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff89187fffc03 0xfdfffe2461ffff00

def z877 : W := mkw 0x8c014912af6dfff7 0xe3005244abdb7ffd 0x2400000007fffffc 0x0900000001ffffff

def z878 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0x93f7200006fcfc01 0x24fdc80001bf3f00

def z879 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7f7200007fffc01 0xbdfdc80001ffff00

def z880 : W := mkw 0x03feb6ed50920000 0x00ffadbb54248000 0xdffffffff81f0003 0xf7fffffffe07c000

def z881 : W := mkw 0x0185c59b0740e300 0x00617166c1d038c0 0xeb87c79f87e0e303 0x7ae1f1e7e1f838c0

def z882 : W := mkw 0x0080058002200280 0x00200160008800a0 0xeb87079e07e003c3 0x7ae1c1e781f800f0

def z883 : W := mkw 0x003323564608b300 0x000cc8d591822cc0 0xfc77275e661cff03 0xbf1dc9d799873fc0

def z884 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef8fff9f87e3ffff 0xfbe3ffe7e1f8ffff

def z885 : W := mkw 0x03feb6ed50960028 0x00ffadbb5425800a 0xfffffffff91f03ff 0xfffffffffe47c0ff

def z886 : W := mkw 0x0185848904408000 0x0061612241102000 0xcb87c79f86e00003 0x72e1f1e7e1b80000

def z887 : W := mkw 0x067a3264709e1438 0xc19e8c991c27850e 0x14783860781f1c3c 0x851e0e181e07c70f

def z888 : W := mkw 0x134cd80001d34800 0x04d336000074d200 0xf7f8f80007fffc01 0xfdfe3e0001ffff00

def z889 : W := mkw 0x1985cd9b8769fbc3 0x06617366e1da7ef0 0xeb87c79f87e0ffc3 0x7ae1f1e7e1f83ff0

def z890 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7f275e671fff33 0xff1fc9d799c7ffcc

def z891 : W := mkw 0x02d807e912b602a8 0x00b601fa44ad80aa 0xfff807e19fff03fe 0xfffe01f867ffc0ff

def z892 : W := mkw 0x03eeb48900000000 0x00fbad2240000000 0xdbfffffff8000003 0xf6fffffffe000000

def z893 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff84007ffff33 0xfdfffe1001ffffcc

def z894 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x8b87c79f86e0e3c3 0x22e1f1e7e1b838f0

def z895 : W := mkw 0x8d27e81fed49fd57 0xe349fa07fb527f55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z896 : W := mkw 0x176ff80645dbd800 0x45dbfe019176f600 0xf7fff80e07fffc01 0xfdfffe0381ffff00

def z897 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfbffffffffe00003 0xfefffffffff80000

def z898 : W := mkw 0x0000001020002510 0x8000000408000944 0x6408f8f1f903ffff 0xd9023e3c7e40ffff

def z899 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7727de671cfff3 0xff1dc9f799c73ffc

def z900 : W := mkw 0x0985cd9b8761ebc3 0x02617366e1d87af0 0xeb87ff9f87e0ffc3 0x7ae1ffe7e1f83ff0

def z901 : W := mkw 0x0984c499816061c3 0x0261312660581870 0xeb87c79f81e0e3c3 0x7ae1f1e7e07838f0

def z902 : W := mkw 0x067a2264409e1028 0x419e88991027840a 0x14780060001f003c 0x851e00180007c00f

def z903 : W := mkw 0x13feb6ed509a1000 0x04ffadbb54268400 0xdbfffffff81c0003 0xf6fffffffe070000

def z904 : W := mkw 0x049007d6622427b0 0xc12401f5988909ec 0x080007de600003f2 0x020001f7980000fc

def z905 : W := mkw 0x0032235462042730 0x800c88d5188109cc 0xfc77275e661cff33 0xbf1dc9d799873fcc

def z906 : W := mkw 0x0c9007ffe22427fb 0xc32401fff88909fe 0x080007ffe00003fe 0x020001fff80000ff

def z907 : W := mkw 0x8985cd9b8f61ebc7 0x22617366e3d87af1 0xef8fffbf9fe3ffcf 0xfbe3ffefe7f8fff3

def z908 : W := mkw 0x0984859b822023c3 0x02612166e08808f0 0xeb87c79f87e003c3 0x7ae1f1e7e1f800f0

def z909 : W := mkw 0x88014912af61efd7 0xa2005244abd87bf5 0x2000000007e0ffc0 0x0800000001f83ff0

def z910 : W := mkw 0x8984cc89896148c7 0x2261332262585231 0xcb8ffffff9e300cf 0xf2e3fffffe78c033

def z911 : W := mkw 0x0985c49b8540e143 0x02617126e1503850 0xeb87c79f87e0e003 0x7ae1f1e7e1f83800

def z912 : W := mkw 0x067a2264609e1438 0xc19e88991827850e 0x14702040601c1c30 0x851c08101807070c

def z913 : W := mkw 0x84014912af0dff76 0xe1005244abc37fdd 0x24000000061cff30 0x0900000001873fcc

def z914 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xcb87071e06e00003 0x32e1c1c781b80000

def z915 : W := mkw 0x0184858902200280 0x00612162408800a0 0x8b87070e06e00000 0x22e1c1c381b80000

def z916 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xef87c79f87e3e3ff 0x7be1f1e7e1f8f8ff

def z917 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xeb87ffffffe0ffff 0x7ae1fffffff83fff

def z918 : W := mkw 0x127a7a64519b5800 0x049e9e991466d600 0x7478f8f1f91ffc03 0xdd1e3e3c7e47ff00

def z919 : W := mkw 0x0985c59b8768f3c3 0x02617166e1da3cf0 0xef87c79f87fcffc3 0x7be1f1e7e1ff3ff0

def z920 : W := mkw 0x0985c4898560c0c3 0x0261712261583030 0xeb87c79f87e0e0c3 0x7ae1f1e7e1f83830

def z921 : W := mkw 0x0248010002b602a8 0x0092004000ad80aa 0xf7f800e007ff03fe 0xfdfe003801ffc0ff

def z922 : W := mkw 0x009007c0022402a0 0x002401f0008900a8 0xfff807e007ff03fe 0xfffe01f801ffc0ff

def z923 : W := mkw 0x0126b10d52b602a8 0x0049ac4354ad80aa 0x2407f81fffff03fd 0x0901fe07ffffc0ff

def z924 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7ff000007fffc00 0xfdffc00001ffff00

def z925 : W := mkw 0x0985c59ba760e7d3 0x82617166e9d839f4 0xef8fe7ffe7e3ffff 0xfbe3f9fff9f8ffff

def z926 : W := mkw 0x037eb24440000000 0x00dfac9110000000 0xdbfffffff8000003 0xf6fffffffe000000

def z927 : W := mkw 0x0185c5920760e380 0x0061716481d838e0 0xeb87c79e07e0e3c3 0x7ae1f1e781f838f0

def z928 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7fff5e661cff33 0xff1fffd799873fcc

def z929 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x8b87070e06e0e000 0x22e1c1c381b83800

def z930 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0xf478f8f1ff1fffff 0xfd1e3e3c7fc7ffff

def z931 : W := mkw 0x927a3a64789b1c14 0xa49e8e991e26c705 0x14783860781f1c3c 0x851e0e181e07c70f

def z932 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xffff07fe07ff03ff 0xffffc1ff81ffc0ff

def z933 : W := mkw 0x93ccdca999d34846 0x24f3372a6674d211 0x0388d8a199e300cc 0x40e236286678c033

def z934 : W := mkw 0x03feb6ed50200088 0x00ffadbb54080022 0xdbfffffff80000cf 0xf6fffffffe000033

def z935 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xcb87c70e06e00001 0x72e1f1c381b80000

def z936 : W := mkw 0x03feb6ed50081000 0x00ffadbb54020400 0xdffffffff81c1c03 0xf7fffffffe070700

def z937 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xab87c71f87e0e3c1 0x2ae1f1c7e1f838f0

def z938 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87078e07e0e3c2 0x7ae1c1e381f838f0

def z939 : W := mkw 0x049007f6622427b8 0xc12401fd988909ee 0x0800075e60000332 0x020001d7980000cc

def z940 : W := mkw 0x167a3244409e1020 0x459e8c9110278408 0x10700000001c0000 0x041c000000070000

def z941 : W := mkw 0x008105922620a790 0x80204164898829e4 0xef8f27fe67e3ffff 0xfbe3c9ff99f8ffff

def z942 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bf7fffff8000003 0x26fdfffffe000000

def z943 : W := mkw 0x0db6e6cde16c54f3 0xc36db9b3785b153c 0x17f0e0c1e1fc1cf0 0xc5fc3830787f073c

def z944 : W := mkw 0x849007f6ea2427fe 0xe12401fdba8909ff 0x080007fff80003fe 0x020001fffe0000ff

def z945 : W := mkw 0x136ff00005dad000 0x04dbfc000176b400 0xf7f7e00007fcfc01 0xfdfdf80001ff3f00

def z946 : W := mkw 0x136ff80d55dbd800 0x04dbfe035576f600 0xf7fff80e07fffc01 0xfdfffe0381ffff00

def z947 : W := mkw 0x04332346460c9220 0x410cc8d191832488 0x9877270e061cfc01 0x261dc9c381873f00

def z948 : W := mkw 0x0985c59ba760e7d3 0x82617166e9d839f4 0xeb87c7dfe7e0e3f3 0x7ae1f1f7f9f838fc

def z949 : W := mkw 0x02d807e442b602a8 0x00b601f910ad80aa 0xfff807fe67ff03fe 0xfffe01ff99ffc0ff

def z950 : W := mkw 0x13ccdca911f34888 0x04f3372a447cd222 0x0388d8a199e300cc 0x40e236286678c033

def z951 : W := mkw 0x0985d59b9760e3c3 0x02617566e5d838f0 0xeb87df9f9fe0e3c3 0x7ae1f7e7e7f838f0

def z952 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87c71f86e0e303 0x3ae1f1c7e1b838c0

def z953 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x37f8f80007fffc00 0xcdfe3e0001ffff00

def z954 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xef87e79f87e0ffc3 0xfbe1f9e7e1f83ff0

def z955 : W := mkw 0x84014912afbffffe 0xe1005244abefffff 0x2400000007fffffc 0x0900000001ffffff

def z956 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8a007fffccd 0xfdfffe2801ffff33

def z957 : W := mkw 0x02d807e902b602a8 0x00b601fa40ad80aa 0xfff807ff87ff03fe 0xfffe01ffe1ffc0ff

def z958 : W := mkw 0x809007f0aa2427fe 0xa02401fc2a8909ff 0x080007e0000003fe 0x020001f8000000ff

def z959 : W := mkw 0x0185859b0620a380 0x00616166c18828e0 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z960 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7f7f80006fcfc01 0xbdfdfe0001bf3f00

def z961 : W := mkw 0x037eb24d50000000 0x00dfac9354000000 0xdbffff5ff8000003 0xf6ffffd7fe000000

def z962 : W := mkw 0x0184c48901404000 0x0061312240501000 0xcb87c79f81e00003 0x72e1f1e7e0780000

def z963 : W := mkw 0x03feb6ed50040028 0x00ffadbb5401000a 0xdbfffffff800003f 0xf6fffffffe00000f

def z964 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0xec0ffffff903ffff 0xfb03fffffe40ffff

def z965 : W := mkw 0x1aea3d9b82bb3bc3 0x06ba8f66e0aecef0 0x1c783f9f801f1fc2 0x871e0fe7e007c7f0

def z966 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7f7c00007fffc01 0x7dfdf00001ffff00

def z967 : W := mkw 0x0985859b8660a3c3 0x02616166e19828f0 0xeb87079f86e0e3c3 0x3ae1c1e7e1b838f0

def z968 : W := mkw 0x0033224444089000 0x000cc89111022400 0xfc77270e061cfc01 0xbf1dc9c381873f00

def z969 : W := mkw 0x167a7a54619f7d30 0xc59e9e951867df4c 0x7478f850611fff33 0xdd1e3e141847ffcc

def z970 : W := mkw 0x01a6b48d50000000 0x0069ad2354000000 0x8b87ff1ff8000001 0x22e1ffc7fe000000

def z971 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x0b87c79f81e0e3c3 0x42e1f1e7e07838f0

def z972 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x97fff80006fffc01 0xa5fffe0001bfff00

def z973 : W := mkw 0x8985c59baf60e7d7 0xa2617166ebd839f5 0xef8fc7ffffe3e3ff 0xfbe3f1fffff8f8ff

def z974 : W := mkw 0x0985cd9ba761efd3 0x82617366e9d87bf4 0xef8fffdfe7e3fff3 0xfbe3fff7f9f8fffc

def z975 : W := mkw 0x04332376660cb738 0xc10cc8dd99832dce 0xfc77277e661cff3f 0xbf1dc9df99873fcf

def z976 : W := mkw 0x0127a00004489000 0x0049e80001122400 0xf7f7200006fcfc01 0xbdfdc80001bf3f00

def z977 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb8fc7ff87e0e3c3 0xfae3f1ffe1f838f0

def z978 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff86007fffc3d 0xfdfffe1801ffff0f

def z979 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xbc77274e661cff30 0xaf1dc9d399873fcc

def z980 : W := mkw 0x127a3a6450930800 0x049e8e991424c200 0x1078386078030000 0x841e0e181e00c000

def z981 : W := mkw 0x027a326450960028 0x009e8c991425800a 0x10700000001c0000 0x041c000000070000

def z982 : W := mkw 0x02490000049a9000 0x009240000126a400 0xf7f8000007fffc00 0xfdfe000001ffff00

def z983 : W := mkw 0x0985859b8660a3c3 0x02616166e19828f0 0x8b87070e06e003c0 0x22e1c1c381b800f0

def z984 : W := mkw 0x0985cd8b0761ca81 0x02617362c1d872a0 0xef8fff0e07e3fc01 0xfbe3ffc381f8ff00

def z985 : W := mkw 0x00332352060cb320 0x000cc8d481832cc8 0xfc77275e061cff33 0xbf1dc9d781873fcc

def z986 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff8dfe19fff03fe 0xfffe37f867ffc0ff

def z987 : W := mkw 0x04332376760cb730 0xc10cc8dd9d832dcc 0xfc77277e7e1cff33 0xbf1dc9df9f873fcc

def z988 : W := mkw 0x010581120640a300 0x00416044819028c0 0xeb87071e06e0e303 0x3ae1c1c781b838c0

def z989 : W := mkw 0x136ff82005dbd808 0x04dbfe080176f602 0xf7fff82007fffc0d 0xfdfffe0801ffff03

def z990 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x1c77275e601cff33 0x871dc9d798073fcc

def z991 : W := mkw 0x0985c58b0760c281 0x02617162c1d830a0 0x8b87c70e06e0e001 0x22e1f1c381b83800

def z992 : W := mkw 0x0184858902200280 0x00612162408800a0 0xeb87078e07e003c2 0x7ae1c1e381f800f0

def z993 : W := mkw 0x0248000000920000 0x0092000000248000 0xf7f8200007fffc01 0xfdfe080001ffff00

def z994 : W := mkw 0x167a3244609e1430 0xc59e8c911827850c 0x14702040601c1c30 0x851c08101807070c

def z995 : W := mkw 0x026b2000049a9000 0x009ac8000126a400 0xf7f7200006fcfc01 0xbdfdc80001bf3f00

def z996 : W := mkw 0x049007f2222427b8 0xc12401fc888909ee 0x080007e0000003fe 0x020001f8000000ff

def z997 : W := mkw 0x827a3a6478970c3c 0xa09e8e991e25c30f 0x14783860781f1c3c 0x851e0e181e07c70f

def z998 : W := mkw 0x04232112260cb730 0xc108c84489832dcc 0xfc77271e061cff33 0xbf1dc9c781873fcc

def z999 : W := mkw 0x036fe00005dad000 0x00dbf8000176b400 0xf7ffe00007fffc01 0xfdfff80001ffff00

def z1000 : W := mkw 0x867a2a64689f1c3c 0xe19e8a991a27c70f 0x14783860781f1c3c 0x851e0e181e07c70f

def z1001 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x187ffffff8000003 0x861ffffffe000000

def z1002 : W := mkw 0x127a3a44409b1800 0x049e8e911026c600 0x14783840601f1c00 0x851e0e101807c700

def z1003 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8a19ffffc01 0xfdfffe2867ffff00

def z1004 : W := mkw 0x0985c58b0760c281 0x02617162c1d830a0 0xeb87c78e07e0e3c3 0x7ae1f1e381f838f0

def z1005 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x2408f8e1f903fffc 0xc9023e387e40ffff

def z1006 : W := mkw 0x009007c002b602a8 0x002401f000ad80aa 0xfff007c007ff03fe 0xfffc01f001ffc0ff

def z1007 : W := mkw 0x03feb6ed50b20088 0x00ffadbb542c8022 0xfffffffff9e303ff 0xfffffffffe78c0ff

def z1008 : W := mkw 0x126b780005dbd800 0x049ade000176f600 0xf7f8380007fffc00 0xfdfe0e0001ffff00

def z1009 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0xe788f8f1ffe3ffff 0xf9e23e3c7ff8ffff

def z1010 : W := mkw 0x0985c58b8760c2c3 0x02617162e1d830b0 0x8b87070e07e000c0 0x22e1c1c381f80030

def z1011 : W := mkw 0x0185cc890541c800 0x0061732241507200 0xef8fffffffe3fc03 0xfbe3fffffff8ff00

def z1012 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff83fe07fff03fe 0xfffe0ff81fffc0ff

def z1013 : W := mkw 0x84332356ee0cb776 0xe10cc8d5bb832ddd 0xfc7ffffffe1cffff 0xff1fffffff873fff

def z1014 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb8fdfbf9fe0e3c3 0x7ae3f7efe7f838f0

def z1015 : W := mkw 0x136ff80445dbd800 0x04dbfe011176f600 0xf7fff81e67fffc01 0xfdfffe0799ffff00

def z1016 : W := mkw 0x136ff80085dbd842 0x04dbfe002176f610 0xf7fff88187fffcc1 0xfdfffe2061ffff30

def z1017 : W := mkw 0x0105810206408200 0x0041604081902080 0x8b87070e06e00000 0x22e1c1c381b80000

def z1018 : W := mkw 0x0985c58b8760c2c3 0x02617162e1d830b0 0xeb87c78f87e0e0c1 0x7ae1f1e3e1f83830

def z1019 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff8070007ff03fc 0xfffe01c001ffc0ff

def z1020 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb8fff9f87e0e3c3 0xfae3ffe7e1f838f0

def z1021 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xd877275e661cfc03 0xb61dc9d799873f00

def z1022 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef8fc7ff87e3ffff 0xfbe3f1ffe1f8ffff

def z1023 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbf7ff9ff8000003 0x76fdffe7fe000000

def z1024 : W := mkw 0x02d807e452b602a8 0x00b601f914ad80aa 0xfff807e07fff03fe 0xfffe01f81fffc0ff

def z1025 : W := mkw 0x1127e80005dbd800 0x0449fa000176f600 0xf7f7e00007fffc01 0xfdfdf80001ffff00

def z1026 : W := mkw 0x967a3a44689f1c34 0xe59e8e911a27c70d 0x14783860781f1c3c 0x851e0e181e07c70f

def z1027 : W := mkw 0x1985dd9b8761ebc3 0x06617766e1d87af0 0xeb87df9f87e0e3c3 0x7ae1f7e7e1f838f0

def z1028 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xbff007e007ff03fe 0x2ffc01f801ffc0ff

def z1029 : W := mkw 0x0023200004089000 0x0008c80001022400 0xf7f7200007fcfc01 0xfdfdc80001ff3f00

def z1030 : W := mkw 0x0985c5bb9760e3c3 0x0261716ee5d838f0 0xeb87c7bf9fe0e3c3 0x7ae1f1efe7f838f0

def z1031 : W := mkw 0x0905c1128760e3c3 0x02417044a1d838f0 0xeb87c71e07e0e3c3 0x7ae1f1c781f838f0

def z1032 : W := mkw 0x0985859b0660a381 0x02616166c19828e0 0x8b87071e06e00302 0x22e1c1c781b800c0

def z1033 : W := mkw 0x136ff80905dbd800 0x04dbfe024176f600 0xf7fff81f87fffc01 0xfdfffe07e1ffff00

def z1034 : W := mkw 0x01b6b6ed50000000 0x006dadbb54000000 0x0807ff1ff8000001 0x0201ffc7fe000000

def z1035 : W := mkw 0x809007fdfa2427fe 0xa02401ff7e8909ff 0x080007fff80003fe 0x020001fffe0000ff

def z1036 : W := mkw 0x167a3a64609f1c38 0xc59e8e991827c70e 0x14783860601f1c3c 0x851e0e181807c70f

def z1037 : W := mkw 0x0c9007fff22427f3 0xc32401fffc8909fc 0x080007fff80003f2 0x020001fffe0000fc

def z1038 : W := mkw 0x8985c59baf60e7d7 0xa2617166ebd839f5 0xeb8fffffffe0e3ff 0xfae3fffffff838ff

def z1039 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80ffffff8000003 0xf203fffffe000000

def z1040 : W := mkw 0x0ad807eb02b602a9 0x02b601fac0ad80aa 0xfff807ee07ff03fe 0xfffe01fb81ffc0ff

def z1041 : W := mkw 0x0985859b0660a381 0x02616166c19828e0 0xeb87c79f86e0e303 0x7ae1f1e7e1b838c0

def z1042 : W := mkw 0x0184848900200080 0x0061212240080020 0xcb87c79f81e000c3 0x72e1f1e7e0780030

def z1043 : W := mkw 0x00904fe003254aa8 0x002413f800c952aa 0x6c08ffe00103ffff 0xdb023ff80040ffff

def z1044 : W := mkw 0x8985c59baf60e7d7 0xa2617166ebd839f5 0xeb87c79fffe0e3c3 0x7ae1f1e7fff838f0

def z1045 : W := mkw 0x0985859b8660a3c3 0x02616166e19828f0 0x8b87071f86e00000 0x22e1c1c7e1b80000

def z1046 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87c7ff87e0e3ff 0x7ae1f1ffe1f838ff

def z1047 : W := mkw 0x8985cd9b8f61ebc7 0x22617366e3d87af1 0xeb8fffffffe3e3cf 0xfae3fffffff8f8f3

def z1048 : W := mkw 0x94014912afdfff76 0xe5005244abf7ffdd 0x2400000007fffffc 0x0900000001ffffff

def z1049 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8f1ffffffff 0xfdfffe3c7fffffff

def z1050 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff827e007ffffff 0xfffe09f801ffffff

def z1051 : W := mkw 0x134dc80005dbd800 0x04d372000176f600 0xf7ffc00007fffc01 0xfdfff00001ffff00

def z1052 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0xf7ff200007fffc01 0xfdffc80001ffff00

def z1053 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfffffffff8000333 0xfffffffffe0000cc

def z1054 : W := mkw 0x0985c5bb8760e3cb 0x0261716ee1d838f2 0xeb87c7bf87e0e3cf 0x7ae1f1efe1f838f3

def z1055 : W := mkw 0x8985c59baf60e7d7 0xa2617166ebd839f5 0xeb87c79f87e0e3ff 0x7ae1f1e7e1f838ff

def z1056 : W := mkw 0x0136b24d50000000 0x004dac9354000000 0x0807ff5ff8000003 0x0201ffd7fe000000

def z1057 : W := mkw 0x03dc86e900000000 0x00f721ba40000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1058 : W := mkw 0x0985859b8660a3c3 0x02616166e19828f0 0xeb87079f87e003c2 0x7ae1c1e7e1f800f0

def z1059 : W := mkw 0x02c805a002b602a8 0x00b2016800ad80aa 0xf7f800a007ff03fc 0xfdfe002801ffc0ff

def z1060 : W := mkw 0x8985cd9b8f61ebc7 0x22617366e3d87af1 0xeb87c79f87e3e3cf 0x7ae1f1e7e1f8f8f3

def z1061 : W := mkw 0x02d817e012b602a8 0x00b605f804ad80aa 0xfff81fe01fff03fe 0xfffe07f807ffc0ff

def z1062 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff8c7f187ff03ff 0xfffe31fc61ffc0ff

def z1063 : W := mkw 0x02d806e000920000 0x00b601b800248000 0xfff807e007ff03fe 0xfffe01f801ffc0ff

def z1064 : W := mkw 0x0985c58b0760c281 0x02617162c1d830a0 0xeb87c79f87e0e003 0x7ae1f1e7e1f83800

def z1065 : W := mkw 0x8985cd9b8f61ebc7 0x22617366e3d87af1 0xef8fdfff9fe3e3ff 0xfbe3f7ffe7f8f8ff

def z1066 : W := mkw 0x136fb80004db9800 0x04dbee000136e600 0xf7ff380006fffc01 0xbdffce0001bfff00

def z1067 : W := mkw 0x0985cd9b8761ebc3 0x02617366e1d87af0 0xef8fffff87e3ffff 0xfbe3ffffe1f8ffff

def z1068 : W := mkw 0x0d85c59ba76cf7f3 0xc3617166e9db3dfc 0xef87e7dfe7fcfff3 0xfbe1f9f7f9ff3ffc

def z1069 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xbc77075e661cff32 0x2f1dc1d799873fcc

def z1070 : W := mkw 0x8985c59b8f60e3c7 0x22617166e3d838f1 0xeb87c7bf9fe0e3cf 0x7ae1f1efe7f838f3

def z1071 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xeb8fffffffe0ffc3 0xfae3fffffff83ff0

def z1072 : W := mkw 0x03feb6ed50b600a8 0x00ffadbb542d802a 0xdffffffff9ff00ff 0xf7fffffffe7fc03f

def z1073 : W := mkw 0x126b3800049b9800 0x049ace000126e600 0xf7ff380007fffc01 0xfdffce0001ffff00

def z1074 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff827f067ff03ff 0xfffe09fc19ffc0ff

def z1075 : W := mkw 0x0985c58b0760c281 0x02617162c1d830a0 0x8b87c70e07e00000 0x62e1f1c381f80000

def z1076 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xdbffff1ff8000001 0xf6ffffc7fe000000

def z1077 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff85067fffc03 0xfdfffe1419ffff00

def z1078 : W := mkw 0x0d85859b266cb7b1 0xc3616166c99b2dec 0xaf87070e06fcff30 0x2be1c1c381bf3fcc

def z1079 : W := mkw 0x036ef80001934800 0x00dbbe000064d200 0xf7fff80007fffc01 0xfdfffe0001ffff00

def z1080 : W := mkw 0x0185c5890760c280 0x0061716241d830a0 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z1081 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x9877070e061cfc00 0x261dc1c381873f00

def z1082 : W := mkw 0x04332256640cb530 0xc10cc89599032d4c 0xdc77275e601cfc33 0xb71dc9d798073f0c

def z1083 : W := mkw 0x0d85c59ba764e7f3 0xc3617166e9d939fc 0xeb87c79f87e0e3f3 0x7ae1f1e7e1f838fc

def z1084 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xeb87c79f87e0ffc3 0x7ae1f1e7e1f83ff0

def z1085 : W := mkw 0x026b6800059bd800 0x009ada000166f600 0xf7fff80007fffc01 0xfdfffe0001ffff00

def z1086 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0x8b87078e07e000c0 0x62e1c1e381f80030

def z1087 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfffffffff9030003 0xfffffffffe40c000

def z1088 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef87e7dfe7e3ffff 0xfbe1f9f7f9f8ffff

def z1089 : W := mkw 0x027a326450960028 0x009e8c991425800a 0x7478f8f1f91f03ff 0xdd1e3e3c7e47c0ff

def z1090 : W := mkw 0x936ff8008ddbd846 0x24dbfe002376f611 0xf7fff8e19fffffff 0xfdfffe3867ffffff

def z1091 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf3f7f80007fcfc01 0x7cfdfe0001ff3f00

def z1092 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77e7dfe61cff33 0xff1df9f7f9873fcc

def z1093 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77270e061cff31 0xbf1dc9c381873fcc

def z1094 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x9c77275e661cfc31 0xa71dc9d799873f0c

def z1095 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0xb7f7000006fcfc00 0x2dfdc00001bf3f00

def z1096 : W := mkw 0x0c332356e62cb7f3 0xc30cc8d5b98b2dfc 0xfc77275e661cfff3 0xbf1dc9d799873ffc

def z1097 : W := mkw 0x936ff8008ddbd846 0x24dbfe002376f611 0xf7fff8f1fffffccf 0xfdfffe3c7fffff33

def z1098 : W := mkw 0x0258034002960220 0x009600d000a58088 0xfff807e007ff03fe 0xfffe01f801ffc0ff

def z1099 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfffffffff800fc03 0xfffffffffe003f00

def z1100 : W := mkw 0x8985c59baf60e7d7 0xa2617166ebd839f5 0xef87e7ffffe0ffff 0xfbe1f9fffff83fff

def z1101 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xcb87078e06e00002 0x72e1c1e381b80000

def z1102 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0x8b87c71f86e00001 0x22e1f1c7e1b80000

def z1103 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0x93fff80007fffc01 0x64fffe0001ffff00

def z1104 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xab87079f87e0e3c2 0x2ae1c1e7e1f838f0

def z1105 : W := mkw 0x0105c9122741ef10 0x8041724489d07bc4 0xef8fff5e67e3ff33 0xfbe3ffd799f8ffcc

def z1106 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xcb8ffffffee00003 0xf2e3ffffffb80000

def z1107 : W := mkw 0x067a2264409e1028 0x419e88991027840a 0x10700000001c0000 0x041c000000070000

def z1108 : W := mkw 0x8185cc99ad41ed56 0xa06173266b507b55 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z1109 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7727fffe1cff33 0xbf1dc9ffff873fcc

def z1110 : W := mkw 0x1bccdca981f348cb 0x06f3372a607cd232 0x0388d8a181e300cc 0x40e236286078c033

def z1111 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xeb87c79f87e003c3 0x7ae1f1e7e1f800f0

def z1112 : W := mkw 0x067a2244609e1430 0xc19e88911827850c 0x14782040601f1c30 0x851e08101807c70c

def z1113 : W := mkw 0x136ff82015dbd800 0x04dbfe080576f600 0xf7fff8201ffffc01 0xfdfffe0807ffff00

def z1114 : W := mkw 0x04332244640c9430 0xc10cc8911903250c 0xfc77275e661cfc33 0xbf1dc9d799873f0c

def z1115 : W := mkw 0x13ffb7ed56fe92a8 0x04ffedfb55bfa4aa 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z1116 : W := mkw 0x0184c599832063c2 0x0061316660c818f0 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z1117 : W := mkw 0x03feb6ed50040020 0x00ffadbb54010008 0xdffffffff81c0033 0xf7fffffffe07000c

def z1118 : W := mkw 0x03feb6ed50920000 0x00ffadbb54248000 0xdbfffffff9e30003 0xf6fffffffe78c000

def z1119 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc77271e661cfc01 0xbf1dc9c799873f00

def z1120 : W := mkw 0x03feb6ed50b20088 0x00ffadbb542c8022 0xffffffffffff00cf 0xffffffffffffc033

def z1121 : W := mkw 0x0985c49b8560e1c3 0x02617126e1583870 0xcb87c79f81e0e0c3 0x72e1f1e7e0783830

def z1122 : W := mkw 0x008105920620a380 0x00204164818828e0 0xeb87071e06e0e303 0x3ae1c1c781b838c0

def z1123 : W := mkw 0x0126b00d50000000 0x0049ac0354000000 0xc807ff1ff8000003 0x3201ffc7fe000000

def z1124 : W := mkw 0x02d807ed52b602a8 0x00b601fb54ad80aa 0xfff8ffffffff03ff 0xfffe3fffffffc0ff

def z1125 : W := mkw 0x136fb00004da9000 0x04dbec000136a400 0xf7fff80006fcfc01 0xfdfffe0001bf3f00

def z1126 : W := mkw 0x8984cc99a9616dd7 0xa26133266a585b75 0xef8ffffff9e3ffff 0xfbe3fffffe78ffff

def z1127 : W := mkw 0x04333356760cb730 0xc10cccd59d832dcc 0xfc773f5e7e1cff33 0xbf1dcfd79f873fcc

def z1128 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xab87c78f87e0e3c0 0x6ae1f1e3e1f838f0

def z1129 : W := mkw 0x1249480005dbd800 0x049252000176f600 0xf7f8f80007fffc01 0xfdfe3e0001ffff00

def z1130 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xeb8fffbfffe3ffcf 0x7ae3ffeffff8fff3

def z1131 : W := mkw 0x8985cd9b8f61ebc7 0x22617366e3d87af1 0xeb87df9f9fe0e3c3 0x7ae1f7e7e7f838f0

def z1132 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bffff7ff8000001 0xa6ffffdffe000000

def z1133 : W := mkw 0x0023200004089000 0x0008c80001022400 0xfc77271e061cfc03 0xbf1dc9c781873f00

def z1134 : W := mkw 0x027a226440960028 0x009e88991025800a 0x14782060601f003c 0x851e08181807c00f

def z1135 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0x8b87c79f87e0e0c1 0x62e1f1e7e1f83830

def z1136 : W := mkw 0x0985c59b8764e3e3 0x02617166e1d938f8 0xef87c79f87fce3f3 0x7be1f1e7e1ff38fc

def z1137 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0xfbfffffff90003c3 0xfefffffffe4000f0

def z1138 : W := mkw 0x8985859bae60a7d7 0xa2616166eb9829f5 0x8b8707fffee003fe 0x22e1c1ffffb800ff

def z1139 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xef87c7df87e0e3f3 0xfbe1f1f7e1f838fc

def z1140 : W := mkw 0x0081058206208280 0x00204160818820a0 0x8b87070e06e00000 0x22e1c1c381b80000

def z1141 : W := mkw 0x13ccdc8901d34800 0x04f337224074d200 0x0388d88181e30000 0x40e236206078c000

def z1142 : W := mkw 0x02c8058002b602a8 0x00b2016000ad80aa 0xfff8078007ff03fe 0xfffe01e001ffc0ff

def z1143 : W := mkw 0x1127f8000549d800 0x0449fe0001527600 0xf7f7f80007fcfc01 0xfdfdfe0001ff3f00

def z1144 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xeb87070e07e00000 0x7ae1c1c381f80000

def z1145 : W := mkw 0x0185848904408000 0x0061612241102000 0x8b87070e06e00000 0x22e1c1c381b80000

def z1146 : W := mkw 0x0105c1020740c200 0x0041704081d03080 0xeb87c70e07e0e001 0x7ae1f1c381f83800

def z1147 : W := mkw 0x04332356460cb320 0x410cc8d591832cc8 0xfc77271e061cff03 0xbf1dc9c781873fc0

def z1148 : W := mkw 0x0984c589836042c3 0x0261316260d810b0 0xeb87c79f87e003c3 0x7ae1f1e7e1f800f0

def z1149 : W := mkw 0x02c8058002b20280 0x00b2016000ac80a0 0xfff807e007ff03fe 0xfffe01f801ffc0ff

def z1150 : W := mkw 0x0000480001014800 0x0000120000405200 0x6408f8f1f903ffff 0xd9023e3c7e40ffff

def z1151 : W := mkw 0x04332356662cb7b0 0xc10cc8d5998b2dec 0xfc77275e67fcfff3 0xbf1dc9d799ff3ffc

def z1152 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xffffff1e07fffc03 0xffffffc781ffff00

def z1153 : W := mkw 0x03feb6ed50960028 0x00ffadbb5425800a 0xffffffffffff003f 0xffffffffffffc00f

def z1154 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xd3fff80006fcfc01 0xf4fffe0001bf3f00

def z1155 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8e007fffc03 0xfdfffe3801ffff00

def z1156 : W := mkw 0x0184858902200280 0x00612162408800a0 0xef8fffffffe303ff 0xfbe3fffffff8c0ff

def z1157 : W := mkw 0x0258036002b602a8 0x009600d800ad80aa 0xf7f8006007ff03fc 0xfdfe001801ffc0ff

def z1158 : W := mkw 0x07ffb7ef56be92a8 0x41ffedfbd5afa4aa 0x9bf7070e06fc0000 0x26fdc1c381bf0000

def z1159 : W := mkw 0x04332356662cb7b8 0xc10cc8d5998b2dee 0xfc77275e661cffff 0xbf1dc9d799873fff

def z1160 : W := mkw 0x0184858902200280 0x00612162408800a0 0xcb87c79f86e00003 0x72e1f1e7e1b80000

def z1161 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87c7ffffe0e3c3 0x7ae1f1fffff838f0

def z1162 : W := mkw 0x02d807ed52b602a8 0x00b601fb54ad80aa 0xfff807ee07ff03fe 0xfffe01fb81ffc0ff

def z1163 : W := mkw 0x167a3a44409f1820 0x459e8e911027c608 0x14783800001f1c00 0x851e0e000007c700

def z1164 : W := mkw 0x98014912affbffd7 0xa6005244abfefff5 0x2400000007fffffc 0x0900000001ffffff

def z1165 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7f277e661fff3f 0xbf1fc9df9987ffcf

def z1166 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xef87ffdfffe0fff3 0xfbe1fff7fff83ffc

def z1167 : W := mkw 0x0984c489816040c3 0x0261312260581030 0x8b87c78f81e000c0 0x62e1f1e3e0780030

def z1168 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87e7dfe7e0e3c3 0xfae1f9f7f9f838f0

def z1169 : W := mkw 0x0985cd9b8761ebc3 0x02617366e1d87af0 0xeb8fdf9f87e3e3c3 0x7ae3f7e7e1f8f8f0

def z1170 : W := mkw 0x127a3a64509f1828 0x049e8e991427c60a 0x14783860781f1c3c 0x851e0e181e07c70f

def z1171 : W := mkw 0x8c9007dfea2427f7 0xe32401f7fa8909fd 0x080007fff80003fe 0x020001fffe0000ff

def z1172 : W := mkw 0x02fa26e440000000 0x00be89b910000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1173 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0xfc7727fe661cffff 0xbf1dc9ff99873fff

def z1174 : W := mkw 0x8d85cd9baf6dfff7 0xe3617366ebdb7ffd 0xef8fffffffffffff 0xfbe3ffffffffffff

def z1175 : W := mkw 0x1bccdc8901f34881 0x06f33722407cd220 0x0388d80001e30000 0x40e236000078c000

def z1176 : W := mkw 0x9527f816ed49fd56 0xe549fe05bb527f55 0x0007f81ff800fc01 0x0001fe07fe003f00

def z1177 : W := mkw 0x036fb000049a9000 0x00dbec000126a400 0xf7fff80007fffc01 0xfdfffe0001ffff00

def z1178 : W := mkw 0x0985859b0660a381 0x02616166c19828e0 0xab87070e06e0e300 0x2ae1c1c381b838c0

def z1179 : W := mkw 0x04110352260cb730 0xc10440d489832dcc 0xfc77075e061cff33 0xbf1dc1d781873fcc

def z1180 : W := mkw 0x0985cd9b8761ebc3 0x02617366e1d87af0 0xef8fffffffe3ffc3 0xfbe3fffffff8fff0

def z1181 : W := mkw 0x049007ff722427b8 0xc12401ffdc8909ee 0x080007fff80003fe 0x020001fffe0000ff

def z1182 : W := mkw 0x927a7a74f99b7d56 0xa49e9e9d3e66df55 0x7478f8f1f91fffff 0xdd1e3e3c7e47ffff

def z1183 : W := mkw 0x027a326450960028 0x009e8c991425800a 0x14780060001f003c 0x851e00180007c00f

def z1184 : W := mkw 0x0985c59b0760e381 0x02617166c1d838e0 0xeb87c71e07e0e303 0x7ae1f1c781f838c0

def z1185 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff807f1ffff03fe 0xfffe01fc7fffc0ff

def z1186 : W := mkw 0x9127f810ad49fd56 0xa449fe042b527f55 0x0007f8000000fc01 0x0001fe0000003f00

def z1187 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xbff807a007ff03fc 0x6ffe01e801ffc0ff

def z1188 : W := mkw 0x03feb6ed50200080 0x00ffadbb54080020 0xdbfffffff9e000c3 0xf6fffffffe780030

def z1189 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0xeb87070e06e0e001 0x3ae1c1c381b83800

def z1190 : W := mkw 0x03feb6ed50b20088 0x00ffadbb542c8022 0xdbfffffff8e00003 0xf6fffffffe380000

def z1191 : W := mkw 0x00b226ed50000000 0x002c89bb54000000 0xd87ffffff8000003 0xf61ffffffe000000

def z1192 : W := mkw 0x009007f0222427b8 0x802401fc088909ee 0x080007f0600003fe 0x020001fc180000ff

def z1193 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff80007fffffd 0xfdfffe0001ffffff

def z1194 : W := mkw 0x0985c59b8760e3c3 0x02617166e1d838f0 0xeb87ff9fffe0e3c3 0x7ae1ffe7fff838f0

def z1195 : W := mkw 0x03feb6ed50920000 0x00ffadbb54248000 0xdbfffffffefc0003 0xf6ffffffffbf0000

def z1196 : W := mkw 0x136ff80005dbd800 0x04dbfe000176f600 0xf7fff8607ffffc01 0xfdfffe181fffff00

def z1197 : W := mkw 0x04332356660cb730 0xc10cc8d599832dcc 0x9877275e661cff33 0x261dc9d799873fcc

def z1198 : W := mkw 0x0985c58b0760c281 0x02617162c1d830a0 0xab87070e07e0e000 0x2ae1c1c381f83800

def z1199 : W := mkw 0x136ff80455dbd800 0x04dbfe011576f600 0xf7fff8007ffffc01 0xfdfffe001fffff00

def z1200 : W := mkw 0x0d85858b066c92a1 0x43616162c19b24a8 0x8b87070e06fc0000 0x22e1c1c381bf0000

def z1201 : W := mkw 0x8985cd8b8f61cac7 0x22617362e3d872b1 0x8b8fdfaf9fe300cc 0x62e3f7ebe7f8c033

def z1202 : W := mkw 0x03eeb4ad50000000 0x00fbad2b54000000 0xcb8fffbff8000003 0x72e3ffeffe000000

def z1203 : W := mkw 0x80004810a9016d56 0xa00012042a405b55 0x0408f8f1f803ffff 0x81023e3c7e00ffff

def z1204 : W := mkw 0x03feb6ed50000000 0x00ffadbb54000000 0x9bffffbff8000001 0x66ffffeffe000000

def z1205 : W := mkw 0x0105c1128740e342 0x00417044a1d038d0 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z1206 : W := mkw 0x13feb6ed50d20000 0x04ffadbb54348000 0xdbfffffff8e00003 0xf6fffffffe380000

def z1207 : W := mkw 0x0985c58b8760c2c3 0x02617162e1d830b0 0x8b87c70f86e00000 0x22e1f1c3e1b80000

def z1208 : W := mkw 0x127a3264509a1000 0x049e8c9914268400 0x10700000001c0000 0x041c000000070000

def z1209 : W := mkw 0x0985858b06608281 0x02616162c19820a0 0x8b87078e06e003c2 0x22e1c1e381b800f0

def z1210 : W := mkw 0x0185c4998540e142 0x0061712661503850 0xeb87c79f87e0e3c3 0x7ae1f1e7e1f838f0

def z1211 : W := mkw 0x0081058206208280 0x00204160818820a0 0xeb87078e07e003c2 0x7ae1c1e381f800f0

def z1212 : W := mkw 0x0905c11b8740e343 0x02417046e1d038d0 0xeb87c71f87e0e303 0x7ae1f1c7e1f838c0

def z1213 : W := mkw 0x84332356ee0cb776 0xe10cc8d5bb832ddd 0xfc7f27ffff1fffff 0xff1fc9ffffc7ffff

def z1214 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0x8b87ff1ffee0fc01 0x22e1ffc7ffb83f00

def z1215 : W := mkw 0x02d807e002b602a8 0x00b601f800ad80aa 0xfff0078007ff03fe 0x7ffc01e001ffc0ff

def z1216 : W := mkw 0x8985cd9baf61efd7 0xa2617366ebd87bf5 0xaf87070e07e3fffc 0x2be1c1c381f8ffff

def z1217 : W := mkw 0x0985859b2660a791 0x82616166c99829e4 0xef87275e66e0ff33 0xbbe1c9d799b83fcc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z8,z4,z5,z9]),(0,[z10,z1,z2,z3,z8,z4,z5]),(1,[z1,z3,z4,z5,z11,z6])],[(1,[z1,z2,z3,z12,z4,z5]),(0,[z1,z13,z2,z3,z8,z4,z5]),(0,[z14,z1,z15,z3,z8,z4,z5]),(0,[z16,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z17,z5]),(0,[z1,z18,z2,z3,z8,z19,z5]),(0,[z20,z1,z2,z3,z8,z4,z5]),(1,[z21,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z22]),(0,[z23,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z24,z4,z5])],[(0,[z1,z2,z3,z8,z25,z4,z5]),(0,[z26,z27,z1,z2,z3,z4,z5]),(0,[z1,z28,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z8,z4,z5,z31]),(0,[z32,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z33,z4,z5])],[(0,[z0,z1,z2,z3,z34,z4,z5]),(0,[z35,z1,z2,z3,z36,z4,z5])],[(0,[z1,z2,z3,z8,z4,z37,z5]),(0,[z14,z1,z2,z3,z8,z38,z5]),(0,[z39,z1,z2,z3,z8,z38,z5]),(0,[z1,z2,z3,z40,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z41])],[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z42])],[(0,[z1,z2,z3,z43,z8,z4,z5]),(0,[z44,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z45,z8,z4,z5]),(0,[z1,z2,z46,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z1,z48,z2,z3,z8,z4,z5])]],
   [[(1,[z49,z1,z2,z3,z4,z5]),(0,[z50,z1,z2,z3,z8,z4,z5]),(0,[z51,z1,z2,z3,z8,z4,z5]),(0,[z1,z46,z3,z52,z8,z4,z5]),(0,[z53,z54,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z55,z5])],[(0,[z29,z14,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z4,z56,z5]),(0,[z1,z2,z3,z57,z8,z4,z5]),(0,[z1,z2,z3,z8,z58,z4,z5]),(0,[z1,z18,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z59,z8,z4,z5]),(0,[z60,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z61,z5])],[(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z63,z5]),(1,[z1,z2,z3,z64,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z65])],[(0,[z66,z2,z3,z8,z4,z5,z9]),(1,[z1,z67,z3,z8,z4,z5]),(0,[z68,z1,z2,z3,z43,z4,z5]),(0,[z1,z2,z3,z69,z8,z4,z5]),(0,[z1,z2,z3,z8,z70,z4,z5]),(0,[z1,z2,z71,z3,z8,z4,z5])],[(0,[z1,z2,z3,z72,z8,z4,z5]),(0,[z1,z2,z3,z8,z73,z4,z5])],[(0,[z2,z74,z3,z8,z75,z4,z5]),(0,[z66,z76,z1,z3,z8,z4,z5]),(0,[z26,z68,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z77,z8,z4,z5]),(0,[z1,z2,z3,z78,z8,z4,z5]),(0,[z1,z2,z3,z8,z79,z4,z5]),(0,[z1,z2,z3,z8,z80,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z81]),(0,[z1,z2,z3,z8,z4,z82,z5]),(0,[z83,z1,z2,z3,z8,z4,z5]),(0,[z84,z1,z2,z3,z8,z4,z5]),(0,[z39,z14,z2,z3,z8,z4,z5]),(0,[z39,z2,z3,z8,z75,z4,z5]),(1,[z85,z1,z52,z8,z4,z5]),(0,[z53,z1,z2,z3,z8,z86,z5]),(0,[z1,z2,z3,z8,z87,z5,z88]),(0,[z1,z2,z3,z89,z36,z4,z5]),(0,[z90,z1,z2,z3,z8,z4,z91])]],
   [[(0,[z1,z2,z3,z12,z92,z4,z5]),(1,[z54,z2,z3,z8,z4,z5]),(0,[z93,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z94,z4,z5]),(0,[z95,z1,z2,z3,z8,z4,z5])],[(0,[z14,z1,z2,z3,z8,z96,z5]),(0,[z39,z1,z2,z3,z8,z96,z5]),(1,[z1,z2,z97,z8,z4,z5]),(0,[z1,z2,z3,z4,z98,z5,z99]),(0,[z1,z2,z3,z8,z100,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z101])],[(0,[z102,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z103,z4,z5]),(0,[z1,z2,z92,z8,z4,z5,z31]),(0,[z1,z2,z3,z8,z104,z4,z5]),(0,[z1,z2,z3,z105,z4,z47,z5]),(0,[z106,z2,z3,z8,z4,z5,z91]),(1,[z2,z3,z8,z4,z5,z107]),(1,[z1,z2,z3,z8,z33,z96])],[(0,[z1,z108,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z19,z5,z91]),(0,[z1,z2,z3,z8,z4,z5,z109])],[(0,[z110,z1,z2,z3,z8,z4,z5]),(0,[z111,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z112,z36,z4,z5]),(0,[z1,z113,z46,z3,z8,z4,z5]),(0,[z114,z1,z2,z3,z8,z4,z5]),(0,[z53,z1,z2,z3,z8,z4,z115]),(0,[z116,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z117,z4,z5]),(0,[z118,z1,z2,z3,z8,z4,z5])],[(0,[z66,z76,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z119]),(0,[z90,z14,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z4,z120,z5]),(1,[z30,z1,z2,z8,z4,z31])],[(0,[z1,z2,z3,z121,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z122,z5]),(0,[z1,z2,z3,z8,z4,z5,z123]),(0,[z1,z2,z3,z124,z8,z4,z5]),(1,[z1,z2,z3,z8,z86,z5]),(0,[z1,z3,z8,z4,z5,z125,z31]),(0,[z1,z2,z3,z8,z4,z5,z126])]],
   [[(0,[z1,z2,z127,z3,z8,z4,z5]),(0,[z128,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z129,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z130]),(0,[z1,z113,z2,z8,z129,z4,z5]),(0,[z131,z1,z2,z3,z8,z4,z5]),(0,[z132,z1,z2,z3,z8,z4,z5]),(0,[z133,z1,z2,z3,z36,z4,z5])],[(0,[z134,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z135,z5]),(0,[z1,z2,z3,z8,z4,z136,z5]),(0,[z1,z2,z3,z137,z4,z138,z5]),(0,[z1,z2,z3,z8,z4,z139,z5])],[(0,[z140,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z141]),(0,[z14,z2,z3,z8,z4,z98,z5]),(0,[z7,z1,z142,z3,z8,z4,z5]),(1,[z1,z113,z46,z8,z4,z5]),(0,[z1,z2,z3,z143,z8,z4,z5]),(0,[z1,z2,z3,z8,z144,z4,z5])],[(0,[z1,z2,z3,z145,z8,z4,z5]),(0,[z1,z2,z15,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z146]),(0,[z1,z2,z3,z147,z8,z137,z5]),(0,[z1,z2,z3,z137,z4,z5,z6]),(0,[z148,z1,z2,z3,z36,z4,z5])],[(0,[z149,z1,z2,z3,z8,z4,z5]),(0,[z76,z1,z2,z3,z8,z150,z5]),(0,[z1,z2,z3,z12,z8,z4,z5]),(0,[z1,z2,z3,z8,z151,z4,z5]),(0,[z152,z1,z2,z3,z8,z4,z5])],[(0,[z153,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z154,z5]),(1,[z1,z2,z3,z78,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z155]),(0,[z156,z1,z2,z3,z36,z4,z5]),(0,[z157,z1,z2,z3,z8,z4,z5])],[(0,[z158,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z159,z5]),(0,[z35,z1,z2,z3,z69,z4,z5])]],
   [[(0,[z1,z2,z3,z8,z160,z4,z5]),(0,[z76,z1,z3,z43,z8,z4,z5]),(0,[z161,z1,z2,z3,z36,z4,z5])],[(0,[z76,z1,z46,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z33,z38,z5]),(0,[z1,z2,z3,z8,z4,z162,z5]),(0,[z1,z2,z163,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z164,z4,z5]),(0,[z1,z2,z3,z36,z4,z165,z5]),(0,[z1,z2,z3,z8,z4,z166,z5])],[(1,[z1,z2,z3,z8,z4,z5]),(0,[z14,z2,z3,z8,z4,z38,z5]),(0,[z2,z3,z8,z75,z4,z38,z5]),(0,[z1,z167,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z168,z4,z5]),(0,[z169,z1,z2,z3,z8,z4,z5])],[(0,[z170,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z171]),(0,[z85,z1,z2,z52,z8,z4,z5]),(0,[z1,z2,z3,z4,z172,z165,z5]),(0,[z173,z1,z2,z3,z8,z4,z5])],[(0,[z174,z1,z2,z3,z8,z4,z5]),(1,[z175,z1,z2,z8,z4,z5])],[(0,[z1,z2,z3,z8,z176,z4,z5]),(0,[z1,z2,z3,z43,z4,z5,z6])],[(0,[z7,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z52,z8,z4,z5,z31]),(0,[z1,z2,z46,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z177,z5])]],
   [[(0,[z1,z2,z3,z178,z8,z4,z5]),(0,[z179,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z180,z5,z6])],[(0,[z1,z2,z3,z8,z4,z181,z5]),(0,[z1,z2,z3,z8,z4,z182,z5]),(0,[z183,z1,z2,z3,z8,z4,z5]),(0,[z106,z1,z2,z3,z8,z4,z5])],[(1,[z170,z2,z3,z8,z4,z98]),(0,[z184,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z185,z3,z8,z4,z5]),(0,[z1,z54,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z186,z8,z4,z5]),(0,[z35,z1,z2,z8,z187,z4,z5]),(0,[z1,z188,z2,z3,z8,z4,z5])],[(0,[z62,z1,z2,z59,z3,z4,z5]),(0,[z189,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z69,z4,z5,z6])],[(0,[z1,z2,z3,z8,z75,z33,z5]),(0,[z190,z1,z2,z3,z8,z5,z9]),(0,[z191,z1,z2,z3,z8,z4,z5]),(0,[z192,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z107])],[(0,[z2,z193,z3,z92,z8,z4,z5]),(0,[z1,z2,z3,z194,z8,z4,z5])],[(0,[z195,z1,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z163,z8,z4,z5]),(0,[z1,z2,z196,z8,z129,z4,z5]),(0,[z1,z2,z3,z8,z33,z96,z5])],[(0,[z1,z2,z3,z92,z36,z4,z5]),(0,[z27,z1,z2,z3,z36,z4,z5]),(0,[z84,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z197,z4,z5])]],
   [[(0,[z1,z3,z8,z19,z4,z47,z5]),(0,[z1,z2,z3,z8,z198,z4,z5]),(0,[z199,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z59,z3,z69,z4,z5]),(0,[z1,z2,z3,z8,z4,z200,z5]),(0,[z1,z2,z3,z8,z4,z201,z5])],[(0,[z1,z2,z3,z8,z202,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z203]),(0,[z204,z1,z2,z3,z8,z4,z5])],[(0,[z66,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z112,z8,z4,z5]),(0,[z35,z62,z1,z2,z3,z4,z5]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z47,z5]),(1,[z1,z2,z3,z4,z5,z205])],[(0,[z1,z2,z3,z8,z4,z5,z206]),(0,[z207,z1,z2,z3,z8,z4,z5]),(0,[z7,z1,z2,z97,z8,z4,z5]),(0,[z1,z2,z3,z8,z208,z4,z5]),(0,[z1,z209,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z210]),(0,[z1,z2,z3,z36,z36,z4,z5])],[(0,[z1,z2,z3,z8,z4,z211,z5]),(0,[z1,z2,z3,z8,z212,z4,z5]),(0,[z14,z1,z2,z3,z8,z75,z5]),(0,[z39,z1,z2,z3,z8,z75,z5]),(0,[z7,z1,z2,z3,z8,z213,z5]),(0,[z1,z2,z3,z36,z19,z4,z5]),(0,[z214,z1,z2,z3,z8,z187,z5]),(0,[z1,z2,z3,z36,z4,z5,z5])],[],[(0,[z1,z2,z3,z215,z8,z4,z5]),(0,[z1,z2,z3,z8,z216,z4,z5])],[(0,[z217,z1,z2,z3,z8,z4,z5]),(0,[z7,z1,z2,z3,z8,z4,z9]),(0,[z1,z2,z3,z36,z187,z4,z5]),(0,[z1,z2,z3,z8,z4,z165,z5]),(1,[z1,z2,z196,z8,z4,z87]),(0,[z218,z1,z2,z3,z8,z4,z5]),(1,[z219,z1,z2,z3,z4,z6])]],
   [[(0,[z220,z1,z2,z3,z8,z4,z5]),(0,[z221,z1,z2,z3,z92,z8,z5]),(0,[z222,z1,z2,z3,z8,z4,z5]),(1,[z27,z1,z3,z43,z4,z5]),(0,[z1,z2,z223,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z224,z4,z5]),(0,[z1,z2,z3,z4,z5,z225,z6])],[(1,[z226,z1,z3,z8,z4,z5]),(1,[z161,z1,z3,z8,z19,z5]),(0,[z227,z1,z2,z3,z8,z4,z5])],[(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z228])],[(0,[z1,z2,z3,z8,z4,z5,z9]),(0,[z1,z2,z3,z8,z229,z4,z5]),(0,[z1,z2,z230,z3,z8,z4,z5]),(0,[z1,z231,z2,z3,z8,z4,z5])],[(0,[z232,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z233,z5]),(0,[z234,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z235,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z236,z5]),(0,[z1,z2,z3,z8,z237,z4,z5]),(0,[z1,z238,z2,z3,z8,z4,z5]),(0,[z27,z1,z2,z3,z239,z4,z5]),(1,[z214,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z4,z240,z5]),(1,[z1,z2,z3,z241,z4,z5])],[(0,[z1,z2,z242,z3,z8,z4,z5]),(0,[z1,z2,z193,z196,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z243,z5]),(0,[z161,z1,z2,z3,z8,z4,z5]),(0,[z244,z1,z2,z3,z8,z4,z5]),(0,[z90,z1,z2,z3,z197,z4,z5])],[(0,[z245,z1,z2,z3,z8,z4,z5]),(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z246,z8,z4,z5]),(0,[z1,z2,z3,z8,z247,z4,z5])]],
   [[(0,[z1,z248,z2,z3,z8,z4,z5]),(0,[z39,z1,z2,z3,z8,z19,z5]),(0,[z249,z1,z2,z3,z8,z4,z5]),(0,[z1,z250,z2,z3,z8,z4,z5]),(1,[z1,z2,z3,z36,z4,z180])],[(0,[z251,z1,z2,z3,z8,z4,z5]),(0,[z1,z113,z2,z46,z8,z4,z5]),(0,[z1,z2,z3,z36,z239,z4,z5]),(0,[z53,z1,z2,z3,z252,z4,z5]),(0,[z1,z2,z163,z3,z4,z5,z6]),(0,[z1,z253,z2,z3,z8,z4,z5])],[(0,[z85,z1,z74,z3,z8,z4,z5]),(0,[z170,z1,z2,z3,z8,z4,z5]),(1,[z1,z2,z3,z36,z4,z6]),(0,[z1,z2,z3,z8,z254,z4,z5]),(0,[z1,z255,z2,z3,z8,z4,z5])],[(0,[z1,z2,z256,z3,z8,z4,z5]),(0,[z1,z2,z3,z257,z8,z4,z5]),(0,[z1,z258,z2,z3,z8,z4,z259]),(1,[z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z260,z8,z4,z5]),(0,[z261,z1,z2,z3,z8,z4,z5]),(1,[z1,z2,z262,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z263,z5]),(0,[z1,z2,z3,z8,z224,z87,z5])],[(0,[z1,z2,z3,z264,z8,z4,z5]),(0,[z1,z2,z3,z8,z265,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z266])],[(0,[z1,z267,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z268,z5]),(0,[z1,z2,z3,z129,z4,z5,z6]),(0,[z269,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z270])],[(0,[z271,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z164,z187,z5]),(0,[z1,z2,z3,z272,z8,z4,z5]),(1,[z273,z1,z3,z8,z4,z5]),(0,[z1,z2,z196,z8,z4,z87,z5])]],
   [[(0,[z1,z2,z274,z3,z8,z4,z5]),(0,[z275,z1,z2,z3,z8,z4,z5]),(0,[z175,z1,z2,z8,z4,z138,z5])],[(0,[z1,z2,z3,z8,z4,z276,z5]),(0,[z1,z2,z3,z8,z4,z5,z5]),(0,[z68,z27,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z19,z4,z5]),(1,[z1,z2,z3,z252,z4,z5]),(0,[z1,z2,z3,z277,z8,z4,z5]),(0,[z1,z2,z278,z3,z8,z4,z5]),(1,[z279,z1,z3,z8,z4,z5])],[(0,[z280,z1,z2,z3,z8,z4,z5]),(0,[z281,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z282,z3,z8,z4,z5]),(0,[z1,z3,z43,z8,z4,z259,z5]),(1,[z1,z2,z3,z4,z5,z283]),(0,[z35,z1,z2,z3,z187,z4,z5]),(0,[z175,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z284])],[(0,[z1,z2,z3,z8,z4,z285,z5]),(0,[z1,z2,z3,z286,z8,z4,z5]),(0,[z27,z1,z2,z3,z69,z4,z5]),(0,[z287,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z187,z4,z5]),(0,[z26,z1,z2,z163,z3,z8,z5]),(0,[z1,z288,z2,z3,z8,z4,z5]),(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z36,z4,z5])],[(0,[z35,z0,z1,z2,z3,z4,z5]),(0,[z290,z1,z2,z3,z8,z4,z5]),(0,[z291,z1,z2,z3,z8,z4,z5])],[(0,[z26,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z292,z8,z4,z5]),(0,[z1,z2,z293,z3,z8,z4,z5])],[(0,[z294,z14,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z295,z4,z5]),(0,[z1,z2,z3,z8,z4,z296,z5]),(0,[z1,z2,z3,z297,z8,z4,z5])]],
   [[(0,[z1,z2,z74,z3,z4,z5,z6]),(0,[z281,z1,z2,z193,z8,z4,z5]),(0,[z85,z1,z113,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z298,z5]),(0,[z1,z2,z3,z8,z4,z86,z5]),(0,[z299,z1,z2,z3,z8,z4,z5])],[(1,[z300,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z8,z4,z301,z5]),(0,[z53,z1,z2,z3,z8,z302,z5]),(0,[z1,z2,z3,z303,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z304]),(0,[z1,z2,z3,z36,z8,z4,z5]),(0,[z1,z2,z3,z36,z305,z4,z5])],[(0,[z14,z2,z74,z3,z8,z4,z5]),(0,[z1,z2,z306,z3,z8,z4,z5]),(0,[z1,z2,z3,z112,z4,z5,z6]),(0,[z214,z1,z2,z3,z8,z4,z5]),(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z307,z3,z8,z4,z5])],[(0,[z308,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z88])],[(0,[z1,z2,z3,z36,z4,z5,z91])],[(0,[z309,z1,z2,z3,z8,z4,z5])],[(0,[z310,z1,z2,z3,z8,z4,z5]),(0,[z311,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z239,z4,z5]),(0,[z1,z2,z3,z312,z8,z4,z5])],[(0,[z217,z1,z2,z3,z4,z5,z6]),(0,[z158,z2,z193,z3,z8,z4,z5]),(0,[z1,z2,z59,z3,z36,z4,z5]),(0,[z279,z1,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z313,z36,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z138,z5,z6])],[(0,[z1,z2,z3,z314,z8,z4,z5]),(1,[z1,z2,z3,z8,z302,z5]),(0,[z315,z1,z2,z3,z8,z4,z5]),(0,[z316,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z317,z4,z5,z6]),(0,[z1,z2,z318,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z319,z5]),(0,[z320,z1,z2,z3,z8,z4,z5]),(0,[z68,z1,z3,z8,z239,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z321]),(0,[z35,z26,z1,z2,z3,z4,z5]),(0,[z1,z2,z322,z3,z8,z4,z5])],[(0,[z2,z74,z3,z8,z4,z5,z9]),(0,[z1,z74,z3,z8,z4,z47,z5]),(0,[z323,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z324,z3,z8,z4,z5]),(0,[z325,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z59,z3,z187,z4,z5]),(0,[z1,z2,z3,z4,z165,z5,z6]),(0,[z1,z2,z3,z36,z326,z4,z5]),(0,[z1,z2,z3,z8,z96,z5,z91])],[(0,[z76,z1,z3,z8,z4,z5,z115]),(0,[z327,z1,z2,z3,z8,z4,z5]),(1,[z1,z3,z8,z4,z5,z125])],[(0,[z1,z328,z2,z3,z8,z4,z5]),(0,[z1,z2,z46,z3,z329,z4,z5]),(0,[z1,z2,z3,z8,z330,z4,z5])],[(1,[z281,z2,z92,z8,z4,z5]),(0,[z1,z2,z331,z3,z8,z4,z5]),(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z53,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z332,z8,z4,z5]),(0,[z1,z2,z333,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z334,z4,z5]),(0,[z327,z62,z1,z3,z8,z4,z5]),(0,[z335,z1,z2,z3,z8,z4,z5])]],
   [[(0,[z68,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z336]),(0,[z1,z3,z8,z4,z5,z11,z6])],[(0,[z1,z2,z3,z8,z337,z4,z5]),(0,[z1,z2,z3,z338,z8,z4,z5]),(0,[z85,z1,z2,z8,z129,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z339]),(0,[z161,z1,z2,z3,z8,z47,z5]),(0,[z1,z2,z340,z3,z8,z4,z5])],[(0,[z170,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z341,z4,z5]),(0,[z1,z2,z3,z342,z8,z4,z5]),(0,[z1,z2,z3,z4,z87,z5,z205]),(1,[z1,z2,z8,z4,z343,z5])],[(1,[z66,z76,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z344,z4,z5])],[(0,[z0,z1,z2,z59,z3,z4,z5]),(0,[z1,z2,z345,z3,z8,z4,z5]),(0,[z53,z1,z3,z43,z8,z4,z5]),(0,[z1,z2,z3,z8,z346,z4,z5]),(0,[z347,z1,z2,z3,z8,z4,z5]),(0,[z1,z258,z2,z3,z8,z4,z115]),(0,[z35,z1,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z3,z8,z33,z5]),(0,[z30,z1,z2,z196,z8,z4,z5]),(0,[z1,z348,z2,z3,z8,z4,z5])],[(0,[z349,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z350,z8,z4,z5])],[(0,[z351,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z8,z4,z5]),(1,[z1,z2,z3,z4,z5,z99]),(0,[z1,z2,z3,z8,z4,z352,z5]),(0,[z1,z353,z2,z3,z8,z4,z5])],[(0,[z217,z1,z74,z3,z8,z4,z5]),(0,[z354,z1,z2,z3,z8,z4,z5]),(0,[z355,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z356,z3,z8,z4,z5]),(0,[z29,z1,z2,z69,z8,z4,z5]),(0,[z219,z1,z2,z3,z8,z4,z180])]],
   [[(0,[z29,z1,z2,z196,z8,z4,z5]),(0,[z273,z1,z3,z8,z4,z5,z31]),(0,[z1,z357,z2,z3,z8,z4,z5])],[(1,[z1,z2,z3,z8,z150,z5]),(0,[z1,z2,z3,z8,z4,z5,z358]),(0,[z1,z113,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z359,z4,z5]),(0,[z360,z1,z2,z3,z8,z4,z5]),(0,[z219,z1,z2,z3,z8,z4,z6]),(1,[z279,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z361,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z91])],[(0,[z76,z68,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z362,z4,z5]),(0,[z1,z2,z3,z363,z8,z4,z5]),(0,[z62,z1,z235,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z47,z5]),(0,[z364,z1,z2,z3,z8,z4,z5]),(0,[z365,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z366,z5]),(0,[z1,z2,z3,z147,z36,z4,z5]),(0,[z280,z1,z2,z3,z4,z5,z6])],[(0,[z367,z1,z2,z3,z8,z4,z5]),(1,[z1,z2,z3,z186,z4,z5])],[(0,[z35,z1,z2,z3,z137,z4,z5]),(0,[z26,z1,z2,z3,z8,z4,z5])],[(0,[z368,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z369,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z370])],[(0,[z161,z1,z74,z3,z8,z4,z5]),(1,[z190,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z371,z4,z5])],[(0,[z372,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z373]),(0,[z1,z2,z3,z8,z4,z374,z5]),(0,[z1,z2,z3,z8,z33,z4,z96])]],
   [[(0,[z375,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z89,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z376]),(0,[z1,z2,z163,z8,z129,z4,z5]),(0,[z1,z2,z3,z8,z326,z4,z5])],[(0,[z377,z1,z2,z3,z8,z4,z5]),(0,[z1,z378,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z379,z5]),(0,[z1,z2,z3,z19,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z380,z5]),(0,[z1,z2,z3,z36,z4,z5,z6]),(0,[z90,z1,z2,z3,z8,z33,z5])],[(0,[z281,z1,z2,z92,z8,z4,z5])],[(0,[z1,z381,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z87,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z382])],[(0,[z1,z2,z3,z36,z34,z4,z5]),(0,[z1,z2,z3,z8,z75,z5,z91]),(0,[z1,z2,z3,z97,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z383]),(0,[z1,z2,z3,z8,z4,z384,z5]),(0,[z385,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z313,z8,z4,z5]),(0,[z1,z2,z3,z329,z8,z4,z5]),(1,[z1,z2,z8,z4,z386,z5]),(0,[z21,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z59,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z387,z4,z5]),(0,[z388,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z205])],[(0,[z0,z27,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z389,z4,z5]),(0,[z390,z1,z2,z3,z8,z4,z5]),(0,[z27,z1,z2,z3,z187,z4,z5]),(0,[z1,z2,z3,z8,z47,z5,z91]),(0,[z391,z1,z2,z3,z36,z4,z5])],[(0,[z1,z2,z3,z8,z392,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z393]),(0,[z1,z2,z3,z8,z4,z394,z5])]],
   [[(0,[z76,z217,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z395,z8,z4,z5]),(0,[z170,z2,z3,z8,z4,z98,z5]),(0,[z396,z1,z2,z3,z8,z4,z5]),(1,[z1,z258,z3,z8,z4,z259]),(1,[z1,z2,z163,z8,z129,z5])],[(0,[z1,z2,z3,z8,z4,z397,z5]),(1,[z1,z2,z3,z329,z4,z5]),(0,[z30,z1,z2,z3,z24,z4,z5]),(0,[z1,z2,z398,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z399])],[(0,[z400,z1,z2,z3,z8,z4,z5]),(1,[z294,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z52,z36,z4,z5]),(0,[z133,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z401,z8,z4,z5]),(0,[z1,z2,z3,z402,z8,z4,z5])],[(0,[z273,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z8,z4,z343,z138,z5])],[(0,[z1,z2,z3,z8,z4,z403,z5]),(0,[z1,z2,z3,z8,z404,z4,z5]),(0,[z1,z405,z2,z3,z8,z4,z5]),(0,[z68,z1,z2,z3,z69,z4,z5]),(0,[z1,z2,z3,z8,z4,z406,z5])],[(0,[z407,z1,z2,z3,z8,z4,z5]),(0,[z148,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z408,z4,z5]),(1,[z1,z2,z3,z4,z172,z5])],[(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z147,z4,z5]),(0,[z1,z2,z409,z3,z8,z4,z5])],[(0,[z0,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z410,z5]),(0,[z1,z2,z3,z8,z4,z47,z5]),(0,[z411,z1,z2,z3,z8,z4,z5]),(0,[z53,z1,z2,z262,z8,z4,z5]),(1,[z29,z1,z2,z8,z165,z5]),(0,[z412,z1,z2,z3,z8,z4,z5]),(0,[z156,z1,z2,z3,z8,z4,z5]),(0,[z1,z413,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z1,z2,z3,z8,z4,z5]),(0,[z62,z27,z1,z2,z3,z4,z5])],[(0,[z1,z414,z2,z3,z8,z4,z5]),(0,[z0,z68,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z415])],[(1,[z1,z15,z3,z8,z4,z5]),(0,[z14,z1,z2,z163,z3,z8,z5]),(0,[z1,z2,z3,z416,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z417,z5]),(0,[z7,z1,z2,z3,z78,z4,z5]),(0,[z1,z2,z3,z4,z5,z9,z6]),(1,[z1,z2,z59,z69,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z418])],[(0,[z419,z1,z2,z3,z8,z4,z5]),(0,[z14,z1,z2,z3,z36,z4,z5]),(0,[z39,z1,z2,z3,z36,z4,z5]),(0,[z35,z1,z2,z3,z4,z5,z6]),(1,[z26,z1,z2,z3,z138,z5]),(0,[z420,z1,z2,z3,z8,z4,z5])],[(0,[z300,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z38,z5,z91]),(0,[z1,z2,z3,z421,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z422]),(0,[z1,z2,z3,z8,z4,z5,z423])],[(0,[z1,z2,z3,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z424,z5]),(0,[z425,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z426,z5]),(1,[z1,z2,z3,z147,z137,z5]),(0,[z427,z1,z2,z3,z8,z4,z5])],[(0,[z76,z2,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z428,z4,z5]),(0,[z1,z2,z3,z8,z4,z429,z5]),(0,[z173,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z430,z4,z5]),(0,[z1,z18,z2,z3,z36,z4,z5])],[(0,[z1,z2,z3,z8,z34,z4,z5]),(0,[z62,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z431]),(0,[z85,z1,z2,z46,z8,z4,z5]),(1,[z432,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z225])],[(0,[z1,z2,z3,z433,z8,z4,z5]),(0,[z434,z1,z2,z3,z8,z4,z5]),(0,[z1,z435,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z423,z6]),(0,[z1,z2,z3,z8,z4,z5,z436])],[(0,[z437,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z438,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z302,z4,z5]),(0,[z1,z2,z3,z439,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z11])],[(0,[z85,z76,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z252,z4,z5]),(1,[z53,z1,z3,z8,z4,z115]),(0,[z26,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z440,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z441,z5]),(0,[z1,z2,z46,z196,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z283]),(0,[z29,z26,z1,z2,z3,z8,z5])],[(0,[z442,z1,z2,z3,z8,z4,z5]),(0,[z279,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z8,z4,z6])],[(0,[z68,z62,z1,z2,z3,z4,z5]),(0,[z1,z2,z443,z3,z8,z4,z5]),(0,[z68,z1,z3,z8,z4,z259,z5]),(0,[z444,z1,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z2,z3,z92,z8,z4,z5]),(0,[z221,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z445]),(0,[z27,z1,z2,z3,z8,z4,z5]),(0,[z1,z258,z2,z3,z36,z4,z5])],[(0,[z300,z1,z2,z74,z3,z4,z5]),(0,[z446,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z447,z8,z4,z5]),(0,[z448,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z449,z8,z4,z5])],[(0,[z1,z2,z3,z8,z450,z4,z5]),(0,[z1,z2,z451,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z452]),(0,[z29,z1,z113,z2,z8,z4,z5]),(0,[z1,z453,z2,z3,z8,z4,z5]),(1,[z1,z2,z3,z361,z4,z5])],[(0,[z66,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z454,z4,z5]),(0,[z1,z2,z3,z8,z455,z4,z5]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z3,z8,z456,z4,z5]),(0,[z457,z1,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z8,z4,z165,z5]),(0,[z1,z2,z3,z8,z4,z5,z458]),(0,[z1,z2,z3,z8,z459,z4,z5])],[(1,[z1,z2,z460,z8,z4,z5]),(0,[z1,z2,z3,z461,z8,z4,z5]),(0,[z26,z1,z2,z3,z8,z138,z5]),(0,[z1,z2,z3,z8,z4,z462,z5])],[(0,[z1,z2,z3,z36,z75,z4,z5]),(0,[z1,z2,z463,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z464,z5]),(0,[z1,z2,z3,z36,z4,z5,z31]),(0,[z1,z2,z3,z465,z36,z4,z5])],[(1,[z1,z2,z3,z338,z8,z5]),(0,[z27,z1,z3,z43,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z87,z5]),(1,[z1,z2,z3,z4,z5,z466]),(1,[z1,z2,z3,z449,z4,z5])],[(0,[z76,z1,z258,z3,z8,z4,z5]),(0,[z1,z2,z3,z187,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z467,z5])]],
   [[(0,[z1,z2,z3,z468,z8,z4,z5]),(0,[z469,z1,z2,z3,z92,z4,z5]),(0,[z27,z1,z2,z3,z137,z4,z5]),(0,[z1,z2,z3,z8,z4,z470,z5]),(0,[z1,z2,z3,z4,z5,z6,z91]),(0,[z1,z2,z3,z36,z471,z4,z5]),(0,[z1,z2,z3,z8,z4,z472,z5])],[(0,[z473,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z193,z8,z4,z5,z31]),(0,[z161,z1,z2,z3,z8,z19,z5]),(0,[z1,z2,z3,z8,z4,z5,z474]),(0,[z1,z2,z3,z8,z4,z5,z475]),(0,[z1,z2,z3,z36,z4,z476,z5])],[(0,[z1,z2,z193,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z477,z5]),(0,[z1,z2,z478,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z11,z6])],[(0,[z479,z1,z2,z3,z8,z4,z5]),(0,[z1,z142,z2,z3,z8,z4,z5])],[(0,[z62,z2,z3,z112,z8,z4,z5]),(0,[z1,z2,z3,z36,z137,z4,z5])],[(1,[z1,z2,z3,z8,z5,z130]),(0,[z1,z2,z480,z3,z8,z4,z5]),(0,[z1,z481,z2,z3,z8,z4,z5]),(0,[z1,z2,z8,z129,z4,z165,z5])],[(0,[z1,z2,z3,z482,z8,z4,z5]),(0,[z1,z2,z3,z483,z8,z4,z5]),(0,[z1,z2,z3,z75,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z484,z5])],[(0,[z485,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z4,z5]),(0,[z90,z1,z2,z3,z8,z4,z96]),(0,[z1,z2,z322,z8,z4,z96,z5])]],
   [[(0,[z486,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z487,z8,z4,z5]),(0,[z1,z488,z2,z3,z8,z4,z5]),(1,[z489,z2,z3,z8,z4,z5]),(0,[z53,z1,z3,z8,z4,z5,z115]),(1,[z106,z2,z3,z8,z4,z5])],[(0,[z281,z158,z2,z3,z8,z4,z5]),(0,[z490,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z98,z5]),(0,[z90,z1,z2,z3,z361,z4,z5]),(1,[z1,z2,z322,z8,z4,z5])],[(0,[z1,z2,z3,z491,z8,z4,z5]),(0,[z1,z2,z3,z492,z8,z4,z5]),(0,[z493,z1,z2,z3,z8,z4,z5]),(0,[z494,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z495,z4,z5])],[(1,[z1,z235,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z496,z5]),(0,[z1,z2,z3,z8,z497,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z498]),(0,[z1,z2,z163,z3,z8,z33,z5])],[(0,[z1,z2,z3,z8,z4,z5,z499]),(0,[z500,z1,z2,z3,z8,z4,z5]),(0,[z161,z432,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z241,z8,z4,z5]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z1,z501,z2,z3,z8,z4,z5])],[(0,[z469,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z67,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z502]),(1,[z1,z2,z3,z8,z162,z5]),(0,[z1,z2,z3,z43,z36,z4,z5]),(0,[z503,z1,z2,z3,z4,z165,z5]),(0,[z1,z2,z163,z3,z147,z8,z5]),(0,[z1,z2,z3,z8,z317,z4,z5]),(0,[z504,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z196,z92,z8,z4,z5]),(1,[z68,z1,z3,z239,z4,z5]),(0,[z1,z18,z2,z3,z8,z4,z5]),(0,[z53,z1,z2,z3,z186,z4,z5]),(0,[z30,z1,z2,z3,z312,z4,z5])],[(0,[z1,z505,z2,z3,z8,z4,z5]),(0,[z68,z1,z2,z3,z187,z4,z5]),(0,[z1,z2,z3,z506,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z507,z5]),(0,[z1,z2,z3,z8,z508,z4,z5])]],
   [[(0,[z1,z2,z3,z8,z509,z4,z5]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z29,z85,z1,z2,z8,z4,z5]),(0,[z53,z1,z46,z3,z8,z4,z5]),(1,[z1,z2,z3,z312,z4,z5])],[(0,[z0,z62,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z38,z5]),(0,[z1,z2,z3,z8,z510,z4,z5]),(0,[z1,z2,z511,z3,z8,z4,z5]),(0,[z29,z1,z2,z3,z147,z8,z5]),(0,[z1,z2,z3,z8,z305,z4,z5])],[(0,[z1,z2,z3,z8,z75,z4,z5]),(0,[z1,z2,z3,z8,z4,z512,z5]),(0,[z1,z2,z3,z8,z4,z5,z513]),(0,[z1,z2,z3,z8,z4,z514,z5]),(0,[z1,z2,z3,z8,z4,z5,z31]),(0,[z1,z2,z3,z8,z4,z5,z515])],[(0,[z281,z1,z2,z3,z8,z4,z5]),(0,[z1,z18,z3,z8,z4,z47,z5]),(0,[z1,z2,z3,z8,z4,z5,z516]),(0,[z1,z2,z3,z4,z259,z5,z6]),(0,[z1,z2,z517,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z518]),(0,[z1,z2,z3,z8,z519,z4,z5]),(0,[z29,z1,z2,z3,z8,z5,z91])],[(0,[z1,z2,z3,z8,z4,z520,z5]),(0,[z521,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z522,z4,z5]),(0,[z289,z1,z2,z3,z8,z4,z5]),(0,[z523,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z69,z8,z129,z4,z5]),(0,[z1,z524,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z525]),(0,[z1,z2,z3,z8,z4,z526,z5]),(0,[z527,z1,z2,z3,z8,z4,z5]),(0,[z1,z258,z2,z3,z8,z4,z5]),(0,[z279,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z476,z5])],[(1,[z14,z2,z3,z8,z38,z5]),(0,[z1,z2,z528,z3,z8,z4,z5]),(0,[z432,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z529,z3,z8,z4,z5]),(0,[z30,z1,z2,z3,z8,z4,z87])]],
   [[(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z2,z3,z8,z530,z4,z5]),(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z196,z3,z8,z4,z87])],[(0,[z226,z1,z2,z3,z8,z4,z5]),(0,[z85,z1,z2,z3,z36,z4,z5]),(0,[z68,z1,z2,z3,z239,z4,z5]),(0,[z1,z2,z3,z8,z137,z4,z5])],[(0,[z531,z1,z2,z3,z8,z4,z5]),(0,[z1,z532,z2,z3,z8,z4,z5]),(0,[z7,z14,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z533,z8,z4,z5]),(1,[z39,z2,z3,z8,z75,z5]),(0,[z7,z2,z3,z8,z75,z4,z5]),(0,[z534,z1,z2,z3,z8,z4,z5]),(0,[z535,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z259,z5,z283]),(0,[z536,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z537,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z138,z5]),(0,[z1,z2,z3,z8,z4,z538,z5])],[(0,[z66,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z539,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z540,z5]),(1,[z131,z1,z2,z3,z4,z5]),(0,[z35,z1,z2,z8,z129,z4,z5]),(0,[z1,z2,z3,z465,z8,z4,z5])],[(0,[z541,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z542,z5]),(0,[z543,z1,z2,z3,z8,z4,z5]),(0,[z544,z1,z2,z3,z8,z4,z5]),(1,[z545,z1,z2,z8,z4,z5])],[(0,[z546,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z8,z197,z4,z5])],[(0,[z1,z2,z3,z8,z547,z4,z5]),(0,[z7,z1,z2,z460,z8,z4,z5]),(0,[z1,z2,z3,z8,z213,z4,z5]),(0,[z1,z2,z3,z8,z4,z98,z5]),(0,[z548,z1,z2,z3,z8,z4,z5]),(0,[z549,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z550,z8,z4,z5]),(0,[z551,z1,z2,z3,z8,z4,z5]),(0,[z1,z552,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z96,z5])],[(0,[z66,z217,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z553,z5]),(0,[z554,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z7,z170,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z2,z193,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z555]),(0,[z1,z2,z3,z8,z4,z556,z5])],[(0,[z76,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z36,z4,z259,z5]),(0,[z1,z2,z163,z3,z8,z165,z5]),(0,[z90,z1,z2,z3,z8,z5,z91])],[(1,[z217,z74,z3,z8,z4,z5]),(0,[z557,z1,z2,z3,z8,z4,z5]),(0,[z558,z1,z2,z3,z8,z4,z5])],[(0,[z281,z2,z3,z92,z8,z4,z5]),(1,[z1,z2,z3,z105,z4,z5]),(0,[z161,z489,z2,z3,z8,z4,z5]),(0,[z559,z1,z2,z3,z8,z4,z5])],[(0,[z1,z560,z2,z3,z8,z4,z5]),(0,[z1,z2,z262,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z561,z5])],[(0,[z1,z2,z2,z3,z8,z4,z5]),(0,[z66,z14,z2,z3,z8,z4,z5]),(0,[z66,z2,z3,z8,z75,z4,z5]),(1,[z469,z1,z2,z3,z4,z5]),(0,[z1,z2,z562,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z563,z4,z5]),(1,[z1,z2,z3,z564,z4,z5]),(0,[z29,z1,z2,z3,z8,z165,z5]),(0,[z1,z2,z3,z4,z5,z31,z6]),(0,[z26,z1,z2,z3,z8,z137,z5])],[(0,[z76,z1,z2,z3,z8,z428,z5]),(0,[z565,z1,z2,z3,z8,z4,z5]),(1,[z158,z2,z193,z8,z4,z5]),(0,[z158,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z38,z5]),(0,[z1,z2,z3,z8,z4,z566,z5]),(0,[z567,z1,z2,z3,z8,z4,z5]),(1,[z1,z2,z3,z24,z4,z5])],[(0,[z1,z2,z568,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z569,z4,z5]),(0,[z1,z2,z3,z570,z8,z4,z5]),(1,[z1,z2,z350,z8,z4,z5]),(0,[z1,z258,z3,z8,z4,z259,z5])]],
   [[(0,[z1,z2,z3,z8,z571,z4,z5]),(0,[z1,z2,z59,z3,z137,z4,z5]),(0,[z1,z2,z3,z8,z4,z172,z5]),(0,[z1,z2,z163,z3,z36,z4,z5]),(0,[z1,z2,z3,z36,z129,z4,z5]),(0,[z30,z1,z2,z3,z36,z4,z5]),(0,[z572,z1,z2,z3,z8,z4,z5])],[(0,[z1,z573,z2,z3,z8,z4,z5]),(1,[z1,z324,z3,z8,z4,z5]),(0,[z68,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z239,z4,z5,z6]),(0,[z161,z1,z18,z3,z8,z4,z5]),(0,[z1,z2,z196,z3,z36,z4,z5])],[(0,[z66,z170,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z574,z5]),(0,[z1,z2,z3,z8,z575,z4,z5]),(0,[z1,z2,z3,z8,z576,z4,z5]),(0,[z577,z1,z2,z3,z8,z4,z5])],[(0,[z66,z1,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z578,z5]),(0,[z1,z579,z2,z3,z8,z4,z5]),(0,[z580,z1,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z8,z4,z5,z31])],[(0,[z158,z1,z67,z3,z8,z4,z5]),(0,[z158,z1,z2,z193,z8,z4,z5]),(0,[z581,z1,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z3,z36,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z582]),(0,[z14,z1,z2,z3,z8,z47,z5]),(0,[z39,z1,z2,z3,z8,z47,z5]),(0,[z39,z1,z2,z163,z3,z8,z5]),(0,[z1,z2,z3,z8,z4,z343,z5])],[(0,[z1,z2,z3,z338,z92,z8,z5]),(0,[z1,z2,z3,z8,z4,z5,z583]),(0,[z1,z2,z3,z8,z4,z584,z5]),(1,[z90,z1,z2,z3,z8,z91]),(0,[z1,z2,z3,z8,z4,z5,z585])],[(1,[z1,z2,z3,z8,z428,z5]),(0,[z7,z1,z2,z3,z8,z162,z5]),(0,[z1,z2,z3,z8,z4,z138,z5])]],
   [[(0,[z1,z2,z3,z8,z586,z4,z5]),(0,[z1,z2,z3,z587,z8,z4,z5]),(0,[z1,z2,z3,z588,z8,z4,z5])],[(0,[z589,z1,z2,z3,z8,z4,z5]),(0,[z590,z1,z2,z3,z8,z4,z5]),(0,[z68,z1,z2,z3,z137,z4,z5]),(1,[z1,z18,z3,z8,z47,z5]),(0,[z1,z18,z2,z3,z8,z47,z5]),(0,[z1,z2,z3,z8,z4,z591,z5]),(0,[z592,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z6])],[(0,[z1,z593,z2,z3,z8,z4,z5]),(0,[z62,z1,z2,z3,z34,z4,z5]),(1,[z7,z2,z3,z8,z4,z9]),(0,[z1,z113,z2,z3,z8,z4,z5]),(0,[z161,z1,z3,z8,z19,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z594]),(0,[z1,z2,z3,z595,z8,z4,z5])],[(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z19,z33,z5]),(0,[z1,z2,z3,z147,z8,z4,z5]),(0,[z219,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z517,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z96,z5]),(0,[z1,z2,z3,z8,z4,z596,z5])],[(1,[z221,z1,z2,z3,z8,z5]),(0,[z597,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z180,z5])],[(0,[z1,z2,z3,z8,z4,z598,z5]),(0,[z1,z2,z8,z129,z4,z5,z31]),(0,[z26,z1,z2,z3,z4,z138,z5]),(0,[z1,z2,z3,z8,z4,z5,z599]),(1,[z1,z2,z8,z4,z5,z382])],[(0,[z600,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z601,z3,z8,z4,z5]),(0,[z602,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z259,z5]),(0,[z1,z2,z3,z8,z4,z603,z5]),(0,[z1,z258,z2,z3,z4,z5,z6])],[(0,[z604,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z74,z3,z36,z4,z5]),(1,[z1,z2,z3,z8,z213,z5]),(0,[z1,z2,z3,z8,z4,z5,z605]),(0,[z85,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z606,z5]),(0,[z1,z2,z8,z4,z386,z47,z5]),(0,[z1,z2,z3,z36,z8,z4,z180])]],
   [[(0,[z1,z2,z3,z564,z8,z4,z5])],[(0,[z1,z2,z607,z3,z8,z4,z5]),(0,[z1,z2,z608,z3,z8,z4,z5]),(0,[z90,z1,z2,z3,z36,z4,z5])],[(0,[z49,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z609,z8,z4,z5]),(0,[z1,z2,z3,z610,z8,z4,z5]),(0,[z1,z3,z43,z8,z239,z4,z5]),(0,[z611,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z612,z4,z5]),(1,[z327,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z38,z5,z6]),(0,[z190,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z613,z4,z5]),(0,[z1,z2,z3,z147,z137,z4,z5])],[(0,[z1,z2,z3,z614,z8,z4,z5]),(0,[z1,z2,z46,z3,z208,z4,z5]),(0,[z615,z1,z2,z3,z8,z4,z5]),(0,[z616,z1,z2,z3,z8,z4,z5]),(0,[z503,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z617,z4,z5]),(0,[z618,z1,z2,z3,z8,z4,z5]),(0,[z1,z619,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z620])],[(0,[z217,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z42])],[(0,[z76,z1,z2,z3,z8,z4,z5]),(0,[z170,z1,z2,z3,z8,z4,z98]),(0,[z1,z2,z621,z3,z8,z4,z5]),(0,[z1,z2,z622,z3,z8,z4,z5]),(1,[z1,z2,z3,z8,z5,z88]),(0,[z1,z623,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z228,z6]),(0,[z391,z1,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z2,z3,z8,z75,z4,z98,z5]),(0,[z1,z2,z3,z624,z8,z4,z5]),(0,[z1,z625,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z386,z5]),(0,[z1,z2,z59,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z626,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z515]),(0,[z1,z2,z3,z8,z4,z5,z466])],[(0,[z1,z2,z3,z8,z4,z5,z627]),(0,[z1,z2,z460,z3,z8,z4,z5]),(0,[z7,z1,z2,z3,z8,z4,z98]),(0,[z27,z1,z2,z3,z43,z4,z5]),(0,[z628,z1,z2,z3,z8,z4,z5]),(0,[z1,z629,z2,z3,z8,z4,z5])],[(0,[z1,z74,z3,z8,z4,z5,z115]),(0,[z7,z1,z2,z3,z389,z4,z5]),(0,[z1,z2,z3,z52,z8,z4,z5]),(0,[z53,z1,z258,z3,z8,z4,z5]),(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z518])],[(0,[z76,z1,z3,z8,z4,z47,z5]),(0,[z29,z39,z1,z2,z3,z8,z5]),(0,[z1,z113,z2,z52,z8,z4,z5])],[(0,[z1,z2,z3,z630,z8,z4,z5]),(1,[z503,z1,z2,z3,z4,z5])],[(0,[z1,z258,z74,z3,z8,z4,z5]),(0,[z49,z1,z2,z74,z3,z4,z5]),(0,[z30,z1,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z631,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z632]),(0,[z1,z2,z633,z3,z8,z4,z5]),(1,[z35,z1,z2,z187,z4,z5]),(0,[z1,z2,z196,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z33,z4,z91]),(0,[z634,z1,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z635,z2,z3,z8,z4,z5]),(0,[z0,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z636]),(0,[z85,z1,z3,z8,z4,z259,z5]),(0,[z1,z2,z3,z8,z4,z637,z5]),(0,[z1,z2,z638,z3,z8,z4,z5])],[(0,[z639,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z640,z5]),(0,[z226,z158,z1,z3,z8,z4,z5]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z69,z8,z187,z4,z5]),(0,[z1,z2,z3,z8,z4,z180,z5])],[(0,[z1,z74,z3,z43,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z101]),(0,[z641,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z33,z47,z5]),(0,[z29,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z642,z5])],[(0,[z1,z74,z46,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z643,z4,z5]),(0,[z7,z1,z324,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z5,z9]),(0,[z580,z1,z2,z3,z4,z5,z6])],[(0,[z644,z1,z2,z3,z8,z4,z5])],[(0,[z645,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z150,z5]),(0,[z1,z2,z646,z3,z8,z4,z5]),(0,[z14,z1,z2,z3,z8,z4,z5]),(0,[z39,z1,z2,z3,z8,z4,z5]),(0,[z647,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z648,z3,z8,z4,z5]),(0,[z35,z29,z1,z2,z8,z4,z5])],[(0,[z158,z1,z2,z92,z8,z4,z5]),(0,[z1,z2,z3,z649,z8,z4,z5])],[(0,[z217,z2,z74,z3,z8,z4,z5]),(1,[z0,z2,z3,z34,z4,z5]),(0,[z1,z2,z3,z650,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z651]),(0,[z1,z2,z163,z3,z8,z129,z5]),(0,[z2,z3,z8,z4,z5,z107,z91])]],
   [[(0,[z1,z2,z3,z8,z652,z4,z5]),(0,[z1,z2,z46,z8,z4,z5,z31]),(0,[z1,z2,z3,z8,z4,z653,z5]),(0,[z1,z2,z3,z654,z8,z4,z5]),(0,[z1,z2,z3,z277,z36,z4,z5])],[(0,[z655,z1,z2,z3,z8,z4,z5]),(0,[z0,z2,z3,z8,z34,z4,z5]),(0,[z90,z39,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z130,z9]),(0,[z656,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z46,z3,z36,z4,z5]),(0,[z1,z2,z3,z241,z4,z87,z5]),(0,[z219,z1,z2,z3,z8,z4,z5]),(0,[z280,z1,z2,z3,z36,z4,z5])],[(0,[z62,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z657,z8,z4,z5]),(0,[z1,z113,z2,z3,z4,z5,z6]),(0,[z1,z3,z8,z4,z259,z5,z115]),(0,[z1,z2,z3,z36,z4,z5,z115]),(0,[z1,z2,z3,z658,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z659,z5]),(0,[z1,z2,z3,z36,z254,z4,z5])],[(0,[z294,z1,z2,z3,z8,z4,z5]),(0,[z660,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z661,z4,z5]),(0,[z1,z2,z3,z8,z662,z4,z5]),(0,[z29,z1,z2,z3,z8,z129,z5]),(0,[z1,z2,z163,z3,z8,z5,z91]),(0,[z663,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z147,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z664])],[(0,[z2,z3,z112,z8,z34,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z99]),(0,[z1,z2,z3,z64,z8,z4,z5]),(0,[z665,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z666,z8,z4,z5]),(0,[z1,z2,z3,z8,z667,z4,z5]),(0,[z1,z2,z668,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z291,z1,z2,z3,z36,z4,z5])],[(0,[z1,z2,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z669,z4,z5]),(0,[z85,z1,z3,z52,z8,z4,z5]),(0,[z1,z2,z670,z3,z8,z4,z5]),(0,[z1,z2,z3,z69,z36,z4,z5]),(0,[z1,z2,z3,z36,z33,z4,z5])],[(0,[z1,z2,z3,z4,z98,z5,z6]),(0,[z1,z671,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z672,z5]),(0,[z1,z2,z3,z8,z4,z87,z5])],[(0,[z1,z2,z673,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z674]),(0,[z90,z1,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z2,z3,z8,z4,z675,z5]),(0,[z2,z3,z8,z4,z98,z5,z9]),(1,[z1,z2,z3,z208,z4,z5]),(0,[z1,z2,z676,z3,z8,z4,z5]),(0,[z26,z1,z2,z59,z3,z4,z5]),(0,[z1,z2,z3,z8,z471,z4,z5])],[(0,[z68,z1,z74,z3,z8,z4,z5]),(0,[z170,z1,z2,z3,z8,z4,z9]),(0,[z1,z2,z196,z52,z8,z4,z5]),(0,[z53,z68,z1,z3,z8,z4,z5]),(1,[z1,z3,z8,z4,z5,z11]),(0,[z1,z2,z307,z3,z36,z4,z5])],[(0,[z170,z2,z74,z3,z8,z4,z5]),(0,[z0,z1,z2,z3,z112,z4,z5]),(0,[z1,z2,z3,z8,z4,z677,z5])],[(0,[z53,z1,z2,z3,z8,z4,z259]),(0,[z1,z2,z3,z147,z8,z138,z5])],[(0,[z678,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z679]),(0,[z1,z2,z3,z8,z4,z680,z5]),(0,[z1,z2,z3,z8,z4,z681,z5]),(0,[z1,z2,z3,z8,z682,z4,z5]),(1,[z1,z2,z3,z8,z224,z5])],[(0,[z683,z1,z2,z3,z8,z4,z5]),(0,[z684,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z685,z5]),(0,[z53,z85,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z564,z4,z259,z5]),(0,[z1,z686,z2,z3,z8,z4,z5])],[(0,[z1,z2,z687,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z688,z4,z5]),(0,[z689,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z690]),(0,[z545,z1,z2,z8,z4,z47,z5]),(0,[z1,z2,z3,z8,z691,z4,z5]),(0,[z1,z2,z3,z8,z4,z5,z125]),(0,[z1,z2,z3,z449,z4,z96,z5])],[(0,[z1,z2,z3,z33,z4,z5,z6])]],
   [[(0,[z692,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z693,z4,z5])],[(1,[z1,z142,z3,z8,z4,z5]),(0,[z1,z2,z3,z64,z4,z98,z5]),(0,[z1,z2,z3,z8,z4,z5,z694]),(0,[z53,z21,z2,z3,z8,z4,z5]),(1,[z1,z2,z3,z8,z164,z5]),(0,[z1,z2,z8,z4,z96,z5,z382])],[(0,[z1,z2,z3,z695,z8,z4,z5]),(0,[z53,z1,z2,z350,z8,z4,z5]),(0,[z1,z2,z59,z69,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z696,z5]),(0,[z1,z2,z8,z4,z87,z5,z31]),(0,[z1,z2,z3,z8,z4,z697,z5])],[(0,[z161,z76,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z1,z46,z3,z8,z4,z259,z5]),(0,[z698,z1,z2,z3,z8,z4,z5])],[(0,[z62,z1,z2,z3,z112,z4,z5]),(0,[z1,z2,z3,z8,z389,z4,z5]),(0,[z1,z2,z3,z699,z8,z4,z5]),(0,[z700,z1,z2,z3,z8,z4,z5]),(0,[z701,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z702,z4,z5]),(0,[z1,z2,z3,z8,z4,z703,z5]),(0,[z30,z1,z2,z3,z8,z4,z31]),(0,[z704,z1,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z96,z5,z466])],[(0,[z14,z1,z2,z3,z8,z19,z5]),(0,[z545,z1,z2,z3,z8,z4,z5]),(0,[z1,z489,z2,z3,z8,z4,z5]),(0,[z53,z1,z2,z3,z36,z4,z5]),(0,[z1,z2,z196,z3,z8,z4,z31]),(0,[z1,z2,z3,z705,z8,z4,z5])],[(1,[z62,z2,z3,z112,z4,z5]),(0,[z1,z2,z3,z8,z105,z4,z5]),(0,[z30,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z4,z5,z706]),(0,[z1,z2,z3,z8,z4,z5,z115]),(0,[z1,z2,z196,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z5,z707]),(0,[z1,z2,z3,z708,z4,z5]),(0,[z1,z2,z709,z8,z4,z5]),(1,[z2,z3,z8,z4,z710]),(0,[z711,z2,z3,z8,z4,z5])],[],[(0,[z1,z2,z712,z8,z4,z5]),(0,[z1,z2,z3,z713,z4,z5]),(0,[z714,z1,z3,z8,z4,z5])],[(0,[z300,z217,z74,z3,z4,z5]),(0,[z1,z2,z3,z8,z715,z5]),(0,[z1,z2,z3,z8,z716,z5]),(0,[z1,z2,z717,z8,z4,z5]),(0,[z53,z1,z3,z8,z4,z452]),(0,[z1,z3,z718,z4,z5,z125]),(0,[z1,z2,z3,z224,z5,z6]),(0,[z1,z3,z719,z4,z5,z6]),(0,[z1,z2,z3,z36,z720,z5]),(0,[z721,z1,z2,z36,z4,z5]),(1,[z1,z2,z3,z8,z722]),(0,[z1,z2,z3,z8,z96,z722])],[(0,[z1,z723,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z5,z724]),(0,[z68,z1,z3,z4,z5,z283]),(0,[z1,z2,z8,z4,z725,z5])],[(0,[z281,z2,z12,z92,z4,z5]),(0,[z158,z2,z193,z4,z5,z6]),(0,[z62,z2,z3,z726,z4,z5]),(0,[z21,z2,z3,z4,z5,z6])],[(0,[z0,z671,z2,z3,z4,z5]),(0,[z170,z2,z3,z4,z98,z6]),(0,[z1,z3,z8,z727,z47,z5]),(0,[z21,z2,z262,z8,z4,z5]),(0,[z1,z2,z350,z4,z5,z6]),(0,[z1,z3,z8,z4,z5,z728]),(0,[z729,z1,z3,z8,z4,z5])],[(0,[z1,z2,z3,z338,z12,z5]),(0,[z1,z2,z3,z8,z730,z5])]],
   [[(0,[z0,z279,z1,z3,z4,z5]),(0,[z1,z2,z3,z731,z4,z5]),(0,[z1,z18,z3,z8,z727,z5])],[(0,[z1,z2,z3,z8,z732,z5]),(0,[z1,z2,z3,z733,z4,z5]),(0,[z1,z2,z3,z734,z4,z5]),(0,[z1,z2,z3,z5,z735,z6])],[(0,[z364,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z736,z4,z5]),(0,[z1,z2,z737,z8,z4,z5]),(0,[z1,z2,z3,z8,z33,z159]),(0,[z1,z2,z8,z4,z738,z5]),(0,[z273,z1,z350,z8,z4,z5]),(0,[z1,z2,z262,z36,z4,z5]),(0,[z1,z2,z163,z8,z5,z109]),(0,[z1,z2,z3,z36,z4,z201]),(0,[z156,z1,z2,z3,z476,z5])],[(0,[z432,z2,z3,z8,z19,z5]),(0,[z21,z2,z3,z252,z4,z5]),(0,[z739,z2,z3,z8,z4,z5])],[(0,[z1,z267,z3,z8,z47,z5]),(0,[z1,z2,z3,z740,z4,z5]),(0,[z1,z288,z46,z8,z4,z5]),(0,[z27,z1,z3,z741,z4,z5]),(0,[z1,z2,z350,z252,z4,z5])],[(0,[z2,z3,z726,z34,z4,z5]),(0,[z742,z1,z15,z3,z4,z5]),(0,[z273,z1,z3,z36,z4,z5])],[(0,[z0,z2,z3,z34,z4,z5]),(0,[z68,z1,z369,z3,z4,z5]),(0,[z743,z1,z3,z8,z4,z5]),(0,[z170,z2,z3,z8,z4,z98]),(0,[z1,z2,z460,z389,z4,z5]),(0,[z1,z2,z3,z4,z200,z6]),(0,[z1,z2,z744,z8,z4,z5]),(0,[z1,z2,z4,z5,z6,z745])],[(0,[z1,z2,z3,z4,z5,z746]),(0,[z1,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z747,z4,z5]),(0,[z1,z2,z3,z4,z502,z6]),(0,[z1,z46,z8,z4,z5,z22]),(0,[z748,z1,z2,z8,z4,z5]),(0,[z1,z2,z749,z8,z4,z5]),(0,[z279,z1,z3,z36,z4,z5]),(0,[z1,z3,z36,z4,z11,z6]),(0,[z106,z750,z3,z8,z4,z5])]],
   [[(0,[z76,z432,z3,z8,z4,z5]),(0,[z751,z1,z2,z3,z4,z5]),(0,[z53,z1,z3,z329,z4,z5])],[(0,[z14,z2,z3,z8,z392,z5]),(0,[z1,z3,z8,z19,z727,z5]),(0,[z29,z273,z1,z8,z4,z5])],[(0,[z1,z2,z3,z752,z4,z5]),(0,[z1,z2,z3,z8,z753,z5]),(0,[z1,z2,z59,z395,z4,z5]),(0,[z754,z2,z3,z8,z4,z5])],[(0,[z50,z2,z3,z8,z75,z5]),(0,[z1,z2,z3,z8,z755,z5]),(0,[z68,z1,z3,z631,z4,z5]),(0,[z1,z756,z3,z8,z4,z5]),(0,[z85,z1,z52,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z757])],[(0,[z1,z2,z758,z8,z4,z5]),(0,[z1,z2,z3,z759,z4,z5]),(0,[z634,z2,z3,z8,z75,z5]),(0,[z1,z760,z2,z3,z8,z5]),(0,[z54,z2,z3,z4,z5,z6]),(0,[z29,z1,z2,z8,z653,z5]),(1,[z1,z2,z8,z4,z761]),(0,[z762,z1,z2,z4,z5,z6])],[(0,[z1,z2,z97,z4,z5,z6]),(0,[z54,z2,z262,z8,z4,z5]),(0,[z1,z2,z8,z4,z763,z5])],[(0,[z190,z2,z74,z3,z8,z5]),(0,[z764,z1,z3,z8,z4,z5]),(0,[z1,z3,z8,z4,z5,z765]),(0,[z1,z2,z3,z4,z685,z6]),(0,[z106,z2,z3,z8,z75,z5]),(0,[z1,z324,z460,z8,z4,z5]),(0,[z1,z2,z3,z766,z4,z5]),(0,[z2,z3,z8,z4,z5,z767]),(0,[z1,z2,z3,z768,z4,z5]),(0,[z1,z2,z3,z8,z33,z722])],[(0,[z1,z2,z769,z8,z4,z5]),(0,[z170,z324,z3,z8,z4,z5]),(0,[z68,z1,z3,z741,z4,z5])]],
   [[(0,[z770,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z5,z130,z6]),(0,[z771,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z241,z5,z88])],[(0,[z35,z1,z2,z495,z4,z5]),(0,[z772,z1,z2,z3,z8,z5])],[(0,[z76,z1,z3,z329,z4,z5]),(0,[z327,z1,z3,z4,z5,z6]),(0,[z1,z773,z3,z8,z4,z5]),(0,[z545,z1,z2,z8,z33,z5]),(0,[z54,z2,z3,z252,z4,z5]),(0,[z1,z2,z3,z5,z205,z88]),(0,[z1,z774,z3,z4,z5,z6]),(0,[z775,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z776])],[(0,[z74,z3,z8,z4,z5,z383]),(0,[z320,z74,z3,z8,z4,z5]),(0,[z412,z2,z92,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z777]),(0,[z1,z142,z3,z78,z4,z5]),(0,[z21,z2,z3,z8,z302,z5]),(0,[z1,z3,z8,z4,z778,z115]),(0,[z1,z2,z3,z4,z5,z779])],[(0,[z1,z2,z780,z8,z4,z5]),(0,[z1,z2,z3,z781,z4,z5]),(0,[z27,z1,z3,z43,z4,z5]),(0,[z1,z2,z350,z8,z302,z5]),(0,[z1,z2,z262,z8,z86,z5]),(0,[z782,z1,z2,z4,z5,z6]),(0,[z90,z1,z2,z3,z197,z91])],[(0,[z226,z1,z3,z8,z4,z5]),(0,[z1,z46,z783,z8,z4,z5]),(0,[z279,z1,z3,z239,z4,z5]),(0,[z161,z1,z3,z8,z19,z5]),(0,[z1,z2,z3,z784,z4,z5]),(1,[z35,z214,z1,z2,z5])],[(0,[z14,z2,z3,z8,z276,z5]),(0,[z785,z1,z2,z3,z4,z5]),(0,[z1,z786,z3,z4,z5,z6])],[(0,[z1,z2,z3,z389,z162,z5]),(0,[z1,z2,z3,z4,z5,z787]),(0,[z1,z2,z3,z36,z302,z5]),(0,[z1,z2,z4,z5,z382,z466]),(0,[z1,z2,z449,z4,z5,z382])]],
   [[(0,[z1,z142,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z788,z5]),(0,[z0,z2,z3,z726,z4,z5]),(0,[z789,z1,z3,z8,z4,z5]),(0,[z35,z1,z2,z305,z4,z5]),(0,[z1,z2,z3,z4,z5,z790])],[(0,[z1,z2,z3,z791,z4,z5]),(0,[z1,z2,z3,z8,z720,z5]),(0,[z1,z2,z3,z252,z86,z5]),(0,[z1,z3,z8,z4,z5,z778]),(0,[z214,z1,z2,z3,z8,z5]),(0,[z1,z2,z8,z4,z5,z792])],[(0,[z545,z76,z1,z8,z4,z5]),(0,[z327,z62,z3,z112,z4,z5]),(0,[z106,z2,z3,z8,z19,z5]),(0,[z1,z2,z3,z137,z374,z5])],[(0,[z1,z2,z793,z8,z4,z5]),(0,[z1,z2,z3,z8,z794,z5]),(0,[z545,z14,z1,z2,z8,z5]),(0,[z1,z783,z52,z8,z4,z5]),(0,[z1,z2,z3,z795,z4,z5])],[(0,[z281,z2,z92,z36,z4,z5]),(0,[z1,z2,z460,z8,z213,z5]),(0,[z68,z1,z3,z471,z4,z5])],[(0,[z1,z2,z3,z8,z5,z796]),(0,[z62,z2,z3,z112,z4,z5]),(0,[z1,z2,z3,z8,z797,z5]),(0,[z798,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z799,z5]),(0,[z2,z3,z4,z5,z6,z107])],[(0,[z161,z432,z3,z8,z19,z5]),(0,[z1,z2,z3,z36,z4,z6])],[(0,[z1,z800,z3,z8,z4,z5]),(0,[z1,z324,z3,z8,z162,z5]),(0,[z1,z2,z3,z801,z4,z5]),(0,[z1,z3,z329,z4,z259,z5]),(0,[z53,z1,z3,z4,z115,z6])]],
   [[(1,[z2,z802,z8,z4,z5]),(0,[z1,z2,z3,z12,z4,z5]),(0,[z803,z1,z3,z8,z4,z5]),(0,[z1,z2,z196,z8,z4,z417]),(0,[z60,z1,z2,z3,z4,z6])],[(0,[z66,z76,z3,z36,z4,z5]),(0,[z804,z1,z3,z8,z4,z5]),(0,[z2,z3,z8,z4,z710,z9]),(0,[z170,z2,z3,z4,z98,z99])],[(0,[z1,z2,z805,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z806]),(1,[z2,z3,z8,z807,z5]),(0,[z54,z2,z3,z8,z302,z5])],[(0,[z68,z300,z1,z3,z4,z5]),(0,[z1,z808,z3,z8,z4,z5]),(0,[z273,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z5,z809]),(0,[z279,z1,z3,z69,z4,z5]),(0,[z2,z3,z8,z4,z5,z810]),(0,[z289,z1,z2,z305,z4,z5])],[(0,[z1,z2,z3,z811,z4,z5]),(0,[z1,z2,z812,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z813]),(0,[z1,z2,z3,z465,z254,z5])],[(0,[z1,z3,z8,z741,z4,z5]),(0,[z1,z2,z3,z252,z4,z5]),(0,[z1,z2,z814,z8,z4,z5]),(0,[z21,z2,z3,z186,z4,z5]),(0,[z1,z2,z8,z129,z5,z210])],[(0,[z324,z3,z8,z4,z5,z9]),(0,[z1,z2,z3,z815,z4,z5]),(0,[z1,z2,z350,z186,z4,z5])],[(0,[z49,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z36,z150,z5]),(0,[z1,z258,z3,z8,z4,z441]),(0,[z1,z2,z163,z129,z5,z6]),(0,[z816,z1,z3,z8,z4,z5])]],
   [[(0,[z1,z817,z3,z8,z4,z5]),(0,[z1,z46,z350,z8,z4,z5]),(0,[z1,z3,z8,z4,z259,z339]),(0,[z818,z2,z3,z8,z4,z5]),(1,[z1,z3,z741,z4,z5]),(0,[z545,z1,z2,z105,z4,z5]),(0,[z1,z2,z819,z8,z4,z5]),(0,[z1,z820,z3,z8,z4,z5]),(0,[z30,z1,z2,z4,z31,z6])],[(0,[z1,z2,z3,z821,z4,z5]),(0,[z2,z3,z112,z726,z4,z5]),(0,[z1,z2,z822,z8,z4,z5]),(1,[z1,z3,z8,z727,z5]),(0,[z545,z131,z1,z2,z4,z5]),(0,[z1,z2,z36,z4,z343,z5])],[(0,[z281,z221,z2,z92,z8,z5]),(0,[z1,z2,z3,z338,z5,z6]),(0,[z1,z2,z3,z823,z4,z5]),(0,[z214,z68,z1,z2,z3,z5]),(0,[z391,z1,z3,z89,z4,z5]),(0,[z1,z2,z3,z36,z824,z5])],[(0,[z1,z167,z3,z8,z47,z5]),(0,[z1,z825,z3,z8,z4,z5]),(0,[z219,z279,z1,z3,z4,z6])],[(0,[z7,z190,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z826,z5]),(0,[z1,z2,z3,z86,z5,z6]),(0,[z827,z2,z3,z8,z4,z5]),(0,[z29,z1,z2,z8,z55,z5])],[(0,[z300,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z8,z828,z5]),(0,[z1,z2,z3,z829,z4,z5]),(0,[z830,z1,z3,z8,z4,z5])],[(0,[z191,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z831,z4,z5]),(0,[z1,z2,z3,z8,z5,z832])],[(0,[z14,z2,z3,z8,z497,z5]),(0,[z1,z2,z163,z8,z725,z5]),(0,[z833,z2,z3,z8,z4,z5])]],
   [[(0,[z1,z2,z36,z834,z4,z5])],[(0,[z1,z2,z835,z8,z4,z5]),(0,[z1,z3,z36,z836,z4,z5]),(0,[z1,z2,z3,z8,z33,z96])],[(0,[z1,z2,z8,z129,z725,z5]),(0,[z1,z2,z3,z8,z722,z91])],[(0,[z1,z2,z3,z8,z837,z5]),(0,[z1,z2,z3,z4,z139,z6])],[(0,[z54,z2,z3,z186,z4,z5])],[(0,[z226,z1,z3,z4,z5,z6]),(0,[z838,z1,z2,z3,z4,z5]),(0,[z54,z3,z43,z8,z4,z5]),(0,[z1,z2,z3,z8,z302,z5]),(0,[z1,z18,z3,z47,z5,z6]),(0,[z1,z2,z3,z839,z4,z5]),(0,[z1,z2,z3,z4,z180,z840])],[(0,[z551,z74,z3,z8,z4,z5]),(0,[z66,z294,z3,z8,z4,z5]),(0,[z54,z46,z3,z8,z4,z5]),(0,[z1,z258,z3,z36,z4,z259]),(0,[z1,z2,z163,z36,z129,z5]),(0,[z1,z3,z4,z5,z125,z841])],[(0,[z842,z2,z3,z8,z4,z5]),(0,[z35,z214,z1,z2,z3,z5])]],
   [[(0,[z843,z1,z2,z3,z4,z5]),(0,[z294,z1,z3,z36,z4,z5]),(0,[z207,z1,z2,z3,z8,z91]),(0,[z1,z142,z3,z4,z5,z6]),(0,[z1,z2,z3,z844,z4,z5]),(0,[z161,z1,z3,z8,z727,z5]),(0,[z214,z1,z2,z69,z8,z5]),(0,[z2,z3,z845,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z846]),(0,[z1,z2,z3,z8,z4,z847]),(0,[z751,z1,z67,z3,z4,z5]),(0,[z1,z2,z3,z848,z4,z5]),(0,[z849,z2,z3,z8,z4,z5]),(1,[z1,z3,z8,z4,z778]),(0,[z1,z2,z196,z4,z87,z205])],[(0,[z1,z2,z3,z4,z5,z850]),(0,[z1,z113,z46,z8,z4,z5]),(0,[z1,z2,z3,z851,z4,z5]),(0,[z1,z2,z3,z852,z4,z5]),(0,[z1,z2,z853,z36,z4,z5])],[(0,[z0,z405,z2,z3,z4,z5]),(0,[z1,z2,z3,z854,z4,z5]),(0,[z7,z2,z3,z8,z4,z710]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z2,z3,z186,z86,z5])],[(0,[z7,z2,z3,z389,z4,z9]),(0,[z1,z2,z36,z4,z386,z5]),(0,[z35,z214,z1,z2,z8,z5]),(0,[z219,z1,z3,z4,z11,z6])],[(0,[z294,z1,z3,z8,z428,z5]),(0,[z1,z856,z3,z8,z4,z5]),(0,[z1,z2,z3,z78,z4,z5]),(0,[z1,z18,z3,z105,z47,z5]),(0,[z29,z1,z2,z36,z165,z5])],[(0,[z411,z1,z2,z3,z8,z91]),(0,[z53,z21,z3,z8,z4,z115]),(0,[z1,z2,z8,z4,z343,z5]),(0,[z1,z2,z3,z857,z4,z5]),(0,[z1,z2,z3,z36,z4,z697])],[(0,[z66,z76,z3,z8,z4,z5]),(0,[z1,z2,z3,z858,z4,z5]),(0,[z859,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z860,z8,z4,z5]),(0,[z1,z861,z3,z8,z4,z5]),(0,[z1,z862,z2,z3,z8,z5]),(0,[z1,z15,z3,z36,z4,z5]),(0,[z1,z2,z97,z389,z4,z5]),(0,[z53,z1,z3,z8,z4,z778])],[(0,[z1,z2,z3,z863,z4,z5]),(0,[z1,z2,z3,z389,z213,z5]),(0,[z106,z2,z3,z8,z162,z5]),(0,[z1,z2,z3,z864,z4,z5]),(0,[z1,z865,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5]),(0,[z866,z1,z3,z8,z4,z5]),(0,[z1,z2,z322,z8,z33,z5])],[(0,[z291,z2,z3,z112,z4,z5]),(0,[z26,z1,z2,z3,z514,z5])],[(0,[z7,z324,z3,z8,z4,z9]),(0,[z867,z1,z2,z3,z8,z5]),(0,[z175,z1,z2,z8,z4,z5]),(0,[z29,z1,z2,z165,z5,z6]),(0,[z279,z1,z3,z36,z4,z6])],[(0,[z1,z2,z3,z8,z150,z5]),(0,[z1,z2,z8,z834,z4,z5])],[(0,[z1,z2,z3,z868,z4,z5]),(0,[z1,z142,z460,z8,z4,z5]),(0,[z1,z2,z262,z252,z4,z5]),(0,[z1,z3,z8,z836,z4,z5]),(0,[z90,z2,z3,z8,z107,z91])],[(0,[z432,z2,z3,z36,z4,z5]),(0,[z53,z1,z350,z8,z4,z115]),(0,[z1,z2,z3,z4,z380,z6]),(0,[z26,z1,z2,z3,z476,z5]),(0,[z1,z2,z3,z33,z96,z6])]],
   [[(0,[z1,z2,z3,z8,z869,z5]),(0,[z870,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z871]),(0,[z872,z2,z3,z8,z4,z5]),(0,[z873,z1,z3,z8,z4,z5]),(0,[z279,z1,z3,z4,z5,z225])],[(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z324,z3,z8,z213,z5]),(0,[z875,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z876,z5])],[(0,[z1,z2,z3,z428,z5,z6]),(0,[z190,z1,z2,z3,z8,z5]),(0,[z53,z1,z3,z36,z4,z115]),(0,[z1,z3,z8,z4,z5,z877]),(0,[z1,z2,z196,z4,z87,z6]),(0,[z279,z1,z3,z4,z5,z11])],[(0,[z1,z2,z3,z8,z878,z5]),(0,[z1,z2,z3,z8,z879,z5]),(0,[z279,z1,z3,z252,z4,z5])],[(0,[z76,z131,z1,z3,z4,z5]),(0,[z1,z880,z3,z8,z4,z5]),(0,[z881,z1,z2,z3,z4,z5]),(0,[z1,z113,z783,z8,z4,z5]),(0,[z175,z1,z2,z137,z4,z5])],[(0,[z1,z2,z3,z338,z36,z5]),(0,[z882,z1,z2,z3,z4,z5]),(0,[z1,z113,z46,z329,z4,z5]),(0,[z883,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z258,z3,z8,z4,z778]),(0,[z1,z885,z3,z8,z4,z5]),(0,[z886,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z887,z4,z5]),(0,[z279,z1,z3,z187,z4,z5]),(0,[z1,z2,z3,z197,z4,z5]),(0,[z279,z84,z1,z3,z4,z5])],[(0,[z1,z2,z3,z8,z888,z5]),(0,[z2,z3,z8,z4,z5,z710]),(0,[z214,z27,z1,z2,z3,z5])]],
   [[(0,[z1,z2,z3,z4,z889,z5]),(0,[z1,z2,z890,z8,z4,z5]),(0,[z207,z14,z2,z3,z8,z5]),(0,[z891,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z555]),(0,[z29,z1,z2,z172,z165,z5]),(0,[z26,z279,z1,z3,z4,z5]),(0,[z1,z2,z4,z343,z5,z6]),(0,[z1,z892,z3,z8,z4,z5])],[(0,[z85,z1,z622,z8,z4,z5]),(0,[z1,z2,z8,z4,z386,z5]),(0,[z1,z2,z3,z4,z5,z205])],[(0,[z1,z2,z3,z8,z893,z5]),(0,[z1,z2,z3,z894,z4,z5]),(0,[z1,z2,z460,z36,z4,z5]),(0,[z420,z1,z2,z4,z5,z42]),(0,[z2,z3,z4,z5,z6,z810]),(0,[z90,z1,z2,z3,z8,z722])],[(0,[z2,z74,z3,z8,z428,z5]),(0,[z1,z2,z3,z36,z4,z397]),(0,[z2,z3,z8,z4,z5,z895])],[(0,[z1,z2,z3,z8,z896,z5]),(0,[z1,z897,z3,z8,z4,z5]),(0,[z90,z1,z2,z3,z8,z141]),(0,[z7,z2,z3,z4,z9,z6]),(0,[z1,z258,z3,z8,z4,z259])],[(0,[z898,z1,z2,z3,z8,z4]),(0,[z85,z1,z264,z8,z4,z5]),(0,[z1,z2,z899,z8,z4,z5]),(0,[z1,z2,z3,z900,z4,z5]),(0,[z1,z2,z3,z329,z4,z5])],[(0,[z294,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z901,z4,z5]),(0,[z1,z2,z262,z8,z302,z5]),(0,[z1,z2,z196,z8,z4,z87]),(0,[z1,z2,z3,z902,z4,z5]),(0,[z1,z2,z8,z4,z87,z761]),(0,[z1,z2,z196,z8,z224,z5]),(0,[z1,z3,z8,z4,z903,z5]),(0,[z219,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z904,z8,z5]),(0,[z1,z142,z3,z8,z162,z5]),(0,[z35,z1,z2,z654,z4,z5]),(0,[z1,z2,z3,z33,z96,z466])]],
   [[(0,[z905,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z8,z906,z5]),(0,[z1,z2,z3,z4,z5,z907])],[(0,[z1,z2,z3,z908,z4,z5]),(0,[z1,z2,z3,z4,z172,z5])],[(0,[z7,z2,z460,z8,z4,z9]),(0,[z1,z3,z8,z4,z5,z909]),(0,[z1,z113,z46,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z910]),(0,[z545,z1,z2,z8,z5,z91]),(0,[z1,z255,z3,z8,z47,z5])],[(0,[z1,z2,z3,z911,z4,z5]),(0,[z1,z2,z3,z36,z5,z130]),(0,[z1,z2,z3,z912,z4,z5]),(0,[z1,z3,z8,z4,z5,z913]),(0,[z1,z2,z3,z914,z4,z5]),(0,[z1,z2,z196,z8,z4,z379]),(0,[z1,z2,z3,z252,z302,z5]),(0,[z1,z3,z8,z4,z259,z778]),(0,[z29,z1,z2,z8,z165,z5]),(0,[z1,z2,z163,z8,z667,z5])],[(0,[z915,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z916,z4,z5]),(0,[z1,z2,z3,z4,z424,z6]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z39,z2,z3,z8,z5,z399]),(0,[z39,z1,z2,z322,z8,z5]),(0,[z1,z2,z3,z918,z4,z5]),(0,[z53,z1,z3,z8,z86,z115]),(0,[z1,z2,z3,z241,z4,z5]),(0,[z106,z2,z163,z3,z8,z5]),(0,[z580,z1,z3,z4,z5,z11]),(0,[z721,z1,z2,z8,z4,z5])],[(0,[z2,z3,z8,z726,z4,z5]),(0,[z1,z2,z3,z919,z4,z5]),(0,[z1,z2,z3,z920,z4,z5]),(0,[z921,z2,z3,z8,z4,z5]),(0,[z922,z2,z3,z8,z4,z5]),(1,[z175,z26,z1,z2,z5]),(0,[z714,z1,z3,z4,z5,z6]),(0,[z1,z2,z517,z4,z5,z225])],[(0,[z923,z2,z3,z8,z4,z5]),(0,[z1,z15,z3,z8,z4,z5]),(0,[z161,z1,z3,z8,z428,z5]),(0,[z489,z2,z3,z36,z4,z5]),(0,[z106,z2,z3,z36,z4,z5])],[(0,[z66,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z924,z5]),(0,[z1,z2,z3,z925,z4,z5]),(0,[z1,z926,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z180]),(0,[z1,z2,z322,z36,z4,z5])]],
   [[(0,[z221,z1,z2,z3,z5,z6]),(0,[z927,z1,z2,z3,z4,z5]),(0,[z798,z1,z3,z4,z5,z99]),(0,[z1,z2,z928,z8,z4,z5]),(0,[z1,z2,z59,z4,z166,z5]),(0,[z26,z1,z2,z3,z138,z5])],[(0,[z1,z2,z3,z929,z4,z5]),(0,[z1,z235,z3,z36,z4,z5]),(0,[z1,z2,z3,z449,z33,z96])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z930]),(0,[z221,z1,z2,z8,z5,z31]),(0,[z85,z1,z783,z8,z4,z5])],[(0,[z1,z2,z3,z36,z162,z5]),(0,[z1,z2,z262,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z931])],[(0,[z932,z2,z3,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z933]),(0,[z1,z258,z3,z4,z259,z6]),(0,[z29,z1,z2,z8,z725,z5]),(0,[z175,z1,z2,z4,z5,z6]),(0,[z279,z1,z3,z317,z4,z5])],[(0,[z1,z934,z3,z8,z4,z5]),(0,[z1,z2,z3,z935,z4,z5]),(0,[z131,z1,z2,z4,z386,z5]),(0,[z1,z936,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z599])],[(0,[z1,z2,z3,z937,z4,z5]),(0,[z1,z2,z3,z938,z4,z5]),(0,[z1,z2,z3,z939,z8,z5]),(0,[z1,z3,z36,z4,z5,z125])],[(0,[z26,z1,z2,z223,z3,z5]),(0,[z1,z2,z3,z4,z940,z5])]],
   [[(0,[z923,z217,z3,z8,z4,z5]),(0,[z941,z1,z2,z3,z4,z5]),(0,[z1,z942,z3,z8,z4,z5]),(0,[z279,z1,z3,z8,z4,z5]),(0,[z1,z2,z69,z943,z4,z5]),(0,[z1,z2,z3,z8,z33,z240]),(0,[z559,z279,z1,z3,z4,z5]),(0,[z873,z1,z3,z4,z5,z6])],[(0,[z66,z641,z3,z8,z4,z5]),(0,[z14,z501,z2,z3,z8,z5]),(0,[z1,z2,z3,z4,z5,z283]),(0,[z175,z26,z1,z2,z3,z5]),(0,[z1,z2,z3,z4,z840,z6])],[(0,[z173,z279,z1,z3,z4,z5])],[(0,[z1,z2,z3,z8,z5,z944]),(0,[z1,z142,z3,z389,z4,z5]),(0,[z1,z2,z460,z78,z4,z5]),(0,[z7,z2,z3,z8,z162,z9]),(0,[z1,z258,z3,z4,z259,z283]),(0,[z1,z2,z3,z8,z945,z5]),(0,[z279,z1,z3,z4,z5,z518])],[(0,[z1,z2,z3,z8,z946,z5]),(0,[z1,z2,z947,z8,z4,z5]),(0,[z1,z2,z196,z8,z4,z240]),(0,[z1,z2,z3,z948,z4,z5])],[(0,[z14,z2,z3,z36,z38,z5])],[(0,[z559,z2,z3,z34,z4,z5]),(0,[z949,z2,z3,z8,z4,z5]),(0,[z1,z3,z43,z252,z4,z5]),(0,[z175,z26,z1,z2,z8,z5])],[(0,[z1,z2,z8,z4,z950,z5]),(0,[z66,z923,z3,z8,z4,z5]),(0,[z1,z2,z97,z8,z162,z5]),(0,[z1,z2,z3,z36,z4,z17]),(0,[z1,z3,z43,z4,z5,z283])]],
   [[(0,[z1,z2,z3,z951,z4,z5]),(0,[z1,z2,z460,z8,z4,z5]),(0,[z1,z2,z3,z952,z4,z5]),(0,[z27,z1,z235,z3,z4,z5]),(0,[z39,z2,z3,z36,z75,z5]),(0,[z1,z2,z3,z8,z953,z5]),(0,[z1,z2,z3,z954,z4,z5]),(0,[z1,z2,z196,z241,z4,z87]),(0,[z644,z1,z2,z3,z4,z6]),(0,[z279,z1,z3,z137,z4,z5]),(0,[z1,z892,z3,z4,z5,z6])],[(0,[z1,z3,z8,z4,z5,z955]),(0,[z1,z2,z3,z8,z956,z5]),(0,[z957,z2,z3,z8,z4,z5]),(0,[z54,z3,z8,z4,z5,z115])],[(0,[z545,z1,z2,z36,z4,z5]),(0,[z1,z2,z3,z8,z5,z958]),(0,[z1,z2,z3,z449,z4,z5]),(0,[z1,z2,z3,z4,z5,z466])],[(0,[z959,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z8,z960,z5]),(0,[z29,z1,z2,z8,z296,z5]),(0,[z1,z3,z741,z239,z4,z5])],[(0,[z372,z74,z3,z8,z4,z5]),(0,[z1,z961,z3,z8,z4,z5]),(0,[z962,z1,z2,z3,z4,z5]),(0,[z1,z2,z196,z8,z4,z761]),(1,[z1,z2,z3,z4,z840])],[(0,[z1,z963,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z964]),(0,[z85,z1,z350,z8,z4,z5]),(1,[z1,z2,z3,z965,z5]),(0,[z1,z2,z3,z4,z6,z370])],[(0,[z1,z2,z3,z8,z966,z5]),(0,[z35,z1,z2,z943,z4,z5]),(0,[z1,z2,z3,z967,z4,z5])],[(0,[z1,z2,z3,z36,z4,z632]),(0,[z1,z2,z3,z726,z4,z5]),(1,[z1,z783,z8,z4,z5]),(0,[z968,z1,z2,z8,z4,z5]),(0,[z1,z2,z3,z4,z969,z5]),(0,[z970,z1,z3,z36,z4,z5])]],
   [[(0,[z217,z74,z3,z36,z4,z5]),(0,[z1,z2,z3,z971,z4,z5]),(0,[z1,z2,z3,z8,z972,z5]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z273,z1,z52,z8,z4,z5]),(0,[z1,z2,z3,z974,z4,z5])],[(0,[z76,z656,z3,z8,z4,z5]),(0,[z1,z2,z975,z8,z4,z5]),(0,[z294,z1,z3,z8,z47,z5]),(0,[z1,z2,z3,z8,z5,z130]),(0,[z1,z2,z3,z213,z5,z6]),(0,[z2,z3,z8,z4,z98,z710]),(0,[z21,z2,z350,z8,z4,z5]),(0,[z1,z3,z4,z5,z6,z877]),(0,[z976,z1,z2,z3,z36,z5]),(0,[z1,z2,z3,z8,z5,z722]),(0,[z90,z106,z2,z3,z8,z5])],[(0,[z66,z190,z2,z3,z8,z5])],[(0,[z1,z2,z3,z977,z4,z5]),(0,[z68,z1,z235,z3,z4,z5]),(0,[z1,z2,z3,z8,z978,z5]),(0,[z1,z3,z8,z4,z5,z125]),(0,[z1,z2,z943,z187,z4,z5]),(0,[z30,z273,z1,z8,z4,z31])],[(0,[z158,z2,z193,z36,z4,z5]),(0,[z1,z2,z979,z8,z4,z5]),(0,[z1,z2,z3,z741,z4,z5]),(0,[z1,z2,z3,z980,z4,z5])],[(0,[z981,z1,z2,z3,z4,z5]),(0,[z281,z2,z92,z8,z4,z5]),(0,[z870,z1,z15,z3,z4,z5]),(0,[z982,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z727,z5]),(0,[z1,z2,z3,z983,z4,z5]),(0,[z1,z2,z350,z36,z4,z5]),(0,[z1,z2,z3,z36,z4,z507]),(0,[z922,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z36,z91])],[(0,[z1,z2,z3,z984,z4,z5])],[(0,[z985,z1,z2,z8,z4,z5]),(0,[z29,z1,z2,z260,z8,z5]),(0,[z1,z324,z3,z36,z4,z5]),(0,[z434,z1,z2,z8,z4,z31]),(0,[z84,z2,z3,z4,z5,z423])]],
   [[],[(0,[z986,z2,z3,z8,z4,z5]),(0,[z1,z2,z987,z8,z4,z5]),(0,[z988,z1,z2,z3,z4,z5])],[(0,[z76,z698,z3,z8,z4,z5]),(0,[z158,z67,z193,z8,z4,z5]),(0,[z1,z2,z3,z8,z989,z5]),(0,[z1,z2,z990,z8,z4,z5]),(0,[z1,z2,z3,z991,z4,z5]),(0,[z68,z1,z3,z239,z4,z5]),(0,[z992,z1,z2,z3,z4,z5]),(0,[z993,z1,z2,z3,z8,z5]),(0,[z2,z3,z4,z5,z6,z895]),(0,[z1,z2,z3,z4,z994,z5])],[(0,[z249,z74,z3,z8,z4,z5]),(0,[z221,z1,z2,z3,z36,z5]),(0,[z995,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z996,z8,z5]),(0,[z1,z2,z262,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z997]),(0,[z35,z1,z2,z482,z4,z5]),(0,[z1,z2,z998,z8,z4,z5]),(0,[z148,z2,z3,z326,z4,z5])],[(0,[z66,z76,z3,z8,z150,z5]),(0,[z1,z2,z3,z36,z428,z5]),(0,[z1,z999,z2,z3,z8,z5]),(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1,z1001,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z99]),(0,[z1,z2,z3,z1002,z4,z5]),(0,[z53,z1,z3,z8,z4,z146])],[(0,[z1,z2,z3,z8,z4,z710]),(0,[z1,z2,z3,z8,z1003,z5]),(0,[z273,z1,z3,z4,z5,z6]),(0,[z772,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1004,z4,z5]),(0,[z1,z18,z3,z36,z47,z5])]],
   [[(0,[z2,z3,z8,z807,z4,z5]),(0,[z7,z2,z3,z36,z4,z9]),(0,[z1,z2,z3,z8,z4,z1005]),(0,[z1006,z2,z3,z8,z4,z5]),(0,[z432,z2,z3,z8,z47,z5]),(0,[z54,z2,z350,z8,z4,z5]),(0,[z1,z2,z59,z943,z4,z5]),(0,[z1,z2,z69,z4,z177,z5]),(0,[z1,z1007,z3,z8,z4,z5]),(0,[z279,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z8,z1008,z5]),(0,[z1,z2,z3,z8,z4,z1009]),(0,[z14,z1,z2,z322,z8,z5]),(0,[z1,z2,z3,z1010,z4,z5]),(0,[z1011,z1,z2,z3,z4,z5]),(0,[z53,z1,z262,z8,z4,z115])],[(0,[z85,z1,z52,z36,z4,z5]),(0,[z1,z2,z3,z186,z4,z5]),(0,[z1012,z2,z3,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1013]),(0,[z1,z750,z3,z8,z4,z5]),(0,[z1,z2,z322,z8,z5,z91])],[(0,[z14,z2,z3,z8,z38,z5]),(0,[z1,z324,z97,z8,z4,z5]),(0,[z1,z2,z3,z1014,z4,z5]),(0,[z29,z1,z2,z8,z514,z5]),(0,[z1,z2,z3,z8,z824,z5])],[(0,[z1,z2,z3,z8,z1015,z5]),(0,[z1,z2,z3,z8,z1016,z5]),(0,[z503,z1,z2,z129,z4,z5]),(0,[z1017,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1018,z4,z5]),(0,[z90,z1,z2,z3,z6,z91]),(0,[z1,z2,z3,z8,z4,z722])],[(0,[z1,z2,z3,z36,z213,z5]),(0,[z1019,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z4,z778]),(0,[z26,z1,z2,z3,z495,z5]),(0,[z30,z1,z2,z24,z4,z31])],[(0,[z545,z1,z74,z8,z4,z5]),(0,[z39,z2,z3,z8,z75,z5]),(0,[z1,z2,z3,z8,z96,z358]),(0,[z1,z2,z3,z36,z4,z690]),(0,[z53,z1,z3,z252,z4,z115]),(0,[z214,z1,z2,z3,z5,z6]),(0,[z29,z1,z2,z8,z366,z5]),(0,[z29,z503,z1,z2,z3,z5])],[(0,[z294,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z1020,z4,z5]),(0,[z1,z2,z350,z8,z86,z5])]],
   [[(0,[z1,z2,z1021,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z1022]),(0,[z1,z1023,z3,z8,z4,z5]),(0,[z545,z1,z2,z8,z4,z5]),(0,[z1024,z2,z3,z8,z4,z5]),(0,[z391,z1,z3,z43,z4,z5]),(0,[z29,z1,z2,z666,z8,z5])],[(0,[z327,z1,z3,z36,z4,z5]),(0,[z1,z2,z3,z8,z1025,z5]),(0,[z1,z2,z3,z302,z5,z6]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z219,z1,z2,z3,z4,z840])],[(0,[z1,z2,z3,z4,z1027,z5]),(0,[z1028,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z86,z5]),(0,[z1,z3,z4,z903,z5,z6])],[(0,[z446,z2,z3,z8,z4,z9]),(0,[z1,z2,z480,z69,z4,z5]),(0,[z29,z503,z1,z2,z8,z5])],[(0,[z62,z2,z3,z303,z4,z5]),(0,[z7,z2,z97,z8,z4,z9]),(0,[z1,z3,z783,z8,z4,z5])],[(0,[z1029,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z389,z4,z5]),(0,[z7,z2,z3,z8,z213,z9]),(0,[z1,z2,z3,z36,z5,z88]),(0,[z279,z1,z3,z4,z5,z42])],[(0,[z217,z74,z3,z8,z4,z5]),(0,[z170,z2,z3,z8,z4,z384]),(1,[z29,z503,z1,z2,z5]),(0,[z1,z2,z3,z147,z94,z5]),(0,[z90,z1,z2,z3,z361,z91])],[(0,[z1,z2,z3,z1030,z4,z5]),(0,[z1,z2,z3,z1031,z4,z5]),(0,[z1,z2,z163,z8,z129,z5]),(0,[z1,z2,z3,z1032,z4,z5]),(0,[z1,z3,z4,z5,z765,z6])]],
   [[(0,[z923,z1,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1033,z5]),(0,[z1,z324,z3,z78,z4,z5]),(0,[z1034,z106,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z5,z1035]),(0,[z281,z469,z2,z92,z4,z5]),(0,[z469,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1036,z5]),(0,[z1,z2,z97,z8,z213,z5]),(0,[z1,z2,z3,z8,z1037,z5]),(0,[z1,z2,z3,z564,z4,z5]),(0,[z1,z2,z3,z4,z5,z1038]),(0,[z1039,z1,z3,z8,z4,z5]),(0,[z2,z3,z36,z1040,z4,z5]),(0,[z90,z106,z2,z3,z8,z91])],[(0,[z1,z2,z3,z1041,z4,z5]),(0,[z1,z2,z3,z24,z4,z5])],[(0,[z1042,z1,z2,z3,z4,z5]),(0,[z1043,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z4,z5,z1044]),(0,[z1,z2,z853,z8,z4,z5]),(0,[z161,z489,z3,z8,z19,z5])],[(0,[z1,z2,z3,z1045,z4,z5]),(0,[z1,z2,z3,z1046,z4,z5]),(0,[z2,z3,z8,z75,z5,z605]),(0,[z1,z2,z3,z4,z5,z1047]),(0,[z1,z3,z8,z4,z5,z1048]),(0,[z1,z2,z3,z36,z4,z840])],[(0,[z1,z324,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1049,z5]),(0,[z281,z2,z92,z4,z5,z6]),(0,[z62,z235,z3,z112,z4,z5]),(0,[z1,z2,z3,z4,z5,z840])],[(0,[z53,z1,z3,z8,z302,z115]),(0,[z1050,z2,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z1051,z5]),(0,[z1,z2,z3,z8,z1052,z5]),(0,[z1,z3,z4,z5,z909,z99]),(0,[z106,z2,z3,z8,z47,z5])]],
   [[(0,[z1,z1053,z3,z8,z4,z5]),(0,[z1,z2,z3,z1054,z4,z5]),(0,[z131,z1,z18,z3,z47,z5]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1056,z1,z3,z8,z4,z5]),(0,[z173,z1,z2,z3,z5,z515]),(0,[z133,z1,z3,z471,z4,z5])],[(0,[z1,z1057,z3,z8,z4,z5]),(0,[z1,z2,z3,z1058,z4,z5]),(0,[z1059,z2,z3,z8,z4,z5]),(0,[z545,z1,z18,z8,z47,z5])],[(0,[z294,z432,z3,z8,z4,z5]),(0,[z1,z2,z59,z69,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1060]),(0,[z1,z2,z3,z4,z5,z841])],[(0,[z325,z76,z3,z8,z4,z5]),(0,[z158,z2,z802,z8,z4,z5]),(0,[z1061,z2,z3,z8,z4,z5]),(0,[z1062,z2,z3,z8,z4,z5]),(0,[z1063,z2,z3,z8,z4,z5])],[(0,[z1,z18,z3,z8,z47,z5]),(0,[z1,z2,z3,z147,z137,z5])],[(0,[z1,z2,z3,z1064,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1065]),(0,[z2,z3,z8,z807,z38,z5]),(0,[z39,z2,z3,z402,z8,z5]),(0,[z190,z2,z3,z8,z98,z5]),(0,[z1,z2,z3,z8,z1066,z5])]],
   [[(0,[z432,z2,z3,z8,z4,z5]),(0,[z14,z2,z3,z38,z5,z6]),(0,[z1,z2,z3,z1067,z4,z5])],[(0,[z2,z802,z92,z8,z4,z5]),(0,[z1,z2,z4,z386,z5,z6]),(0,[z1,z2,z3,z1068,z4,z5])],[(0,[z0,z2,z3,z326,z4,z5]),(0,[z1,z2,z1069,z8,z4,z5])],[(0,[z53,z1,z3,z8,z4,z115]),(0,[z1,z2,z262,z186,z4,z5]),(0,[z1,z2,z3,z4,z5,z1070])],[(0,[z300,z1,z3,z43,z4,z5]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z54,z258,z3,z8,z4,z5]),(0,[z1,z1072,z3,z8,z4,z5]),(0,[z35,z214,z1,z2,z187,z5]),(0,[z1,z2,z3,z456,z4,z6])],[(0,[z1,z2,z3,z8,z1073,z5]),(0,[z294,z14,z3,z8,z38,z5]),(0,[z39,z2,z3,z75,z5,z6]),(0,[z1074,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z1075,z4,z5])],[(0,[z14,z2,z3,z8,z640,z5]),(0,[z1,z2,z802,z8,z4,z5]),(0,[z1,z2,z8,z129,z561,z5]),(0,[z2,z3,z8,z1040,z4,z5])],[(0,[z1,z774,z3,z8,z4,z5]),(0,[z1,z1076,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1077,z5]),(0,[z1,z2,z3,z1078,z4,z5]),(0,[z1,z2,z322,z8,z33,z96])]],
   [[(0,[z1,z1079,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z807,z5]),(0,[z30,z1,z8,z4,z125,z31])],[(0,[z1080,z1,z2,z3,z4,z5]),(0,[z1,z2,z1081,z8,z4,z5]),(0,[z1,z2,z1082,z8,z4,z5]),(0,[z294,z1,z3,z8,z19,z5]),(0,[z1,z2,z3,z1083,z4,z5]),(0,[z214,z1,z2,z3,z36,z5]),(0,[z1,z2,z8,z4,z136,z31]),(0,[z1,z2,z3,z361,z4,z5]),(0,[z26,z1,z2,z3,z965,z5]),(0,[z1,z2,z3,z4,z965,z5])],[(0,[z49,z217,z74,z3,z4,z5]),(0,[z279,z1,z3,z43,z4,z5]),(0,[z35,z29,z26,z1,z2,z5]),(0,[z1,z2,z307,z69,z4,z5]),(0,[z1,z3,z4,z5,z125,z6]),(0,[z1,z2,z3,z36,z224,z5])],[(0,[z1,z2,z3,z4,z5,z1084]),(0,[z281,z2,z338,z92,z8,z5]),(0,[z1085,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z1086,z4,z5])],[(0,[z2,z3,z802,z8,z4,z5]),(0,[z1,z1087,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z1088]),(0,[z1,z2,z3,z36,z4,z146])],[(0,[z1089,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z338,z8,z5]),(0,[z170,z2,z3,z8,z4,z710]),(0,[z273,z1,z8,z129,z4,z5]),(0,[z1,z862,z2,z3,z5,z6])],[(0,[z217,z74,z3,z4,z5,z6]),(0,[z35,z1,z2,z164,z187,z5])],[(0,[z1,z2,z3,z8,z5,z1090]),(0,[z1,z142,z3,z36,z4,z5]),(0,[z68,z1,z3,z4,z5,z11]),(0,[z1,z2,z3,z36,z164,z5]),(0,[z1,z2,z3,z4,z475,z6]),(0,[z29,z1,z2,z654,z8,z5])]],
   [[(0,[z1,z2,z3,z8,z1091,z5]),(0,[z545,z39,z1,z2,z8,z5]),(0,[z1,z2,z1092,z8,z4,z5]),(0,[z68,z1,z3,z252,z4,z5]),(0,[z1,z2,z1093,z8,z4,z5]),(0,[z1,z3,z36,z4,z5,z11])],[(0,[z294,z1,z3,z4,z5,z6]),(0,[z503,z1,z2,z3,z4,z5]),(0,[z29,z503,z1,z2,z165,z5]),(0,[z1,z2,z8,z4,z761,z31]),(0,[z175,z26,z1,z2,z4,z5])],[(0,[z1,z2,z1094,z8,z4,z5]),(0,[z1,z2,z3,z8,z1095,z5]),(0,[z1,z2,z8,z1096,z4,z5]),(0,[z30,z1,z2,z312,z4,z31]),(0,[z1,z2,z3,z8,z4,z840])],[(0,[z1,z2,z3,z8,z5,z1097]),(0,[z35,z1,z2,z187,z4,z5]),(0,[z1098,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z965,z5])],[(0,[z26,z1,z2,z3,z637,z5]),(0,[z1,z1099,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z5,z1100]),(0,[z1,z2,z8,z224,z5,z31])],[(0,[z1,z2,z3,z1101,z4,z5]),(0,[z1,z2,z3,z1102,z4,z5]),(0,[z1,z2,z3,z8,z1103,z5]),(0,[z1,z324,z3,z4,z5,z6]),(0,[z1,z3,z8,z4,z259,z690]),(0,[z1,z2,z3,z8,z696,z91]),(0,[z173,z1,z2,z3,z138,z5])],[(0,[z581,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z1104,z4,z5]),(1,[z1,z2,z943,z4,z5]),(1,[z1,z2,z8,z725,z5]),(0,[z1105,z1,z2,z3,z4,z5])],[(0,[z14,z74,z3,z8,z47,z5]),(0,[z489,z2,z3,z8,z4,z5]),(0,[z106,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z4,z141,z6]),(0,[z7,z142,z3,z8,z4,z9]),(0,[z1,z2,z3,z78,z162,z5]),(0,[z190,z1,z2,z3,z5,z6]),(0,[z21,z2,z3,z36,z4,z5]),(0,[z1,z2,z3,z1106,z4,z5])]],
   [[(0,[z1,z2,z3,z1107,z4,z5]),(0,[z1,z2,z3,z4,z5,z1108]),(0,[z1,z2,z1109,z8,z4,z5]),(0,[z1,z2,z3,z186,z302,z5]),(0,[z1,z2,z322,z8,z4,z5])],[(0,[z548,z74,z3,z8,z4,z5]),(0,[z1,z2,z8,z4,z1110,z5]),(0,[z1,z15,z3,z4,z5,z6]),(0,[z1,z2,z8,z129,z606,z5]),(0,[z53,z54,z3,z8,z4,z115]),(0,[z1,z1057,z3,z4,z5,z6])],[(0,[z1,z235,z3,z8,z4,z5]),(0,[z1,z2,z3,z1111,z4,z5]),(0,[z1,z2,z3,z1112,z4,z5])],[(0,[z1,z142,z97,z8,z4,z5]),(0,[z1,z2,z3,z8,z1113,z5]),(0,[z1,z2,z1114,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z584]),(0,[z1,z2,z8,z943,z4,z5]),(0,[z30,z1,z2,z8,z4,z761]),(0,[z1,z2,z3,z137,z965,z5])],[(0,[z1,z2,z3,z8,z4,z1115]),(0,[z1116,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z150,z5,z6]),(0,[z1,z1117,z3,z8,z4,z5]),(0,[z1,z1118,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z162,z5]),(0,[z1,z2,z1119,z8,z4,z5]),(0,[z1,z142,z3,z8,z213,z5]),(0,[z1,z113,z46,z208,z4,z5]),(0,[z1,z1120,z3,z8,z4,z5]),(0,[z1,z2,z4,z5,z382,z6])],[(0,[z300,z1,z235,z3,z4,z5]),(0,[z1,z2,z3,z1121,z4,z5]),(0,[z1122,z1,z2,z3,z4,z5]),(0,[z1,z3,z43,z741,z4,z5]),(0,[z1123,z1,z3,z8,z4,z5]),(0,[z1124,z2,z3,z8,z4,z5])],[(0,[z2,z3,z8,z4,z98,z627]),(0,[z1,z2,z676,z187,z4,z5])],[(0,[z14,z324,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1125,z5]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z161,z1,z3,z19,z5,z6]),(0,[z1,z2,z3,z312,z4,z5]),(0,[z1,z2,z59,z4,z5,z225]),(0,[z29,z1,z2,z8,z5,z498]),(0,[z559,z2,z3,z4,z5,z101])]],
   [[(0,[z1,z74,z3,z329,z4,z5]),(0,[z1,z2,z1127,z8,z4,z5]),(0,[z1,z2,z3,z1128,z4,z5]),(0,[z432,z2,z3,z4,z5,z6]),(0,[z420,z1,z2,z187,z4,z5]),(0,[z29,z106,z2,z3,z8,z5]),(0,[z175,z1,z2,z147,z8,z5])],[(0,[z1,z2,z3,z8,z1129,z5]),(0,[z1,z2,z3,z4,z5,z1130]),(0,[z1,z67,z3,z36,z4,z5]),(0,[z7,z2,z3,z8,z4,z141])],[(0,[z1,z2,z3,z4,z5,z1131]),(0,[z1,z1132,z3,z8,z4,z5]),(0,[z1133,z1,z2,z8,z4,z5]),(0,[z35,z214,z1,z2,z4,z5])],[(0,[z683,z1,z2,z8,z4,z31]),(0,[z1,z2,z3,z36,z4,z206]),(0,[z1,z2,z163,z609,z8,z5]),(0,[z1134,z1,z2,z3,z4,z5]),(0,[z1,z2,z783,z8,z4,z5]),(0,[z577,z1,z3,z8,z19,z5])],[(0,[z1,z2,z3,z1135,z4,z5]),(0,[z1042,z1,z67,z3,z4,z5]),(0,[z1,z2,z3,z208,z4,z5]),(0,[z1,z2,z3,z4,z373,z6]),(0,[z1,z2,z3,z8,z33,z464]),(0,[z1,z2,z307,z277,z4,z5]),(0,[z830,z1,z3,z36,z4,z5])],[(0,[z1,z2,z3,z1136,z4,z5]),(0,[z1,z1137,z3,z8,z4,z5]),(0,[z1,z3,z8,z4,z5,z11]),(0,[z1,z2,z8,z725,z165,z5]),(0,[z1,z2,z3,z147,z965,z5])],[(0,[z54,z2,z3,z36,z4,z5]),(0,[z833,z2,z3,z36,z4,z5])],[(0,[z1,z2,z97,z36,z4,z5]),(0,[z214,z1,z2,z59,z3,z5]),(0,[z1,z2,z3,z4,z5,z1138])]],
   [[(0,[z131,z1,z74,z3,z4,z5]),(0,[z1,z2,z3,z1139,z4,z5]),(0,[z1140,z1,z2,z3,z4,z5]),(0,[z279,z62,z1,z3,z4,z5]),(0,[z742,z1,z2,z3,z4,z5]),(0,[z1,z2,z8,z4,z1141,z5]),(0,[z1142,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z224,z5]),(0,[z1,z2,z3,z965,z138,z5]),(0,[z1,z2,z3,z36,z33,z96])],[(0,[z923,z74,z3,z8,z4,z5]),(0,[z14,z2,z3,z8,z37,z5]),(0,[z1,z2,z3,z8,z1143,z5]),(0,[z1,z2,z3,z1144,z4,z5]),(0,[z1,z2,z3,z162,z5,z6]),(0,[z1,z2,z3,z36,z4,z182]),(0,[z1145,z1,z2,z3,z4,z5]),(0,[z21,z2,z3,z8,z86,z5]),(0,[z1146,z1,z2,z3,z4,z5]),(0,[z1,z2,z1147,z8,z4,z5]),(0,[z1,z2,z8,z33,z96,z382])],[(0,[z1,z2,z3,z1148,z4,z5]),(0,[z131,z1,z2,z3,z4,z5]),(0,[z1149,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z36,z837,z5])],[(0,[z1,z2,z460,z4,z5,z6])],[(0,[z446,z1,z3,z8,z4,z115]),(0,[z1150,z1,z2,z3,z8,z4]),(0,[z1,z2,z1151,z8,z4,z5]),(0,[z39,z2,z3,z8,z73,z5]),(0,[z1,z2,z3,z8,z1152,z5]),(0,[z30,z1,z2,z36,z4,z31]),(0,[z1,z1153,z3,z8,z4,z5])],[(0,[z1,z2,z3,z8,z1154,z5]),(0,[z221,z1,z2,z196,z8,z5]),(0,[z269,z2,z193,z8,z4,z5]),(0,[z1,z2,z3,z8,z164,z5])],[],[(0,[z1,z2,z3,z8,z1155,z5]),(0,[z1156,z1,z2,z3,z4,z5]),(0,[z1,z2,z8,z4,z5,z745]),(0,[z14,z28,z2,z3,z8,z5]),(0,[z1157,z2,z3,z8,z4,z5]),(0,[z1,z2,z36,z4,z5,z382])]],
   [[(0,[z432,z74,z3,z8,z4,z5]),(0,[z1,z2,z3,z1158,z8,z4]),(0,[z1,z2,z1159,z8,z4,z5]),(0,[z324,z3,z8,z75,z4,z5]),(0,[z1160,z1,z2,z3,z4,z5]),(0,[z68,z1,z3,z519,z4,z5]),(0,[z1,z2,z3,z1161,z4,z5]),(0,[z1162,z2,z3,z8,z4,z5]),(0,[z970,z1,z3,z8,z4,z5])],[(0,[z1,z113,z46,z36,z4,z5]),(0,[z1,z2,z3,z4,z1163,z5]),(0,[z1,z3,z4,z5,z6,z1164]),(0,[z1,z2,z3,z317,z5,z228]),(0,[z2,z3,z36,z4,z5,z107])],[(0,[z1,z2,z1165,z8,z4,z5]),(0,[z14,z2,z3,z8,z807,z5]),(0,[z2,z3,z8,z75,z807,z5]),(0,[z1,z2,z3,z105,z4,z5]),(0,[z26,z1,z2,z343,z138,z5])],[(0,[z1,z2,z3,z4,z5,z1166]),(0,[z7,z190,z2,z3,z8,z9]),(0,[z27,z1,z3,z4,z394,z5]),(0,[z1,z3,z8,z727,z4,z5]),(0,[z1,z2,z3,z1167,z4,z5]),(0,[z1,z3,z719,z8,z4,z5])],[(0,[z1,z2,z3,z1168,z4,z5]),(0,[z1,z3,z4,z5,z11,z6])],[(0,[z21,z2,z3,z8,z4,z5]),(0,[z158,z2,z193,z8,z4,z5]),(0,[z273,z1,z46,z8,z4,z5]),(0,[z1,z2,z3,z1169,z4,z5]),(0,[z1,z2,z3,z36,z4,z266])],[(1,[z923,z3,z8,z4,z5]),(0,[z1,z2,z3,z1170,z4,z5]),(0,[z106,z2,z3,z8,z38,z5]),(0,[z1,z2,z350,z8,z4,z5]),(0,[z29,z503,z1,z2,z4,z5]),(0,[z1,z2,z196,z8,z87,z88]),(0,[z1,z2,z3,z5,z6,z1171])],[(0,[z1,z532,z46,z8,z4,z5]),(0,[z281,z2,z802,z8,z4,z5]),(0,[z1,z1172,z3,z8,z4,z5]),(0,[z1,z2,z1173,z8,z4,z5]),(0,[z1,z2,z3,z4,z56,z6]),(0,[z1,z2,z3,z4,z5,z1174]),(0,[z489,z2,z3,z4,z5,z6]),(0,[z106,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z1175,z5])]],
   [[(0,[z54,z2,z3,z8,z86,z5]),(0,[z2,z3,z8,z4,z5,z1176]),(0,[z1,z2,z322,z4,z5,z6])],[(0,[z1,z2,z3,z36,z4,z5]),(0,[z1,z1177,z2,z3,z8,z5]),(0,[z27,z1,z3,z408,z4,z5]),(0,[z175,z26,z1,z2,z138,z5]),(0,[z976,z1,z2,z3,z8,z5])],[(0,[z1,z235,z3,z4,z5,z6]),(0,[z190,z1,z2,z3,z36,z5]),(0,[z1,z2,z3,z1178,z4,z5]),(0,[z503,z1,z2,z163,z3,z5])],[(0,[z66,z76,z3,z8,z428,z5]),(0,[z1,z2,z1179,z8,z4,z5]),(0,[z1,z3,z4,z5,z11,z283]),(0,[z1,z2,z3,z943,z4,z5]),(0,[z1,z2,z3,z8,z725,z5]),(0,[z175,z1,z2,z36,z4,z5]),(0,[z1,z2,z8,z4,z5,z776])],[(0,[z7,z2,z3,z78,z4,z9]),(0,[z1,z113,z8,z4,z659,z5]),(0,[z1,z2,z105,z4,z386,z5]),(0,[z1,z2,z3,z1180,z4,z5]),(0,[z35,z1,z2,z387,z4,z5]),(0,[z1,z2,z196,z8,z224,z87]),(0,[z1034,z1,z3,z8,z4,z5])],[(0,[z1,z2,z3,z1181,z8,z5]),(0,[z1,z2,z3,z4,z5,z1182]),(0,[z1183,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z164,z5,z6]),(0,[z1,z2,z3,z1184,z4,z5]),(0,[z1,z2,z3,z137,z5,z228]),(0,[z90,z1,z2,z3,z8,z91])],[(0,[z1,z2,z3,z8,z428,z5]),(0,[z2,z193,z802,z8,z4,z5]),(0,[z1,z2,z3,z64,z4,z5]),(0,[z1185,z2,z3,z8,z4,z5])],[(0,[z1,z67,z3,z8,z4,z5]),(0,[z469,z1,z2,z3,z338,z5]),(0,[z62,z2,z3,z4,z5,z423]),(0,[z2,z3,z8,z4,z5,z1186]),(0,[z291,z2,z3,z313,z4,z5])]],
   [[(0,[z1,z2,z97,z78,z4,z5]),(0,[z170,z2,z3,z36,z4,z98]),(0,[z1187,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z104,z4,z6])],[(0,[z66,z2,z3,z8,z428,z5]),(0,[z1,z1188,z3,z8,z4,z5]),(1,[z2,z3,z726,z4,z5]),(0,[z7,z2,z3,z8,z4,z9]),(0,[z1,z2,z3,z78,z213,z5]),(0,[z549,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z137,z243,z5]),(0,[z1,z2,z3,z1189,z4,z5])],[(0,[z1,z1190,z3,z8,z4,z5]),(0,[z14,z15,z3,z8,z38,z5]),(0,[z1,z2,z3,z8,z5,z1171]),(0,[z1191,z1,z3,z8,z4,z5]),(0,[z1192,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z224,z5,z205]),(0,[z1,z2,z3,z241,z224,z5]),(0,[z1,z2,z3,z5,z6,z88])],[(0,[z221,z1,z2,z3,z8,z5]),(0,[z85,z1,z52,z8,z4,z5]),(0,[z68,z54,z3,z8,z4,z5]),(0,[z106,z2,z3,z8,z96,z5])],[(0,[z54,z2,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1193,z5]),(0,[z1,z3,z8,z428,z47,z5]),(0,[z1,z2,z3,z1194,z4,z5]),(0,[z226,z158,z193,z8,z4,z5]),(0,[z1,z1195,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1196,z5]),(0,[z1,z2,z3,z4,z120,z6]),(0,[z1,z2,z8,z4,z5,z382]),(0,[z762,z1,z2,z8,z4,z5]),(0,[z1,z885,z3,z36,z4,z5])],[(0,[z1,z2,z97,z8,z4,z5]),(0,[z1,z2,z3,z36,z4,z680]),(0,[z170,z2,z3,z64,z4,z98]),(0,[z1,z3,z8,z4,z5,z1164])],[(0,[z1,z2,z3,z617,z4,z6]),(0,[z1,z2,z1197,z8,z4,z5]),(0,[z1,z2,z3,z8,z213,z5]),(0,[z14,z2,z3,z8,z162,z5]),(0,[z2,z3,z8,z4,z5,z107]),(0,[z2,z3,z8,z75,z162,z5]),(0,[z1,z2,z3,z1198,z4,z5]),(0,[z1,z258,z3,z564,z4,z259]),(0,[z1,z2,z3,z8,z4,z761])],[(0,[z76,z923,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z1199,z5]),(0,[z85,z54,z3,z8,z4,z5]),(0,[z27,z1,z3,z4,z5,z11])]],
   [[(0,[z39,z2,z3,z8,z807,z5]),(0,[z1,z324,z3,z389,z4,z5]),(0,[z1,z2,z3,z1200,z4,z5]),(0,[z68,z1,z340,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1201]),(0,[z1,z2,z3,z718,z4,z5]),(0,[z1,z2,z322,z4,z5,z466]),(0,[z1,z2,z322,z449,z4,z5])],[(0,[z1,z1202,z3,z8,z4,z5]),(0,[z469,z221,z1,z2,z3,z5]),(0,[z1,z2,z3,z8,z4,z1203]),(0,[z1,z2,z3,z8,z5,z735]),(0,[z1,z2,z3,z4,z452,z6])],[(0,[z327,z1,z3,z8,z4,z5]),(0,[z221,z1,z2,z3,z12,z5]),(0,[z1,z2,z460,z8,z162,z5]),(0,[z1,z2,z3,z36,z4,z321]),(0,[z775,z1,z3,z8,z4,z5]),(0,[z30,z1,z2,z8,z4,z31]),(0,[z1149,z2,z3,z4,z5,z6])],[(0,[z545,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z8,z86,z5]),(0,[z53,z1,z3,z186,z4,z115])],[(0,[z1,z1204,z3,z8,z4,z5]),(0,[z782,z1,z2,z8,z4,z5]),(0,[z1,z18,z8,z386,z47,z5]),(0,[z1205,z1,z2,z3,z4,z5]),(0,[z1,z3,z8,z4,z1206,z5]),(0,[z1,z2,z8,z4,z5,z761]),(0,[z1,z2,z3,z147,z254,z5]),(0,[z1,z2,z8,z4,z1175,z5])],[(0,[z1,z2,z3,z1207,z4,z5]),(0,[z7,z2,z3,z8,z130,z9]),(0,[z1,z2,z3,z1208,z4,z5]),(0,[z1,z2,z196,z36,z4,z87])],[(0,[z62,z481,z2,z3,z4,z5]),(0,[z1,z2,z3,z1209,z4,z5]),(0,[z1210,z1,z2,z3,z4,z5]),(0,[z1,z786,z3,z8,z4,z5]),(0,[z1,z2,z3,z8,z5,z88]),(0,[z1211,z1,z2,z3,z4,z5])],[(0,[z226,z1,z3,z36,z4,z5]),(0,[z1,z2,z3,z1212,z4,z5]),(0,[z1,z2,z8,z4,z5,z1213]),(0,[z1,z2,z3,z4,z5,z1214]),(0,[z1215,z2,z3,z8,z4,z5]),(0,[z161,z1,z3,z36,z19,z5]),(0,[z1,z2,z3,z4,z5,z1216]),(0,[z1,z2,z3,z1217,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 527).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1052).take 202) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1254)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [527, 525, 202] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 104).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 209).take 47).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [104, 105, 47] = true :=
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

end PEqualNP.Outside.L_meta_38779

theorem PEqualNP.Outside.L_meta_38779 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4270369280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4270369280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38779.solve