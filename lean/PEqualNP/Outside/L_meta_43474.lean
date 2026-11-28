import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43474

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4272613504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0000021500950db4#64 ++ 0x40000021500950db#64 ++ 0xe0239e3f01ff1fff#64 ++ 0xbe0239e3f01ff1ff#64 : BitVec 256),
   (0x10cd28cc864c62d2#64 ++ 0x810cd28cc864c62d#64 ++ 0xf1dd69cc8e4ce3ff#64 ++ 0x6f1dd69cc8e4ce3f#64 : BitVec 256),
   (0x26165170b070b46b#64 ++ 0x026165170b070b46#64 ++ 0xbe1e71f0f070fc7e#64 ++ 0xfbe1e71f0f070fc7#64 : BitVec 256),
   (0x4b607e005b80db0c#64 ++ 0x04b607e005b80db0#64 ++ 0x6fe07e00ff80ff8d#64 ++ 0xf6fe07e00ff80ff8#64 : BitVec 256),
   (0x0dbf8000ed6a0000#64 ++ 0x00dbf8000ed6a000#64 ++ 0x4fff8000ffff000b#64 ++ 0xf4fff8000ffff000#64 : BitVec 256),
   (0x8ffbfdaa00000000#64 ++ 0x08ffbfdaa0000000#64 ++ 0x9fffffff00000007#64 ++ 0xe9fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000021100910d24 0x40000021100910d2 0x0000163300001c00 0x00000163300001c0

def z1 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe0239e3f01ff1fff 0xbe0239e3f01ff1ff

def z2 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff8000ffff000b 0xf4fff8000ffff000

def z3 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd69cc8e4ce3ff 0x6f1dd69cc8e4ce3f

def z4 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e71f0f070fc7e 0xfbe1e71f0f070fc7

def z5 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe07e00ff80ff8d 0xf6fe07e00ff80ff8

def z6 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fffffff00000007 0xe9fffffff0000000

def z7 : W := mkw 0x00040000ed6a0000 0x000040000ed6a000 0x00000000fe000000 0x000000000fe00000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000100000001c0c 0xb2000100000001c0

def z9 : W := mkw 0x0200500010009008 0x0020050001000900 0x0e006000f000e000 0x40e006000f000e00

def z10 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe003803f01ff1ffa 0x1e003803f01ff1ff

def z11 : W := mkw 0x0d360000e9600000 0x00d360000e960000 0x4ffe0000fff0000b 0xf4ffe0000fff0000

def z12 : W := mkw 0xaffffdfab070b46b 0x0affffdfab070b46 0xbffffffff070fc7f 0xfbffffffff070fc7

def z13 : W := mkw 0xcffbffaa5b80db0c 0x0cffbffaa5b80db0 0xffffffffff80ff8f 0xfffffffffff80ff8

def z14 : W := mkw 0x04160000a0600000 0x004160000a060000 0x4e3f8000f1ff000b 0xf4e3f8000f1ff000

def z15 : W := mkw 0x20040255b0f5bdff 0x420040255b0f5bdf 0x60000000f1fffff8 0x160000000f1fffff

def z16 : W := mkw 0x26165375b0f5bdff 0x426165375b0f5bdf 0xfe3ffffff1ffffff 0xffe3ffffff1fffff

def z17 : W := mkw 0x0000021500950db4 0x40000021500950db 0x8023963f01ff1c72 0x98023963f01ff1c7

def z18 : W := mkw 0x22045050b070b46b 0x022045050b070b46 0x2e007000f070fc7c 0xf2e007000f070fc7

def z19 : W := mkw 0x10c9288c060c4290 0x810c9288c060c429 0x41c1080c0e0c0381 0x041c1080c0e0c038

def z20 : W := mkw 0x2612513030309429 0x0261251303030942 0x0e02103070301c00 0x90e02103070301c0

def z21 : W := mkw 0x50040244dfccfbde 0x850040244dfccfbd 0x60000000ffccfff8 0x160000000ffccfff

def z22 : W := mkw 0x0000020000800904 0x0000002000080090 0x60201e0001801f8d 0xb60201e0001801f8

def z23 : W := mkw 0x4b607e155b95dfbc 0x44b607e155b95dfb 0xefe3fe3fffffffff 0xfefe3fe3ffffffff

def z24 : W := mkw 0x20040050b070b46b 0x020040050b070b46 0xa0021030f070fc7e 0xba0021030f070fc7

def z25 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x1ffdefcf00000001 0x41ffdefcf0000000

def z26 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x51dd69cc8e0ce381 0x451dd69cc8e0ce38

def z27 : W := mkw 0x400002005b80db0c 0x0400002005b80db0 0x60000000ff80ff88 0x160000000ff80ff8

def z28 : W := mkw 0x4b607c005b00d208 0x04b607c005b00d20 0x0fc06000fe00e000 0x40fc06000fe00e00

def z29 : W := mkw 0x1dbf8044ef6e62d2 0x81dbf8044ef6e62d 0x6fff8000ffffe3fb 0xf6fff8000ffffe3f

def z30 : W := mkw 0x20040050a0702463 0x020040050a070246 0x0000000000700070 0x0000000000070007

def z31 : W := mkw 0x1dffaaddefff6ff6 0xc1dffaaddefff6ff 0xffffffffffffffff 0xffffffffffffffff

def z32 : W := mkw 0x4ffffe15ffffdfbc 0x44ffffe15ffffdfb 0xeffffe3fffffffff 0xfeffffe3ffffffff

def z33 : W := mkw 0x8ffbffaf00850994 0x48ffbffaf0085099 0xdfffffff018f0387 0xedfffffff018f038

def z34 : W := mkw 0x20040040b060b04b 0x020040040b060b04 0x00000000f000e000 0x000000000f000e00

def z35 : W := mkw 0x220051701010b46b 0x0220051701010b46 0xbe0071f0f000fc7c 0xfbe0071f0f000fc7

def z36 : W := mkw 0x1dffa8cc864c62d2 0x81dffa8cc864c62d 0xffffe9cc8e4ce3ff 0xeffffe9cc8e4ce3f

def z37 : W := mkw 0x0004004080402042 0x0000400408040204 0xb01c61c08040e07e 0x6b01c61c08040e07

def z38 : W := mkw 0x0200500010009008 0x0020050001000900 0x2e007000f000fc0c 0xf2e007000f000fc0

def z39 : W := mkw 0x8ffbfdaa10009008 0x08ffbfdaa1000900 0xbffffffff000fc0f 0xfbffffffff000fc0

def z40 : W := mkw 0x0612512000000000 0x0061251200000000 0x9e1e71f000000006 0xe9e1e71f00000000

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x4023800001ff000b 0xb4023800001ff000

def z42 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0fdc0000fe000000 0x40fdc0000fe00000

def z43 : W := mkw 0x0000021500950db4 0x40000021500950db 0x2000000000001ff0 0x02000000000001ff

def z44 : W := mkw 0x108d00cc844c20d2 0x8108d00cc844c20d 0x901d01cc004c0072 0x0901d01cc004c007

def z45 : W := mkw 0x24160170a0702463 0x024160170a070246 0x901e01f000700072 0x0901e01f00070007

def z46 : W := mkw 0x49602e004b804b04 0x049602e004b804b0 0x41e00e000f800381 0x041e00e000f80038

def z47 : W := mkw 0x6f767f70fbf0ff6f 0x06f767f70fbf0ff6 0xfffe7ff0fff0ffff 0xffffe7ff0fff0fff

def z48 : W := mkw 0x89e9ac8a00000000 0x089e9ac8a0000000 0x01c0000000000000 0x001c000000000000

def z49 : W := mkw 0x4ffffe00ffeadb0c 0x04ffffe00ffeadb0 0x6ffffe00ffffff8f 0xf6ffffe00ffffff8

def z50 : W := mkw 0x42407e001280db0c 0x042407e001280db0 0x20007e000000ff84 0x020007e000000ff8

def z51 : W := mkw 0x008d000084480000 0x0008d00008448000 0x41dd00008e4c000b 0x641dd00008e4c000

def z52 : W := mkw 0x1040288c02044290 0x81040288c0204429 0x0000080c00000380 0x00000080c0000038

def z53 : W := mkw 0x32cd79fc965cf6fb 0x832cd79fc965cf6f 0xf1dd79fc8e4cffff 0x6f1dd79fc8e4cfff

def z54 : W := mkw 0x0000021100910d24 0x40000021100910d2 0x0022963301b31c00 0x90022963301b31c0

def z55 : W := mkw 0x10cd28c886486242 0x810cd28c88648624 0x11dc61c08e00e000 0x411dc61c08e00e00

def z56 : W := mkw 0x0089000004080000 0x0008900000408000 0x41c100000e0c0001 0x041c100000e0c000

def z57 : W := mkw 0x0000000049000000 0x0000000004900000 0x40000000ff800008 0x140000000ff80000

def z58 : W := mkw 0x492002005b80db0c 0x0492002005b80db0 0x6fe00000ff80ff89 0xf6fe00000ff80ff8

def z59 : W := mkw 0x0040280000000000 0x0004028000000000 0x01c0680000000005 0x601c068000000000

def z60 : W := mkw 0x00040000ed6a0000 0x000040000ed6a000 0x40238000ffff000b 0xb40238000ffff000

def z61 : W := mkw 0x2000017000102463 0x0200001700010246 0x900001f000000070 0x0900001f00000007

def z62 : W := mkw 0x36df79fcb67cf6fb 0x836df79fcb67cf6f 0xffdf79fcfe7cffff 0xfffdf79fcfe7cfff

def z63 : W := mkw 0x59e92e8c4f8c4b94 0x859e92e8c4f8c4b9 0x41e10e0c0f8c0381 0x041e10e0c0f8c038

def z64 : W := mkw 0x5bed7eccdfccfbde 0x85bed7eccdfccfbd 0xfffd7fccffccffff 0xffffd7fccffccfff

def z65 : W := mkw 0x04160010a0700420 0x004160010a070042 0xae1e1030f0701c7e 0xfae1e1030f0701c7

def z66 : W := mkw 0xcffbffaa5980990c 0x0cffbffaa5980990 0x9fffffff71801c07 0xf9fffffff71801c0

def z67 : W := mkw 0x108d00cc844c20d2 0x8108d00cc844c20d 0xb01d61cc804ce07e 0x6b01d61cc804ce07

def z68 : W := mkw 0x20040050b070b46b 0x020040050b070b46 0x20000000f070fc78 0x120000000f070fc7

def z69 : W := mkw 0x0d32800069220000 0x00d3280006922000 0x0e22800071b30000 0x90e22800071b3000

def z70 : W := mkw 0x104028cc020462d2 0x8104028cc020462d 0xb00069cc0000e3f4 0x0b00069cc0000e3f

def z71 : W := mkw 0x104428cc864c62d2 0x8104428cc864c62d 0xf00069cc8e4ce3fc 0x0f00069cc8e4ce3f

def z72 : W := mkw 0x4ffbfe005b80db0c 0x04ffbfe005b80db0 0x6ffffe00ff80ff8f 0xf6ffffe00ff80ff8

def z73 : W := mkw 0x4b607e001280db0c 0x04b607e001280db0 0x2fe07e000000ff85 0xe2fe07e000000ff8

def z74 : W := mkw 0x0040280002004200 0x0004028000200420 0x61c068008e00e38d 0x661c068008e00e38

def z75 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901f81ff00000002 0x0901f81ff0000000

def z76 : W := mkw 0x89e9ac8a00000000 0x089e9ac8a0000000 0x01e18e0f00000001 0x001e18e0f0000000

def z77 : W := mkw 0x1004004086486242 0x8100400408648624 0x000000008e00e000 0x0000000008e00e00

def z78 : W := mkw 0x2612513030309429 0x0261251303030942 0x2e027030f030fc0c 0xf2e027030f030fc0

def z79 : W := mkw 0x06db79a800000000 0x006db79a80000000 0x9fdf79fc00000007 0xe9fdf79fc0000000

def z80 : W := mkw 0x9ffbfdae060c4290 0x89ffbfdae060c429 0xdfffffff0e0c0387 0xedfffffff0e0c038

def z81 : W := mkw 0x0dbf800084480000 0x00dbf80008448000 0x4fff80008e4c000b 0xe4fff80008e4c000

def z82 : W := mkw 0x09240000ed6a0000 0x009240000ed6a000 0x4fe00000ffff0009 0xf4fe00000ffff000

def z83 : W := mkw 0x10c92a8d068d4b94 0xc10c92a8d068d4b9 0x41e18e0f0f8f0381 0x041e18e0f0f8f038

def z84 : W := mkw 0x42407e001280db0c 0x042407e001280db0 0x2e007e00f000ff8c 0xf2e007e00f000ff8

def z85 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x41ff80000fff0003 0x041ff80000fff000

def z86 : W := mkw 0x10c9288c060c4290 0x810c9288c060c429 0x61c1680c8e0ce38d 0x661c1680c8e0ce38

def z87 : W := mkw 0x5ffffeccffeefbde 0x85ffffeccffeefbd 0xffffffccffffffff 0xfffffffccfffffff

def z88 : W := mkw 0x4f767e00fbe0db0c 0x04f767e00fbe0db0 0x6ffe7e00fff0ff8f 0xf6ffe7e00fff0ff8

def z89 : W := mkw 0x24160375a0f52df7 0x424160375a0f52df 0xf03f9fff01ff1fff 0xbf03f9fff01ff1ff

def z90 : W := mkw 0x0000000400040090 0x0000000040004009 0x8001000c004c0072 0x08001000c004c007

def z91 : W := mkw 0x2fbfd170fd7ab46b 0x02fbfd170fd7ab46 0xfffff1f0fffffc7f 0xffffff1f0fffffc7

def z92 : W := mkw 0x2412013020300421 0x0241201302030042 0x0002003000300000 0x0000200300030000

def z93 : W := mkw 0x92407dee020462d2 0x892407dee020462d 0xb0007fff0000e3f4 0x0b0007fff0000e3f

def z94 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe001080c01ff1fff 0x3e001080c01ff1ff

def z95 : W := mkw 0x2000001030309429 0x0200000103030942 0x0000000070301c00 0x10000000070301c0

def z96 : W := mkw 0x00c9288800000000 0x000c928880000000 0x91dd69cc00000007 0x691dd69cc0000000

def z97 : W := mkw 0x0920000049000000 0x0092000004900000 0x4fe00000ff800009 0xf4fe00000ff80000

def z98 : W := mkw 0x8ffbfdaa49000000 0x08ffbfdaa4900000 0xdfffffffff80000f 0xfdfffffffff80000

def z99 : W := mkw 0x049f8000a46a0000 0x0049f8000a46a000 0x001f8000007f0002 0x0001f8000007f000

def z100 : W := mkw 0x049f0000a4680000 0x0049f0000a468000 0x4fdf0000fe7c000b 0xf4fdf0000fe7c000

def z101 : W := mkw 0x2612513030309429 0x0261251303030942 0xae02103070701c7e 0xbae02103070701c7

def z102 : W := mkw 0x0612512000000000 0x0061251200000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z103 : W := mkw 0x0200501010109428 0x0020050101010942 0xae027030f070fc7e 0xfae027030f070fc7

def z104 : W := mkw 0x6f767d70fb70f66b 0x06f767d70fb70f66 0xbfde71f0fe70fc7e 0xfbfde71f0fe70fc7

def z105 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xb01e71f00070fc76 0x0b01e71f00070fc7

def z106 : W := mkw 0x0089008800000000 0x0008900880000000 0x901d01cc00000002 0x0901d01cc0000000

def z107 : W := mkw 0x0b607c0000000000 0x00b607c000000000 0x0fe07e0000000005 0xe0fe07e000000000

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x0022800001b30000 0x90022800001b3000

def z109 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fdd0000fe4c000b 0x64fdd0000fe4c000

def z110 : W := mkw 0x10cd28dd865d66f2 0xc10cd28dd865d66f 0xf1dfe9ff8e7fe3ff 0x6f1dfe9ff8e7fe3f

def z111 : W := mkw 0x7fff7ffcfffcffff 0x87fff7ffcfffcfff 0xffff7ffcfffcffff 0xfffff7ffcfffcfff

def z112 : W := mkw 0x008d0004844c0090 0x0008d0004844c009 0xe1dd080c8e4c03ff 0x6e1dd080c8e4c03f

def z113 : W := mkw 0x26165375b0f5bdff 0x426165375b0f5bdf 0xbe1e7ffff070fffe 0xfbe1e7ffff070fff

def z114 : W := mkw 0x0000000400040090 0x0000000040004009 0x4001080c000c0381 0x04001080c000c038

def z115 : W := mkw 0x2612512030209009 0x0261251203020900 0x0e00000070000000 0x00e0000007000000

def z116 : W := mkw 0x0000021500950db4 0x40000021500950db 0x6000000001ff1ff8 0x16000000001ff1ff

def z117 : W := mkw 0x4be9fe005f8adb0c 0x04be9fe005f8adb0 0x6fe1fe00ff8fff8d 0xf6fe1fe00ff8fff8

def z118 : W := mkw 0x00000015001504b0 0x400000015001504b 0x8000003f00000070 0x08000003f0000007

def z119 : W := mkw 0x42407e001280db0c 0x042407e001280db0 0x60207e000180ff8d 0xb60207e000180ff8

def z120 : W := mkw 0x8ffbfdaa02004200 0x08ffbfdaa0200420 0xffffffff8e00e38f 0xeffffffff8e00e38

def z121 : W := mkw 0x849b83bf00950db4 0x4849b83bf00950db 0xf03f9fff01ff1fff 0xbf03f9fff01ff1ff

def z122 : W := mkw 0x8ffffdaaed6a0000 0x08ffffdaaed6a000 0xdfffffffffff000f 0xfdfffffffffff000

def z123 : W := mkw 0x0200512000000000 0x0020051200000000 0x900071f000000004 0x0900071f00000000

def z124 : W := mkw 0xaf36d572b070b46b 0x0af36d572b070b46 0xbe3ef7f3f070fc7e 0xfbe3ef7f3f070fc7

def z125 : W := mkw 0x0000001000100420 0x0000000100010042 0x2000000000701c78 0x12000000000701c7

def z126 : W := mkw 0x4b647e00ffeadb0c 0x04b647e00ffeadb0 0x6fe07e00ffffff8d 0xf6fe07e00ffffff8

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020000001800009 0xb402000000180000

def z128 : W := mkw 0x108d00cc844c20d2 0x8108d00cc844c20d 0xf01d09cc004c03ff 0x2f01d09cc004c03f

def z129 : W := mkw 0x1dffa8ccef6e62d2 0x81dffa8ccef6e62d 0xffffe9ccffffe3ff 0xfffffe9ccffffe3f

def z130 : W := mkw 0x0000001000100420 0x0000000100010042 0xa000103000001c74 0x0a000103000001c7

def z131 : W := mkw 0x1dffa8c8ef6a6242 0x81dffa8c8ef6a624 0x5fffe1c0ffffe00b 0xf5fffe1c0ffffe00

def z132 : W := mkw 0x8ffbfdaa69220000 0x08ffbfdaa6922000 0x9fffffff71b30007 0xf9fffffff71b3000

def z133 : W := mkw 0x4ffffc00ff6ad208 0x04ffffc00ff6ad20 0x0fdc6000fe00e000 0x40fdc6000fe00e00

def z134 : W := mkw 0x50cd2accdfccfbde 0x850cd2accdfccfbd 0xf1dd69ccffccffff 0x7f1dd69ccffccfff

def z135 : W := mkw 0x10000044020462d2 0x810000044020462d 0x200000000000e3f0 0x0200000000000e3f

def z136 : W := mkw 0x800001aa00000000 0x0800001aa0000000 0x900001ff00000000 0x0900001ff0000000

def z137 : W := mkw 0x400002155b95dfbc 0x4400002155b95dfb 0x60000000fffffff8 0x160000000fffffff

def z138 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1ffe9cc8fffe3ff 0xff1ffe9cc8fffe3f

def z139 : W := mkw 0x0dbf8215edff0db4 0x40dbf8215edff0db 0xefff9e3fffff1fff 0xfefff9e3fffff1ff

def z140 : W := mkw 0x4ffffe00ffeadb0c 0x04ffffe00ffeadb0 0x6ffc7e00ff80ff8d 0xf6ffc7e00ff80ff8

def z141 : W := mkw 0x00000015001504b0 0x400000015001504b 0x00000000007f0070 0x000000000007f007

def z142 : W := mkw 0x8dfbadaa00000000 0x08dfbadaa0000000 0x91ff8fff00000003 0x091ff8fff0000000

def z143 : W := mkw 0x0dbf8000a46a0000 0x00dbf8000a46a000 0x0fff8000007f0003 0xe0fff8000007f000

def z144 : W := mkw 0x82c97daa00000000 0x082c97daa0000000 0x91dd7fff00000007 0x691dd7fff0000000

def z145 : W := mkw 0x06165120a0600000 0x006165120a060000 0x9e1e71f0f070000e 0xf9e1e71f0f070000

def z146 : W := mkw 0x8dbf81aaed6a0000 0x08dbf81aaed6a000 0xdfff81ffffff000b 0xfdfff81ffffff000

def z147 : W := mkw 0x0000021500950db4 0x40000021500950db 0xa0001e3f00001ff4 0x0a0001e3f00001ff

def z148 : W := mkw 0x0000000400040090 0x0000000040004009 0xe001080c004c03ff 0x2e001080c004c03f

def z149 : W := mkw 0x4b20540059009008 0x04b2054005900900 0x0e00000070000000 0x00e0000007000000

def z150 : W := mkw 0x0d32800069220000 0x00d3280006922000 0x4e23800071ff000b 0xb4e23800071ff000

def z151 : W := mkw 0x2fbfd160fd6ab04b 0x02fbfd160fd6ab04 0x5fffe1c0ffffe00b 0xf5fffe1c0ffffe00

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0x200060008000e00c 0x6200060008000e00

def z153 : W := mkw 0x220051701010b46b 0x0220051701010b46 0xb00271f00070fc7e 0xbb00271f00070fc7

def z154 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x2e207e007180ff84 0x92e207e007180ff8

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0x80239e3f00000007 0xa80239e3f0000000

def z156 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1ffffff8e4ce3ff 0xef1ffffff8e4ce3f

def z157 : W := mkw 0x0000020000800904 0x0000002000080090 0xe0239e3f01801f8f 0xbe0239e3f01801f8

def z158 : W := mkw 0x0dbf8010ed7a0420 0x00dbf8010ed7a042 0xefff9030ffff1c7f 0xfefff9030ffff1c7

def z159 : W := mkw 0x19ed28cccf4c62d2 0x819ed28cccf4c62d 0xfffd69ccffcce3ff 0xffffd69ccffcce3f

def z160 : W := mkw 0xa49f81faa0702463 0x0a49f81faa070246 0x901f81ff00700072 0x0901f81ff0070007

def z161 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xb1dc69cc8e00e3f4 0x4b1dc69cc8e00e3f

def z162 : W := mkw 0x220051601000b04b 0x0220051601000b04 0x100061c00000e000 0x0100061c00000e00

def z163 : W := mkw 0x400002005b80db0c 0x0400002005b80db0 0x60201e00ff80ff8d 0xb60201e00ff80ff8

def z164 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xb01d69cc004ce3f6 0x0b01d69cc004ce3f

def z165 : W := mkw 0x6f32573079b09d2d 0x06f32573079b09d2 0x0e22163071b01c00 0x90e22163071b01c0

def z166 : W := mkw 0x10cd28dc865c66f2 0x810cd28dc865c66f 0xf1df79fc8e7cffff 0xff1df79fc8e7cfff

def z167 : W := mkw 0x0040280402044290 0x0004028040204429 0xe1c1680c8e4ce3ff 0x6e1c1680c8e4ce3f

def z168 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xefe3fe3fff80ff8f 0xfefe3fe3fff80ff8

def z169 : W := mkw 0x86dbfdaa00000000 0x086dbfdaa0000000 0x901fffff00000006 0x0901fffff0000000

def z170 : W := mkw 0x49602e005b80db0c 0x049602e005b80db0 0x61e00e00ff80ff89 0x161e00e00ff80ff8

def z171 : W := mkw 0x0000021500950db4 0x40000021500950db 0x6022963301ff1ff8 0x96022963301ff1ff

def z172 : W := mkw 0x949f81ee844c20d2 0x8949f81ee844c20d 0x901f81ff004c0072 0x0901f81ff004c007

def z173 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xfe3ff1f0f1fffc7f 0xffe3ff1f0f1fffc7

def z174 : W := mkw 0x8ffbfdae00040090 0x08ffbfdae0004009 0xffffffff004c03ff 0xeffffffff004c03f

def z175 : W := mkw 0x8ffbffbf00950db4 0x48ffbffbf00950db 0xffffffff01ff1fff 0xfffffffff01ff1ff

def z176 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0fff8000fe000003 0xe0fff8000fe00000

def z177 : W := mkw 0x0000020500850994 0x4000002050085099 0x40238e0f01ff038b 0xb40238e0f01ff038

def z178 : W := mkw 0x0612513000100420 0x0061251300010042 0xbe1e71f000701c7e 0xfbe1e71f000701c7

def z179 : W := mkw 0x0000021500950db4 0x40000021500950db 0xa0039e3f007f1ff6 0x0a0039e3f007f1ff

def z180 : W := mkw 0x10c92a9d069d4fb4 0xc10c92a9d069d4fb 0xe1e39e3f0fff1fff 0xbe1e39e3f0fff1ff

def z181 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fdc7fff00000004 0x49fdc7fff0000000

def z182 : W := mkw 0x10cd2add86dd6ff6 0xc10cd2add86dd6ff 0xf1ffffff8fffffff 0xff1ffffff8ffffff

def z183 : W := mkw 0x04160000a0600000 0x004160000a060000 0x0e1e0000f070000a 0xf0e1e0000f070000

def z184 : W := mkw 0x09a980004d0a0000 0x009a980004d0a000 0x41e180000f8f0001 0x041e180000f8f000

def z185 : W := mkw 0x80402c8a00000000 0x080402c8a0000000 0x00000e0f00000000 0x000000e0f0000000

def z186 : W := mkw 0x8be9fc8a00000000 0x08be9fc8a0000000 0x0fe1fe0f00000005 0xe0fe1fe0f0000000

def z187 : W := mkw 0x26165160b060b04b 0x026165160b060b04 0x1e1c61c0f000e000 0x41e1c61c0f000e00

def z188 : W := mkw 0x200000501010b46b 0x0200000501010b46 0x200000000000fc70 0x0200000000000fc7

def z189 : W := mkw 0x82407fbf00950db4 0x482407fbf00950db 0xf023ffff01ff1fff 0xbf023ffff01ff1ff

def z190 : W := mkw 0xeffffffafbf0ff6f 0x0effffffafbf0ff6 0xfffffffffff0ffff 0xffffffffffff0fff

def z191 : W := mkw 0x0004004080402042 0x0000400408040204 0x901c01c000400072 0x0901c01c00040007

def z192 : W := mkw 0x4b2056005980990c 0x04b2056005980990 0x0e20160071801c00 0x90e20160071801c0

def z193 : W := mkw 0x12cd78cc964cf2da 0x812cd78cc964cf2d 0xffdd79ccfe4cffff 0xfffdd79ccfe4cfff

def z194 : W := mkw 0xcbe9fe8a5b80db0c 0x0cbe9fe8a5b80db0 0x6fe1fe0fff80ff8d 0xf6fe1fe0fff80ff8

def z195 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903f9fff00000007 0xa903f9fff0000000

def z196 : W := mkw 0x86527daa00000000 0x086527daa0000000 0x9e1e7fff00000006 0xe9e1e7fff0000000

def z197 : W := mkw 0x4f727f205b80db0c 0x04f727f205b80db0 0xfffe7ff0ff80ff8f 0xffffe7ff0ff80ff8

def z198 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x101c01c000000000 0x0101c01c00000000

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x901c61c000000006 0x6901c61c00000000

def z200 : W := mkw 0x0000021100910d24 0x40000021100910d2 0xa022963301f31c7e 0xba022963301f31c7

def z201 : W := mkw 0xdfffffeedfccfbde 0x8dfffffeedfccfbd 0xffffffffffccffff 0xfffffffffffccfff

def z202 : W := mkw 0x10040044864c62d2 0x810040044864c62d 0x600000008e4ce3f8 0x0600000008e4ce3f

def z203 : W := mkw 0x8f32d52200000000 0x08f32d5220000000 0x0e22963300000000 0x80e2296330000000

def z204 : W := mkw 0x20040255b0f5bdff 0x420040255b0f5bdf 0xe0239e3ff1ffffff 0xbe0239e3ff1fffff

def z205 : W := mkw 0x108d00c884482042 0x8108d00c88448204 0x101c01c000000000 0x0101c01c00000000

def z206 : W := mkw 0x8f32d52200000000 0x08f32d5220000000 0x8e239e3f00000007 0xa8e239e3f0000000

def z207 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe0011e3f004c1fff 0x2e0011e3f004c1ff

def z208 : W := mkw 0x0b607c0002004200 0x00b607c000200420 0x6fe07e008e00e38d 0xe6fe07e008e00e38

def z209 : W := mkw 0x0dbf8015ed7f04b0 0x40dbf8015ed7f04b 0xcfff803fffff007b 0xfcfff803fffff007

def z210 : W := mkw 0x0000020500850994 0x4000002050085099 0x40218e0f018f0381 0x040218e0f018f038

def z211 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0xcfff9e3fffff000f 0xfcfff9e3fffff000

def z212 : W := mkw 0x0612512010009008 0x0061251201000900 0xbe1e71f0f000fc0e 0xfbe1e71f0f000fc0

def z213 : W := mkw 0xcffbfdaa5b00d208 0x0cffbfdaa5b00d20 0x9ffffffffe00e007 0xe9ffffffffe00e00

def z214 : W := mkw 0x00c9288c00040090 0x000c9288c0004009 0xf1dd69cc004c03ff 0x6f1dd69cc004c03f

def z215 : W := mkw 0x0920000049000000 0x0092000004900000 0x0e20000071800000 0x90e2000007180000

def z216 : W := mkw 0x4b607c005b00d208 0x04b607c005b00d20 0x6fc06800fe00e38d 0x66fc06800fe00e38

def z217 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x0fff800000000003 0xe0fff80000000000

def z218 : W := mkw 0x9ffffdee864c62d2 0x89ffffdee864c62d 0xffffffff8e4ce3ff 0xeffffffff8e4ce3f

def z219 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1c71f0f000fc74 0x4be1c71f0f000fc7

def z220 : W := mkw 0x04160000a0600000 0x004160000a060000 0x0e1c0000f0000000 0x40e1c0000f000000

def z221 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x9e1e61f0f070e072 0x49e1e61f0f070e07

def z222 : W := mkw 0x8ffbffaa00800904 0x08ffbffaa0080090 0xffffffff01801f8f 0xfffffffff01801f8

def z223 : W := mkw 0x220051701010b46b 0x0220051701010b46 0xb00071f00000fc74 0x0b00071f00000fc7

def z224 : W := mkw 0x0dffa888ed6a0000 0x00dffa888ed6a000 0xdfffe9ccffff000f 0xfdfffe9ccffff000

def z225 : W := mkw 0x8ffbffbf00950db4 0x48ffbffbf00950db 0xbfffffff00001ff7 0xebfffffff00001ff

def z226 : W := mkw 0x9ffffdea86486242 0x89ffffdea8648624 0x9fffffff8e00e007 0xe9fffffff8e00e00

def z227 : W := mkw 0x2f365170f970b46b 0x02f365170f970b46 0xfffe71f0fff0fc7f 0xffffe71f0fff0fc7

def z228 : W := mkw 0x36165174b67cf6fb 0x836165174b67cf6f 0xfe1e71f0fe7cfffe 0xffe1e71f0fe7cfff

def z229 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x1fdc61c000000000 0x41fdc61c00000000

def z230 : W := mkw 0x30040054b67cf6fb 0x830040054b67cf6f 0x60000000fe7cfff8 0x160000000fe7cfff

def z231 : W := mkw 0x9ffffdea86486242 0x89ffffdea8648624 0x1fdc61c08e00e000 0x41fdc61c08e00e00

def z232 : W := mkw 0x49602e054b854b94 0x449602e054b854b9 0x41e18e0f0f8f0381 0x041e18e0f0f8f038

def z233 : W := mkw 0x4b20561559959dbc 0x44b20561559959db 0xee239e3f71ff1fff 0xbee239e3f71ff1ff

def z234 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fc06000ff80ff88 0x56fc06000ff80ff8

def z235 : W := mkw 0x10cd28c886486242 0x810cd28c88648624 0x91dd69cc8e00e007 0x691dd69cc8e00e00

def z236 : W := mkw 0x9ffffdee864c62d2 0x89ffffdee864c62d 0xffdd69cc8e4ce3ff 0x6ffdd69cc8e4ce3f

def z237 : W := mkw 0x52cd7ecc96ccfbde 0x852cd7ecc96ccfbd 0xf1dd7fcc8e4cffff 0x6f1dd7fcc8e4cfff

def z238 : W := mkw 0xcf32d7225980990c 0x0cf32d7225980990 0x0e22963371801c00 0x90e22963371801c0

def z239 : W := mkw 0x0fbbd12000000000 0x00fbbd1200000000 0x9ffff1f000000007 0xe9ffff1f00000000

def z240 : W := mkw 0x0412000000000000 0x0041200000000000 0x0e1e000000000002 0xe0e1e00000000000

def z241 : W := mkw 0x8fbbd5aa00000000 0x08fbbd5aa0000000 0x9e3f97ff00000002 0x89e3f97ff0000000

def z242 : W := mkw 0x108d00cc864c62d2 0x8108d00cc864c62d 0xf01d01cc8e4ce3fa 0x0f01d01cc8e4ce3f

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000000040007e 0x2a00000000040007

def z244 : W := mkw 0xaffffdeab060b04b 0x0affffdeab060b04 0x9ffffffff000e007 0xe9ffffffff000e00

def z245 : W := mkw 0x82407fbf00950db4 0x482407fbf00950db 0xb0007fff00001ff4 0x0b0007fff00001ff

def z246 : W := mkw 0x8412812200000000 0x0841281220000000 0x0002803300000000 0x0000280330000000

def z247 : W := mkw 0x04160215a0f50db4 0x404160215a0f50db 0xee3f9e3ff1ff1fff 0xfee3f9e3ff1ff1ff

def z248 : W := mkw 0x82407daa00000000 0x082407daa0000000 0x90007fff00000004 0x090007fff0000000

def z249 : W := mkw 0x2612533530b59dbd 0x42612533530b59db 0xee239e3f71ff1fff 0xbee239e3f71ff1ff

def z250 : W := mkw 0x4b607e055b85db9c 0x44b607e055b85db9 0x6fe1fe0fff8fff8d 0xf6fe1fe0fff8fff8

def z251 : W := mkw 0x04160000ed6a0000 0x004160000ed6a000 0x4e1e0000ffff000a 0xf4e1e0000ffff000

def z252 : W := mkw 0x0920000049000000 0x0092000004900000 0x4fe38000ffff000b 0xf4fe38000ffff000

def z253 : W := mkw 0x26165170fd7ab46b 0x026165170fd7ab46 0xfe1e71f0fffffc7e 0xffe1e71f0fffffc7

def z254 : W := mkw 0x024078001200d208 0x0024078001200d20 0x6fc07800fe00ff8d 0xf6fc07800fe00ff8

def z255 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x2fc07e00fe00ff84 0x42fc07e00fe00ff8

def z256 : W := mkw 0xcffbffaa4b804b04 0x0cffbffaa4b804b0 0xdfffffff0f800387 0xedfffffff0f80038

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x600008000000038d 0x2600008000000038

def z258 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fdc0000ffff0008 0x54fdc0000ffff000

def z259 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe3fe00ffffff8f 0xf6fe3fe00ffffff8

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x00201e0000000005 0xa00201e000000000

def z261 : W := mkw 0x0000000400040090 0x0000000040004009 0xe023880c01ff03ff 0xbe023880c01ff03f

def z262 : W := mkw 0x1dbf80cced6e20d2 0x81dbf80cced6e20d 0xdfff81ccffff007b 0xfdfff81ccffff007

def z263 : W := mkw 0x0000021500950db4 0x40000021500950db 0xc0238e3f01ff03f3 0x0c0238e3f01ff03f

def z264 : W := mkw 0x0000021500950db4 0x40000021500950db 0x40239e3f01bf1f81 0x940239e3f01bf1f8

def z265 : W := mkw 0x0612512000000000 0x0061251200000000 0x0e02103000000000 0x80e0210300000000

def z266 : W := mkw 0xaffffdfaa0702463 0x0affffdfaa070246 0x9fffffff00700077 0xe9fffffff0070007

def z267 : W := mkw 0x00040215edff0db4 0x400040215edff0db 0xe0239e3fffff1fff 0xbe0239e3fffff1ff

def z268 : W := mkw 0x0200521510959dbc 0x40200521510959db 0xee23fe3ff1ffffff 0xfee23fe3ff1fffff

def z269 : W := mkw 0x00000015001504b0 0x400000015001504b 0xa003903f007f1c7e 0xba003903f007f1c7

def z270 : W := mkw 0x0dbf8004ed6e0090 0x00dbf8004ed6e009 0xefff880cffff03ff 0xfefff880cffff03f

def z271 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe3ffffff070fc7f 0xfbe3ffffff070fc7

def z272 : W := mkw 0x0004000080400000 0x0000400008040000 0x001c00008040000a 0x6001c00008040000

def z273 : W := mkw 0x2f36d170f972b46b 0x02f36d170f972b46 0xbe3ef1f0f1f3fc7e 0xfbe3ef1f0f1f3fc7

def z274 : W := mkw 0x9ffffdee844c20d2 0x89ffffdee844c20d 0x9fffffff004c0077 0xe9fffffff004c007

def z275 : W := mkw 0x0000020500850994 0x4000002050085099 0x60219e0f018f1f8d 0xb60219e0f018f1f8

def z276 : W := mkw 0x00040215edff0db4 0x400040215edff0db 0x60000000ffff1ff8 0x160000000ffff1ff

def z277 : W := mkw 0x2612513030309429 0x0261251303030942 0x9e1e71f070301c06 0xf9e1e71f070301c0

def z278 : W := mkw 0x8fbfd522ed6a0000 0x08fbfd522ed6a000 0x4fff9633ffff000b 0xf4fff9633ffff000

def z279 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x1fffe1c000000003 0xe1fffe1c00000000

def z280 : W := mkw 0x49602e004b804b04 0x049602e004b804b0 0x61e01e000f801f8d 0xb61e01e000f801f8

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003803f00000002 0x08003803f0000000

def z282 : W := mkw 0x4ffffc00ff6ad208 0x04ffffc00ff6ad20 0x4fffe000ffffe00b 0xf4fffe000ffffe00

def z283 : W := mkw 0xaffffdfab070b46b 0x0affffdfab070b46 0xbfde71f0f070fc7e 0xfbfde71f0f070fc7

def z284 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0e3f800071ff0002 0x90e3f800071ff000

def z285 : W := mkw 0x369f51fcb47cb4fb 0x8369f51fcb47cb4f 0xbe1f71fcf07cfc7e 0xfbe1f71fcf07cfc7

def z286 : W := mkw 0x049f8000a46a0000 0x0049f8000a46a000 0x403f800001ff000b 0xb403f800001ff000

def z287 : W := mkw 0x14df28cca66c62d2 0x814df28cca66c62d 0xffdf69ccfe7ce3ff 0xfffdf69ccfe7ce3f

def z288 : W := mkw 0x10c928cc020462d2 0x810c928cc020462d 0xb1dd69cc0000e3f7 0x6b1dd69cc0000e3f

def z289 : W := mkw 0x4b647e40dbc0fb4e 0x04b647e40dbc0fb4 0xfffc7fc0ffc0ffff 0xffffc7fc0ffc0fff

def z290 : W := mkw 0x0000000069220000 0x0000000006922000 0x0000000071b30000 0x10000000071b3000

def z291 : W := mkw 0x8b607daa00000000 0x08b607daa0000000 0x9fe07fff00000005 0xe9fe07fff0000000

def z292 : W := mkw 0x0dbf8040ed6a2042 0x00dbf8040ed6a204 0xffffe1c0ffffe07f 0xfffffe1c0ffffe07

def z293 : W := mkw 0x0000021100910d24 0x40000021100910d2 0x80239e3f01b31c07 0xb80239e3f01b31c0

def z294 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x3e1c61c0f070fc78 0x53e1c61c0f070fc7

def z295 : W := mkw 0x00c9288800000000 0x000c928880000000 0x01c1080c00000001 0x001c1080c0000000

def z296 : W := mkw 0x66165370fbf0ff6f 0x066165370fbf0ff6 0xfe1e71f0fff0fffe 0xffe1e71f0fff0fff

def z297 : W := mkw 0x36df79f8b678f66b 0x836df79f8b678f66 0xbfde71f0fe70fc7e 0xfbfde71f0fe70fc7

def z298 : W := mkw 0x220053751095bdff 0x4220053751095bdf 0xf023ffff01ffffff 0xbf023ffff01fffff

def z299 : W := mkw 0x00040000ed6a0000 0x000040000ed6a000 0x40000000ffff0008 0x140000000ffff000

def z300 : W := mkw 0xcffbffbf5b95dfbc 0x4cffbffbf5b95dfb 0xffffffffffffffff 0xffffffffffffffff

def z301 : W := mkw 0x0d32800000000000 0x00d3280000000000 0x0e22800000000000 0x80e2280000000000

def z302 : W := mkw 0x324079fc1214f6fb 0x8324079fc1214f6f 0xb00079fc0000fff4 0x0b00079fc0000fff

def z303 : W := mkw 0x10cd2add86dd6ff6 0xc10cd2add86dd6ff 0xf1dd69cc8fffffff 0x7f1dd69cc8ffffff

def z304 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x1e1e71f0f030fc00 0xd1e1e71f0f030fc0

def z305 : W := mkw 0x5bed7edddfddfffe 0xc5bed7edddfddfff 0xffffffffffffffff 0xffffffffffffffff

def z306 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fdfe1ff00000002 0x49fdfe1ff0000000

def z307 : W := mkw 0x008d004084482042 0x0008d00408448204 0xf1dd61c08e4ce07f 0x6f1dd61c08e4ce07

def z308 : W := mkw 0x0000021500950db4 0x40000021500950db 0x6023800001ff1ffb 0xb6023800001ff1ff

def z309 : W := mkw 0x8ffffdea80402042 0x08ffffdea8040204 0xbfffffff8040e07f 0xebfffffff8040e07

def z310 : W := mkw 0x849b81bf001504b0 0x4849b81bf001504b 0x901f81ff007f0072 0x0901f81ff007f007

def z311 : W := mkw 0x40040200ffeadb0c 0x040040200ffeadb0 0x60000000ffffff88 0x160000000ffffff8

def z312 : W := mkw 0x0be97c8800000000 0x00be97c880000000 0x9ffd7fcc00000007 0xe9ffd7fcc0000000

def z313 : W := mkw 0x0412000020200000 0x0041200002020000 0x0e02000070300000 0x90e0200007030000

def z314 : W := mkw 0x0d368000ed6a0000 0x00d368000ed6a000 0x4e228000ffff0008 0x94e228000ffff000

def z315 : W := mkw 0x8fffffbfedff0db4 0x48fffffbfedff0db 0xffffffffffff1fff 0xfffffffffffff1ff

def z316 : W := mkw 0x4b607e155b95dfbc 0x44b607e155b95dfb 0xefe07e3fff80fffd 0xfefe07e3fff80fff

def z317 : W := mkw 0x00040044804420d2 0x000040044804420d 0xf01d69cc804ce3ff 0x6f01d69cc804ce3f

def z318 : W := mkw 0x0612512000000000 0x0061251200000000 0x1e1c61c000000000 0x41e1c61c00000000

def z319 : W := mkw 0x10402add02956ff6 0xc10402add02956ff 0xf023ffff01ffffff 0xbf023ffff01fffff

def z320 : W := mkw 0x10040044844c20d2 0x810040044844c20d 0x00000000004c0070 0x000000000004c007

def z321 : W := mkw 0x1004025586dd6ff6 0xc1004025586dd6ff 0xe0239e3f8fffffff 0xbe0239e3f8ffffff

def z322 : W := mkw 0x0d32800069220000 0x00d3280006922000 0x0e00000070000000 0x00e0000007000000

def z323 : W := mkw 0x0000020100810904 0x4000002010081090 0x0020860301830000 0x0002086030183000

def z324 : W := mkw 0x40402e0002804b04 0x040402e0002804b0 0x00000e0000000380 0x000000e000000038

def z325 : W := mkw 0x020052001080990c 0x0020052001080990 0x6e207e00f180ff8d 0xf6e207e00f180ff8

def z326 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4ffc0000ff800009 0xf4ffc0000ff80000

def z327 : W := mkw 0x020450409040b04a 0x0020450409040b04 0xbe1c71c0f040fc7e 0xfbe1c71c0f040fc7

def z328 : W := mkw 0x4b607e105b90df2c 0x04b607e105b90df2 0xefe27e30fff0ffff 0xfefe27e30fff0fff

def z329 : W := mkw 0x36df79ecb66cf2db 0x836df79ecb66cf2d 0xffdd69ccfe4ce3ff 0x6ffdd69ccfe4ce3f

def z330 : W := mkw 0x3ffff9fcff7ef6fb 0x83ffff9fcff7ef6f 0xfffff9fcffffffff 0xffffff9fcfffffff

def z331 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x0fe39e3f00000001 0x80fe39e3f0000000

def z332 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x9e1e11f070701c72 0x99e1e11f070701c7

def z333 : W := mkw 0x84dba9aa00000000 0x084dba9aa0000000 0x91dfe9ff00000007 0x691dfe9ff0000000

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x40010000004c000b 0x240010000004c000

def z335 : W := mkw 0x42407e151295dfbc 0x442407e151295dfb 0xa0007e3f0000fff4 0x0a0007e3f0000fff

def z336 : W := mkw 0x6fffff70fffaff6f 0x06fffff70fffaff6 0xfffffff0ffffffff 0xffffffff0fffffff

def z337 : W := mkw 0x0dffa800ef6a4200 0x00dffa800ef6a420 0x6fffe800ffffe38f 0xf6fffe800ffffe38

def z338 : W := mkw 0x6f365770f9f0bd6f 0x06f365770f9f0bd6 0xbe3e77f0f1f0fc7e 0xfbe3e77f0f1f0fc7

def z339 : W := mkw 0x2dbf8170ed7a2463 0x02dbf8170ed7a246 0xdfff81f0ffff007b 0xfdfff81f0ffff007

def z340 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4ffd8000ff8f0001 0x44ffd8000ff8f000

def z341 : W := mkw 0x2fbfd160fd6ab04b 0x02fbfd160fd6ab04 0x1fdc61c0fe00e000 0x41fdc61c0fe00e00

def z342 : W := mkw 0x4dffae00efea4b04 0x04dffae00efea4b0 0x4fff8e00ffff038b 0xf4fff8e00ffff038

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001080c00000007 0x28001080c0000000

def z344 : W := mkw 0x8f32d73300910d24 0x48f32d73300910d2 0x0e22963301b31c00 0x90e22963301b31c0

def z345 : W := mkw 0x10c928cc060c62d2 0x810c928cc060c62d 0xf1c169cc0e0ce3f5 0x0f1c169cc0e0ce3f

def z346 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x1ffc7fc000000005 0xe1ffc7fc00000000

def z347 : W := mkw 0x0000000002004200 0x0000000000200420 0x600000008e00e388 0x0600000008e00e38

def z348 : W := mkw 0x4fbfd600fdea990c 0x04fbfd600fdea990 0x4fff9600ffff1c0b 0xf4fff9600ffff1c0

def z349 : W := mkw 0xcf72ff225b80db0c 0x0cf72ff225b80db0 0x6fe2fe33ff80ff8d 0xf6fe2fe33ff80ff8

def z350 : W := mkw 0x0612533500950db4 0x40612533500950db 0xfe3fffff01ff1fff 0xffe3fffff01ff1ff

def z351 : W := mkw 0x00000015001504b0 0x400000015001504b 0x8003803f007f0072 0x08003803f007f007

def z352 : W := mkw 0x20040050fd7ab46b 0x020040050fd7ab46 0x60000000fffffc78 0x160000000fffffc7

def z353 : W := mkw 0x0d32821569b70db4 0x40d32821569b70db 0xee239e3f71ff1fff 0xbee239e3f71ff1ff

def z354 : W := mkw 0x000000004d0a0000 0x0000000004d0a000 0x400000000f8f0000 0x0400000000f8f000

def z355 : W := mkw 0x0dbb80004d0a0000 0x00dbb80004d0a000 0x4fff80000f8f0003 0xe4fff80000f8f000

def z356 : W := mkw 0x4b607c005b00d208 0x04b607c005b00d20 0x2fc07000fe00fc0c 0xf2fc07000fe00fc0

def z357 : W := mkw 0x00040000a0600000 0x000040000a060000 0x00000000f0700008 0x100000000f070000

def z358 : W := mkw 0x00000015001504b0 0x400000015001504b 0xc023803f01ff007b 0xbc023803f01ff007

def z359 : W := mkw 0x0000021500950db4 0x40000021500950db 0x60218e0f01ff1ff9 0x160218e0f01ff1ff

def z360 : W := mkw 0x2612533130b19d2d 0x42612533130b19d2 0x0e22963371b31c00 0x90e22963371b31c0

def z361 : W := mkw 0x0dbf8215edff0db4 0x40dbf8215edff0db 0x6fff8000ffff1ffb 0xf6fff8000ffff1ff

def z362 : W := mkw 0x8f72fdaa00000000 0x08f72fdaa0000000 0x9e22ffff00000004 0x89e22ffff0000000

def z363 : W := mkw 0x261251701010b46b 0x0261251701010b46 0xbe1e71f00000fc76 0xebe1e71f00000fc7

def z364 : W := mkw 0x349f01fca47c24f3 0x8349f01fca47c24f 0x901f01fc007c0072 0x0901f01fc007c007

def z365 : W := mkw 0x10cd28c886486242 0x810cd28c88648624 0x71dc69c08e00e38d 0x671dc69c08e00e38

def z366 : W := mkw 0x149f80cca46e20d2 0x8149f80cca46e20d 0x901f81cc007f0072 0x0901f81cc007f007

def z367 : W := mkw 0x0000021500950db4 0x40000021500950db 0xa0021e3f00701ffe 0xba0021e3f00701ff

def z368 : W := mkw 0x10cd288c864c4290 0x810cd288c864c429 0x41dd080c8e4c038b 0x641dd080c8e4c038

def z369 : W := mkw 0x420056001080990c 0x0420056001080990 0x0000160000001c00 0x00000160000001c0

def z370 : W := mkw 0x8ffbfdbf001504b0 0x48ffbfdbf001504b 0x9fffffff007f0077 0xe9fffffff007f007

def z371 : W := mkw 0x0044284082406242 0x0004428408240624 0xf1dc69c08e40e3ff 0x6f1dc69c08e40e3f

def z372 : W := mkw 0x0000020500850994 0x4000002050085099 0xc0239e3f018f0387 0xac0239e3f018f038

def z373 : W := mkw 0x008d000084480000 0x0008d00008448000 0x41ff80008fff000b 0xf41ff80008fff000

def z374 : W := mkw 0x8ffbfdaa4d0a0000 0x08ffbfdaa4d0a000 0xdfffffff0f8f0007 0xedfffffff0f8f000

def z375 : W := mkw 0x16df79ec864c62d2 0x816df79ec864c62d 0xffdf79fc8e4ce3ff 0xeffdf79fc8e4ce3f

def z376 : W := mkw 0x10cd28c886486242 0x810cd28c88648624 0x51dd61c08e4ce00b 0x651dd61c08e4ce00

def z377 : W := mkw 0xcffbffaa5b80db0c 0x0cffbffaa5b80db0 0x7ffc7fc0ff80ff8d 0xf7ffc7fc0ff80ff8

def z378 : W := mkw 0x8f72fd2200000000 0x08f72fd220000000 0x0fe2fe3300000005 0xe0fe2fe330000000

def z379 : W := mkw 0x5bed7ec8dfc8fb4e 0x85bed7ec8dfc8fb4 0x7ffc7fc0ff80ff8d 0xf7ffc7fc0ff80ff8

def z380 : W := mkw 0x49602e004b804b04 0x049602e004b804b0 0x4fe00e00ff800389 0xf4fe00e00ff80038

def z381 : W := mkw 0x0000020000800904 0x0000002000080090 0x60239e0001ff1f8f 0xb60239e0001ff1f8

def z382 : W := mkw 0x0089000000000000 0x0008900000000000 0x01dd000000000003 0x601dd00000000000

def z383 : W := mkw 0x09ad8000cd4a0000 0x009ad8000cd4a000 0x41fd80008fcf000b 0x641fd80008fcf000

def z384 : W := mkw 0x8fbbd52200000000 0x08fbbd5220000000 0x0fff963300000003 0xe0fff96330000000

def z385 : W := mkw 0x049f8015a47f04b0 0x4049f8015a47f04b 0x801f803f007f0072 0x0801f803f007f007

def z386 : W := mkw 0x0000000500050090 0x4000000050005009 0x0001800f000f0000 0x00001800f000f000

def z387 : W := mkw 0x4bed7e00dfc8db0c 0x04bed7e00dfc8db0 0x6ffd7e00ffccff8f 0xf6ffd7e00ffccff8

def z388 : W := mkw 0x0920800049020000 0x0092080004902000 0x0020800001830000 0x0002080000183000

def z389 : W := mkw 0x2fbfd375fdffbdff 0x42fbfd375fdffbdf 0xffffffffffffffff 0xffffffffffffffff

def z390 : W := mkw 0x1004025586dd6ff6 0xc1004025586dd6ff 0x600000008ffffff8 0x1600000008ffffff

def z391 : W := mkw 0x0000001000100420 0x0000000100010042 0xa002103000701c7e 0xba002103000701c7

def z392 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x71dc61c08e4ce3f8 0x471dc61c08e4ce3f

def z393 : W := mkw 0x008d0000ed6a0000 0x0008d0000ed6a000 0x41dd0000ffff000b 0x741dd0000ffff000

def z394 : W := mkw 0x0ffffc00ed6a0000 0x00ffffc00ed6a000 0x4ffffe00ffff000f 0xf4ffffe00ffff000

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x0022963300000000 0x8002296330000000

def z396 : W := mkw 0x0200500010009008 0x0020050001000900 0x200070000000fc04 0x0200070000000fc0

def z397 : W := mkw 0x0000021500950db4 0x40000021500950db 0xa0239e3f00001ff7 0xaa0239e3f00001ff

def z398 : W := mkw 0x0000021100910d24 0x40000021100910d2 0x60229e3301b31f8d 0xb60229e3301b31f8

def z399 : W := mkw 0x0f727d2000000000 0x00f727d200000000 0x9ffe7ff000000007 0xe9ffe7ff00000000

def z400 : W := mkw 0x0b607c0010009008 0x00b607c001000900 0x2fe07e00f000fc0d 0xf2fe07e00f000fc0

def z401 : W := mkw 0x0dbb80006d2a0000 0x00dbb80006d2a000 0x4fe380007fbf0001 0x94fe380007fbf000

def z402 : W := mkw 0x20040050b070b46b 0x020040050b070b46 0xb01c61c0f070fc7e 0x7b01c61c0f070fc7

def z403 : W := mkw 0x420052005b80db0c 0x0420052005b80db0 0x6e007000ff80ff8c 0xf6e007000ff80ff8

def z404 : W := mkw 0x42407c001200d208 0x042407c001200d20 0x000060000000e000 0x0000060000000e00

def z405 : W := mkw 0x0920000049000000 0x0092000004900000 0x0fc00000fe000000 0x40fc00000fe00000

def z406 : W := mkw 0x8ffffdaaa0600000 0x08ffffdaaa060000 0x9ffffffff070000f 0xf9ffffffff070000

def z407 : W := mkw 0x0200500010009008 0x0020050001000900 0x0e00100070001c00 0x90e00100070001c0

def z408 : W := mkw 0x8ffbffbb00910d24 0x48ffbffbb00910d2 0x9fffffff01b31c07 0xf9fffffff01b31c0

def z409 : W := mkw 0x89e9ac8a4d0a0000 0x089e9ac8a4d0a000 0x41e18e0f0f8f0001 0x041e18e0f0f8f000

def z410 : W := mkw 0x89e9ae8f00850994 0x489e9ae8f0085099 0x41e18e0f018f0381 0x041e18e0f018f038

def z411 : W := mkw 0x0040280002004200 0x0004028000200420 0x41c008000e000381 0x041c008000e00038

def z412 : W := mkw 0x0d368000e9620000 0x00d368000e962000 0x0e3e8000f1f3000a 0xf0e3e8000f1f3000

def z413 : W := mkw 0x8f32d52200000000 0x08f32d5220000000 0x9e3ef7f300000006 0xe9e3ef7f30000000

def z414 : W := mkw 0x00c9288800000000 0x000c928880000000 0x91ffffff00000007 0xe91ffffff0000000

def z415 : W := mkw 0x0dbf8211edfb0d24 0x40dbf8211edfb0d2 0x4fff9633ffff1c0b 0xf4fff9633ffff1c0

def z416 : W := mkw 0x42407e001280db0c 0x042407e001280db0 0x61c07e008e00ff8d 0x661c07e008e00ff8

def z417 : W := mkw 0x108d00dd845d24f2 0xc108d00dd845d24f 0x901f81ff007f0072 0x0901f81ff007f007

def z418 : W := mkw 0x8f32d52269220000 0x08f32d5226922000 0x0e22963371b30000 0x90e22963371b3000

def z419 : W := mkw 0x06165000b0609008 0x006165000b060900 0x2e1e7000f070fc0e 0xf2e1e7000f070fc0

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0239e3f01ff000f 0xbc0239e3f01ff000

def z421 : W := mkw 0x26165170a0702463 0x026165170a070246 0x9e1e71f000700076 0xe9e1e71f00070007

def z422 : W := mkw 0x26165160b060b04b 0x026165160b060b04 0x9e1e71f0f000e006 0xe9e1e71f0f000e00

def z423 : W := mkw 0x19eda8cccf4e62d2 0x819eda8cccf4e62d 0xf1fde9cc8fcfe3ff 0x6f1fde9cc8fcfe3f

def z424 : W := mkw 0x108d0044864c62d2 0x8108d0044864c62d 0x61dd00008e4ce3fb 0x661dd00008e4ce3f

def z425 : W := mkw 0xaffffdeab060b04b 0x0affffdeab060b04 0x1fdc61c0f000e000 0x41fdc61c0f000e00

def z426 : W := mkw 0x4b2056005980990c 0x04b2056005980990 0x4fe01600ff801c09 0xf4fe01600ff801c0

def z427 : W := mkw 0x0920021549950db4 0x40920021549950db 0xefe39e3fffff1fff 0xfefe39e3fffff1ff

def z428 : W := mkw 0x049f8000a46a0000 0x0049f8000a46a000 0x001c000000000000 0x0001c00000000000

def z429 : W := mkw 0x8dffac8aed6a0000 0x08dffac8aed6a000 0x4fff8e0fffff000b 0xf4fff8e0fffff000

def z430 : W := mkw 0x09a980004d0a0000 0x009a980004d0a000 0x01c000000e000000 0x001c000000e00000

def z431 : W := mkw 0x09a9800000000000 0x009a980000000000 0x01e1800000000001 0x001e180000000000

def z432 : W := mkw 0xa6567dfab070b46b 0x0a6567dfab070b46 0xbe1e7ffff070fc7e 0xfbe1e7ffff070fc7

def z433 : W := mkw 0x82407daa00000000 0x082407daa0000000 0x100061c000000000 0x0100061c00000000

def z434 : W := mkw 0x99e9ac8e060c4290 0x899e9ac8e060c429 0x41e18e0f0e0c0381 0x041e18e0f0e0c038

def z435 : W := mkw 0x10cd28cc844c20d2 0x810cd28cc844c20d 0x91dd69cc004c0077 0x691dd69cc004c007

def z436 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x4fff800001ff000b 0xf4fff800001ff000

def z437 : W := mkw 0x6f767f75fbf5ffff 0x46f767f75fbf5fff 0xffffffffffffffff 0xffffffffffffffff

def z438 : W := mkw 0x400000005b00d208 0x0400000005b00d20 0x00000000fe00e000 0x000000000fe00e00

def z439 : W := mkw 0xaffbfdba30309429 0x0affbfdba3030942 0x9fffffff70301c07 0xf9fffffff70301c0

def z440 : W := mkw 0x0fbfd000fd6a9008 0x00fbfd000fd6a900 0x6ffff000fffffc0f 0xf6ffff000fffffc0

def z441 : W := mkw 0x24160175a07524f3 0x424160175a07524f 0x901f81ff007f0072 0x0901f81ff007f007

def z442 : W := mkw 0x89e9ac8a00000000 0x089e9ac8a0000000 0x81e39e3f00000007 0xa81e39e3f0000000

def z443 : W := mkw 0x09ad8000ed6a0000 0x009ad8000ed6a000 0x41e18000ffff0009 0x141e18000ffff000

def z444 : W := mkw 0x0000001000100420 0x0000000100010042 0xa0239e3f00701c7f 0xba0239e3f00701c7

def z445 : W := mkw 0x0000020500850994 0x4000002050085099 0xe0218e0f01cf03ff 0x2e0218e0f01cf03f

def z446 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe002103001ff1ffe 0xbe002103001ff1ff

def z447 : W := mkw 0x049f8215a4ff0db4 0x4049f8215a4ff0db 0xe03f9e3f01ff1fff 0xbe03f9e3f01ff1ff

def z448 : W := mkw 0x0000021100910d24 0x40000021100910d2 0x4023963301ff1c0b 0xb4023963301ff1c0

def z449 : W := mkw 0x0b20500059009008 0x00b2050005900900 0x6fe07000ff80fc0d 0xf6fe07000ff80fc0

def z450 : W := mkw 0x09a982154d9f0db4 0x409a982154d9f0db 0xe1e39e3f0fff1fff 0xbe1e39e3f0fff1ff

def z451 : W := mkw 0x94dfa9ee864c62d2 0x894dfa9ee864c62d 0xf1dfe9ff8e4ce3ff 0x6f1dfe9ff8e4ce3f

def z452 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0fde0000fe70000a 0xf0fde0000fe70000

def z453 : W := mkw 0x1dffa88cef6e4290 0x81dffa88cef6e429 0x4fff880cffff038b 0xf4fff880cffff038

def z454 : W := mkw 0x8f32d73700950db4 0x48f32d73700950db 0xee239e3f01ff1fff 0xbee239e3f01ff1ff

def z455 : W := mkw 0x0dbf8000a0600000 0x00dbf8000a060000 0x0fff8000f070000b 0xf0fff8000f070000

def z456 : W := mkw 0x4b607c005b00d208 0x04b607c005b00d20 0x4fe06000ff80e009 0xf4fe06000ff80e00

def z457 : W := mkw 0x09a980004d0a0000 0x009a980004d0a000 0x41e380000fff000b 0xb41e380000fff000

def z458 : W := mkw 0x0b20540000000000 0x00b2054000000000 0x0e20160000000000 0x80e2016000000000

def z459 : W := mkw 0x10442844864c62d2 0x810442844864c62d 0x61c068008e4ce3fd 0x661c068008e4ce3f

def z460 : W := mkw 0xa69fd1fab070b46b 0x0a69fd1fab070b46 0xbe1ff1fff070fc7e 0xfbe1ff1fff070fc7

def z461 : W := mkw 0x42407e151295dfbc 0x442407e151295dfb 0xe023fe3f01ffffff 0xbe023fe3f01fffff

def z462 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0fdf8000fe7f0002 0x40fdf8000fe7f000

def z463 : W := mkw 0x9ffbfdee020462d2 0x89ffbfdee020462d 0xbfffffff0000e3f7 0xebfffffff0000e3f

def z464 : W := mkw 0x26567970b270f66b 0x026567970b270f66 0xffde79f0fe70ffff 0xfffde79f0fe70fff

def z465 : W := mkw 0x4f32d60079a2990c 0x04f32d60079a2990 0x0e22960071b31c00 0x90e22960071b31c0

def z466 : W := mkw 0x049f8000a46a0000 0x0049f8000a46a000 0x41df80008e7f000b 0x641df80008e7f000

def z467 : W := mkw 0x24160170b070b46b 0x024160170b070b46 0xb01e01f0f070fc7a 0x1b01e01f0f070fc7

def z468 : W := mkw 0x0920020049800904 0x0092002004980090 0x6fe01e00ff801f8d 0xf6fe01e00ff801f8

def z469 : W := mkw 0x0000020500850994 0x4000002050085099 0x00000e0f00000380 0x000000e0f0000038

def z470 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x61e07e000f80ff85 0x061e07e000f80ff8

def z471 : W := mkw 0x0616516080402042 0x0061651608040204 0xbe1e71f08040e07e 0xebe1e71f08040e07

def z472 : W := mkw 0x0412012000000000 0x0041201200000000 0x901e01f000000002 0x0901e01f00000000

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x000200000070000a 0xb000200000070000

def z474 : W := mkw 0x0dbf8200edea0904 0x00dbf8200edea090 0x6fff9e00ffff1f8f 0xf6fff9e00ffff1f8

def z475 : W := mkw 0x42407e005b80db0c 0x042407e005b80db0 0x60007e00ff80ff8c 0x160007e00ff80ff8

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x00038000007f0002 0x000038000007f000

def z477 : W := mkw 0x220451709050b46b 0x0220451709050b46 0xb01c71f08040fc7e 0x6b01c71f08040fc7

def z478 : W := mkw 0x26165160b060b04b 0x026165160b060b04 0x3e1c71c0f000fc0c 0xf3e1c71c0f000fc0

def z479 : W := mkw 0x24160170a0702463 0x024160170a070246 0xb01e11f000701c7e 0xbb01e11f000701c7

def z480 : W := mkw 0x8be9fdaa00000000 0x08be9fdaa0000000 0x91e1ffff00000005 0x091e1ffff0000000

def z481 : W := mkw 0x00cd28c880402042 0x000cd28c88040204 0xb1dd69cc8040e07f 0x6b1dd69cc8040e07

def z482 : W := mkw 0x4b20561159919d2c 0x44b20561159919d2 0x0e22963371b31c00 0x90e22963371b31c0

def z483 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe0001e3f01ff1ffc 0x1e0001e3f01ff1ff

def z484 : W := mkw 0x99edacce864c62d2 0x899edacce864c62d 0xf1fdefcf8e4ce3ff 0x6f1fdefcf8e4ce3f

def z485 : W := mkw 0x24160160a0602043 0x024160160a060204 0x101c01c000000000 0x0101c01c00000000

def z486 : W := mkw 0x5bed7cccdf4cf2da 0x85bed7cccdf4cf2d 0xffdd69ccfe4ce3ff 0x6ffdd69ccfe4ce3f

def z487 : W := mkw 0x108d00cc844c20d2 0x8108d00cc844c20d 0xd1dd01cc8e4c007b 0x6d1dd01cc8e4c007

def z488 : W := mkw 0x2fbfd130fd7a9429 0x02fbfd130fd7a942 0x4fff9030ffff1c0b 0xf4fff9030ffff1c0

def z489 : W := mkw 0x0000001100110420 0x4000000110011042 0x0002803300330000 0x0000280330033000

def z490 : W := mkw 0x8ffbfdba00100420 0x08ffbfdba0010042 0xbfffffff00701c7f 0xfbfffffff00701c7

def z491 : W := mkw 0x24160050b070b46b 0x024160050b070b46 0x2e1e0000f070fc7a 0xf2e1e0000f070fc7

def z492 : W := mkw 0x6f767d60fb60f24b 0x06f767d60fb60f24 0x1fdc61c0fe00e000 0x41fdc61c0fe00e00

def z493 : W := mkw 0x60040250fbf0ff6f 0x060040250fbf0ff6 0x60000000fff0fff8 0x160000000fff0fff

def z494 : W := mkw 0x400002155b95dfbc 0x4400002155b95dfb 0xe0239e3fffffffff 0xbe0239e3ffffffff

def z495 : W := mkw 0x00cd288884480000 0x000cd28888448000 0xd1dd69cc8e4c000f 0x6d1dd69cc8e4c000

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x0023800000000003 0xa002380000000000

def z497 : W := mkw 0x0dbf8205edef0994 0x40dbf8205edef099 0x4fff8e0fffff038b 0xf4fff8e0fffff038

def z498 : W := mkw 0x4b607e155b95dfbc 0x44b607e155b95dfb 0x6fe07e00fffffffd 0xf6fe07e00fffffff

def z499 : W := mkw 0x4b607c005b00d208 0x04b607c005b00d20 0x0fe07e00fe00e005 0xe0fe07e00fe00e00

def z500 : W := mkw 0x04160040a0602042 0x004160040a060204 0xbe1e61c0f070e07e 0xfbe1e61c0f070e07

def z501 : W := mkw 0x5b607ecc5b84fbde 0x85b607ecc5b84fbd 0xffe07fccff80fffd 0xfffe07fccff80fff

def z502 : W := mkw 0x6f767f60fbe0fb4f 0x06f767f60fbe0fb4 0x7ffc7fc0ff80ff8d 0xf7ffc7fc0ff80ff8

def z503 : W := mkw 0x0dbb800069220000 0x00dbb80006922000 0x0fff800071b30003 0xf0fff800071b3000

def z504 : W := mkw 0x008d000084480000 0x0008d00008448000 0x01dc00008e000000 0x401dc00008e00000

def z505 : W := mkw 0x10040044ef6e62d2 0x810040044ef6e62d 0x60000000ffffe3f8 0x160000000ffffe3f

def z506 : W := mkw 0x26165130b0709429 0x026165130b070942 0x0e1e1030f0701c0a 0xf0e1e1030f0701c0

def z507 : W := mkw 0xaffbfdfa1010b46b 0x0affbfdfa1010b46 0xbfffffff0000fc77 0xebfffffff0000fc7

def z508 : W := mkw 0x10040044864c62d2 0x810040044864c62d 0xf01c61c08e4ce3fe 0x6f01c61c08e4ce3f

def z509 : W := mkw 0x4b607e045b84db9c 0x04b607e045b84db9 0xefe17e0cffccffff 0xfefe17e0cffccfff

def z510 : W := mkw 0x26df79f8b070b46b 0x026df79f8b070b46 0xbfdf79fcf070fc7f 0xfbfdf79fcf070fc7

def z511 : W := mkw 0x8f32d52200000000 0x08f32d5220000000 0x0e00000000000000 0x00e0000000000000

def z512 : W := mkw 0x0b607c0049000000 0x00b607c004900000 0x4fe07e00ff80000d 0xf4fe07e00ff80000

def z513 : W := mkw 0x2fbfd170fd7ab46b 0x02fbfd170fd7ab46 0xbfde71f0fe70fc7e 0xfbfde71f0fe70fc7

def z514 : W := mkw 0x8ffffdaaed6a0000 0x08ffffdaaed6a000 0x9ffffffffe000007 0xe9ffffffffe00000

def z515 : W := mkw 0x0000000400040090 0x0000000040004009 0xe0239e3f004c03ff 0xae0239e3f004c03f

def z516 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x91dd61cc8e4ce072 0x491dd61cc8e4ce07

def z517 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe0219e3f018f1ff5 0x0e0219e3f018f1ff

def z518 : W := mkw 0x14dfa8cca66e62d2 0x814dfa8cca66e62d 0xf1dfe9cc8e7fe3ff 0x6f1dfe9cc8e7fe3f

def z519 : W := mkw 0x0dfba88800000000 0x00dfba8880000000 0x9fffe9cc00000007 0xe9fffe9cc0000000

def z520 : W := mkw 0x34df29fca67c66f3 0x834df29fca67c66f 0xf1df69fc8e7ce3ff 0x6f1df69fc8e7ce3f

def z521 : W := mkw 0x4dbf8200ffeadb0c 0x04dbf8200ffeadb0 0x6fff8000ffffff8b 0xf6fff8000ffffff8

def z522 : W := mkw 0x8200552200000000 0x0820055220000000 0x0000163300000000 0x0000016330000000

def z523 : W := mkw 0x4f72fe007ba2db0c 0x04f72fe007ba2db0 0x6fe2fe00ffb3ff8d 0xf6fe2fe00ffb3ff8

def z524 : W := mkw 0x0000001000100420 0x0000000100010042 0xe023903001ff1c7f 0xbe023903001ff1c7

def z525 : W := mkw 0x22045170b070b46b 0x022045170b070b46 0xb00071f0f070fc7c 0x1b00071f0f070fc7

def z526 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xdfffffff01ff000f 0xfdfffffff01ff000

def z527 : W := mkw 0x008d021584dd0db4 0x4008d021584dd0db 0xe1ff9e3f8fff1fff 0xfe1ff9e3f8fff1ff

def z528 : W := mkw 0x1dffa8ccef6e62d2 0x81dffa8ccef6e62d 0xffdd69ccfe4ce3ff 0x6ffdd69ccfe4ce3f

def z529 : W := mkw 0x0000020000800904 0x0000002000080090 0x6000000001801f88 0x16000000001801f8

def z530 : W := mkw 0x6b607f705b90ff6f 0x06b607f705b90ff6 0xffe07ff0ff80fffd 0xfffe07ff0ff80fff

def z531 : W := mkw 0xcb607faa5b80db0c 0x0cb607faa5b80db0 0xffe07fffff80ff8d 0xfffe07fffff80ff8

def z532 : W := mkw 0x4b2056005980990c 0x04b2056005980990 0x2e207600f180fc0c 0xf2e207600f180fc0

def z533 : W := mkw 0x5bed7cc8df48f24a 0x85bed7cc8df48f24 0x1fdc61c0fe00e000 0x41fdc61c0fe00e00

def z534 : W := mkw 0x49602c004b004200 0x049602c004b00420 0x01c000000e000000 0x001c000000e00000

def z535 : W := mkw 0x0000020000800904 0x0000002000080090 0x0020160001801c00 0x90020160001801c0

def z536 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fde71f000000006 0xe9fde71f00000000

def z537 : W := mkw 0xcffbffaa1280db0c 0x0cffbffaa1280db0 0xbfffffff0000ff87 0xebfffffff0000ff8

def z538 : W := mkw 0x52407ecc1284fbde 0x852407ecc1284fbd 0xb0007fcc0000fff4 0x0b0007fcc0000fff

def z539 : W := mkw 0x400002005980990c 0x0400002005980990 0x0000000071801c00 0x10000000071801c0

def z540 : W := mkw 0x0000000400040090 0x0000000040004009 0xa000080c000003f4 0x0a000080c000003f

def z541 : W := mkw 0x6f727f307bb0df2d 0x06f727f307bb0df2 0x6fe27e30ffb0ff8d 0xf6fe27e30ffb0ff8

def z542 : W := mkw 0x10000004060c4290 0x810000004060c429 0x400000000e0c0380 0x0400000000e0c038

def z543 : W := mkw 0x0000001000100420 0x0000000100010042 0x0002103000301c00 0x90002103000301c0

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x00218e0f00000001 0x000218e0f0000000

def z545 : W := mkw 0x0000004000002042 0x0000000400000204 0xb00061c00000e074 0x0b00061c00000e07

def z546 : W := mkw 0x0000020500850994 0x4000002050085099 0x40000000018f0380 0x040000000018f038

def z547 : W := mkw 0x00cd280086484200 0x000cd28008648420 0x61dd68008e4ce38f 0x661dd68008e4ce38

def z548 : W := mkw 0x0040280002004200 0x0004028000200420 0x01c060008e00e000 0x401c060008e00e00

def z549 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x4fe06e00ff80e381 0x44fe06e00ff80e38

def z550 : W := mkw 0x26165175b075b4fb 0x426165175b075b4f 0xbe1ff1fff07ffc7e 0xfbe1ff1fff07ffc7

def z551 : W := mkw 0x0040280002004200 0x0004028000200420 0x200068000000e384 0x0200068000000e38

def z552 : W := mkw 0x49e9ae004f8a4b04 0x049e9ae004f8a4b0 0x41e18e000f8f0381 0x041e18e000f8f038

def z553 : W := mkw 0x4920060049800904 0x0492006004980090 0x0020060001800000 0x0002006000180000

def z554 : W := mkw 0x24160170a0702463 0x024160170a070246 0xb01e61f08070e07e 0x6b01e61f08070e07

def z555 : W := mkw 0x0004005080502462 0x0000400508050246 0xb01e71f08070fc7e 0xfb01e71f08070fc7

def z556 : W := mkw 0x4b2056005980990c 0x04b2056005980990 0x6e201e0071801f8d 0xb6e201e0071801f8

def z557 : W := mkw 0x049b800000000000 0x0049b80000000000 0x001f800000000002 0x0001f80000000000

def z558 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xd1dd09cc0e4c03f3 0x0d1dd09cc0e4c03f

def z559 : W := mkw 0x0200500000000000 0x0020050000000000 0x0e00700000000004 0xe0e0070000000000

def z560 : W := mkw 0xaf32d53230309429 0x0af32d5323030942 0x0e22963370301c00 0x90e22963370301c0

def z561 : W := mkw 0x09a982054d8f0994 0x409a982054d8f099 0x41e18e0f0f8f0381 0x041e18e0f0f8f038

def z562 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x8fff9e3f00000007 0xe8fff9e3f0000000

def z563 : W := mkw 0x261251703030b46b 0x0261251703030b46 0xbe0271f07030fc74 0x9be0271f07030fc7

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c000008e000009 0x641c000008e00000

def z565 : W := mkw 0x62407f701290ff6f 0x062407f701290ff6 0xb0007ff00000fff4 0x0b0007ff00000fff

def z566 : W := mkw 0x8ffffdaaed6a0000 0x08ffffdaaed6a000 0x5fffe1c0ffff000b 0xf5fffe1c0ffff000

def z567 : W := mkw 0x108d02dd84dd2df6 0xc108d02dd84dd2df 0xf03f9fff01ff1fff 0xbf03f9fff01ff1ff

def z568 : W := mkw 0xc9e9ae8a4b804b04 0x0c9e9ae8a4b804b0 0x41e18e0f0f800381 0x041e18e0f0f80038

def z569 : W := mkw 0x0dbb800000000000 0x00dbb80000000000 0x0fdc000000000000 0x40fdc00000000000

def z570 : W := mkw 0x26165160b060b04b 0x026165160b060b04 0xbe1c61c0f040e07e 0x6be1c61c0f040e07

def z571 : W := mkw 0x36df79e8b668f24b 0x836df79e8b668f24 0x1fdc61c0fe00e000 0x41fdc61c0fe00e00

def z572 : W := mkw 0x24160170a0702463 0x024160170a070246 0x9e1e01f0f070007a 0xf9e1e01f0f070007

def z573 : W := mkw 0x00402a1502954fb4 0x400402a1502954fb 0xe1e3fe3f8fffffff 0xfe1e3fe3f8ffffff

def z574 : W := mkw 0x049f8000ed6a0000 0x0049f8000ed6a000 0x401f8000ffff000a 0x1401f8000ffff000

def z575 : W := mkw 0x0920000000000000 0x0092000000000000 0x0fe0000000000001 0xe0fe000000000000

def z576 : W := mkw 0x00c9288800000000 0x000c928880000000 0x11dc61c000000000 0x411dc61c00000000

def z577 : W := mkw 0x40402a005b80db0c 0x040402a005b80db0 0x61c06800ff80ff8d 0x761c06800ff80ff8

def z578 : W := mkw 0x400002004b804b04 0x0400002004b804b0 0x400000000f800380 0x0400000000f80038

def z579 : W := mkw 0x0fbfd120ed6a0000 0x00fbfd120ed6a000 0xdffff1f0ffff000f 0xfdffff1f0ffff000

def z580 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fdd69cc00000007 0x69fdd69cc0000000

def z581 : W := mkw 0x10c9288c060c4290 0x810c9288c060c429 0xe1c1080c0e4c03ff 0x2e1c1080c0e4c03f

def z582 : W := mkw 0x104028c802006242 0x8104028c80200624 0x100061c00000e000 0x0100061c00000e00

def z583 : W := mkw 0x26165371b0f1bd6f 0x426165371b0f1bd6 0xbe3ef7f3f1f3fc7e 0xfbe3ef7f3f1f3fc7

def z584 : W := mkw 0xaffffdfafd7ab46b 0x0affffdfafd7ab46 0xfffffffffffffc7f 0xffffffffffffffc7

def z585 : W := mkw 0x66567f70b2f0ff6f 0x066567f70b2f0ff6 0xbe1e7ff0f070fffe 0xfbe1e7ff0f070fff

def z586 : W := mkw 0x0dbb821500950db4 0x40dbb821500950db 0xefff9e3f01ff1fff 0xfefff9e3f01ff1ff

def z587 : W := mkw 0x849f81aaa46a0000 0x0849f81aaa46a000 0x901f81ff007f0002 0x0901f81ff007f000

def z588 : W := mkw 0x49602e154b954fb4 0x449602e154b954fb 0xe1e39e3f0fff1fff 0xbe1e39e3f0fff1ff

def z589 : W := mkw 0x82407daa00000000 0x082407daa0000000 0x9023ffff00000007 0xa9023ffff0000000

def z590 : W := mkw 0x00898000040a0000 0x000898000040a000 0x00018000000f0000 0x000018000000f000

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000001ff0008 0x14000000001ff000

def z592 : W := mkw 0x220053751095bdff 0x4220053751095bdf 0xb0007fff0000fff4 0x0b0007fff0000fff

def z593 : W := mkw 0x5be97e8c5f8cdb9c 0x85be97e8c5f8cdb9 0x6fe17e0cff8cff8d 0xf6fe17e0cff8cff8

def z594 : W := mkw 0x2f767d70b070b46b 0x02f767d70b070b46 0xbffe7ff0f070fc7f 0xfbffe7ff0f070fc7

def z595 : W := mkw 0x8ffffdaa84480000 0x08ffffdaa8448000 0xdfffffff8e4c000f 0xedfffffff8e4c000

def z596 : W := mkw 0x10cd28ccef6e62d2 0x810cd28ccef6e62d 0xf1dd69ccffffe3ff 0x7f1dd69ccffffe3f

def z597 : W := mkw 0x4b607e005980990c 0x04b607e005980990 0x0fe07e0071801c05 0xf0fe07e0071801c0

def z598 : W := mkw 0x49602e004b804b04 0x049602e004b804b0 0x61e06e008f80e38d 0x661e06e008f80e38

def z599 : W := mkw 0x59ed2ecccfcc6bd6 0x859ed2ecccfcc6bd 0xf1fd6fcc8fcce3ff 0x6f1fd6fcc8fcce3f

def z600 : W := mkw 0x00c92a9d00950db4 0x400c92a9d00950db 0xf1ffffff01ff1fff 0xff1ffffff01ff1ff

def z601 : W := mkw 0x10cd28c886486242 0x810cd28c88648624 0xb1dc61c08e40e07e 0x6b1dc61c08e40e07

def z602 : W := mkw 0x0b607c0000000000 0x00b607c000000000 0x8fe3fe3f00000007 0xe8fe3fe3f0000000

def z603 : W := mkw 0x0000021000900d24 0x00000021000900d2 0xe0221e3001f01fff 0xbe0221e3001f01ff

def z604 : W := mkw 0x8920840200000000 0x0892084020000000 0x0020860300000000 0x0002086030000000

def z605 : W := mkw 0x26165174b074b4fb 0x026165174b074b4f 0xfe1f79fcf07cffff 0xffe1f79fcf07cfff

def z606 : W := mkw 0x0b607c0000000000 0x00b607c000000000 0x0fc0600000000000 0x40fc060000000000

def z607 : W := mkw 0x096028004b004200 0x0096028004b00420 0x6fe06800ff80e38d 0xf6fe06800ff80e38

def z608 : W := mkw 0xcfffffaaffeadb0c 0x0cfffffaaffeadb0 0xffffffffffffff8f 0xfffffffffffffff8

def z609 : W := mkw 0x1089008c040c0090 0x81089008c040c009 0x0001000c000c0000 0x00001000c000c000

def z610 : W := mkw 0x00402a0002804b04 0x000402a0002804b0 0x61e07e008f80ff8d 0xf61e07e008f80ff8

def z611 : W := mkw 0x00000015001504b0 0x400000015001504b 0xe003883f007f03ff 0x2e003883f007f03f

def z612 : W := mkw 0x30cd28dcb67cf6fb 0x830cd28dcb67cf6f 0xf1dd69ccfe7cffff 0x7f1dd69ccfe7cfff

def z613 : W := mkw 0x6b647e50fbf0ff6f 0x06b647e50fbf0ff6 0x6fe07e00fff0fffd 0xf6fe07e00fff0fff

def z614 : W := mkw 0x02407c0000000000 0x002407c000000000 0x00007e0000000004 0x000007e000000000

def z615 : W := mkw 0x049f8000a46a0000 0x0049f8000a46a000 0x0e1f8000f07f000a 0xf0e1f8000f07f000

def z616 : W := mkw 0x0dbb800049000000 0x00dbb80004900000 0x4fff8000ff80000b 0xf4fff8000ff80000

def z617 : W := mkw 0x008d000084480000 0x0008d00008448000 0x001d0000004c0002 0x0001d0000004c000

def z618 : W := mkw 0x00000015001504b0 0x400000015001504b 0x80239e3f007f0077 0xa80239e3f007f007

def z619 : W := mkw 0x19e9a88c4f0e4290 0x819e9a88c4f0e429 0x41e1880c0f8f0381 0x041e1880c0f8f038

def z620 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x2e021030f070fc78 0x92e021030f070fc7

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x40218000018f0001 0x040218000018f000

def z622 : W := mkw 0x36df7bfdb6fdffff 0xc36df7bfdb6fdfff 0xffffffffffffffff 0xffffffffffffffff

def z623 : W := mkw 0x1dffa8c8ef6a6242 0x81dffa8c8ef6a624 0x1fdc61c0fe00e000 0x41fdc61c0fe00e00

def z624 : W := mkw 0x0004004080402042 0x0000400408040204 0x200000008040e078 0x0200000008040e07

def z625 : W := mkw 0x4b2056005b80db0c 0x04b2056005b80db0 0x6e201600ff80ff88 0x96e201600ff80ff8

def z626 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0ffe8000ffb30000 0xd0ffe8000ffb3000

def z627 : W := mkw 0x10402add02956ff6 0xc10402add02956ff 0xb0007fff0000fff4 0x0b0007fff0000fff

def z628 : W := mkw 0x0412800020220000 0x0041280002022000 0x0002800000330000 0x0000280000033000

def z629 : W := mkw 0x1bed7ccc864c62d2 0x81bed7ccc864c62d 0xfffd7fcc8e4ce3ff 0xefffd7fcc8e4ce3f

def z630 : W := mkw 0x0000021100910d24 0x40000021100910d2 0x0000000001b31c00 0x10000000001b31c0

def z631 : W := mkw 0x249f8170a47a2463 0x0249f8170a47a246 0x901f81f0007f0072 0x0901f81f0007f007

def z632 : W := mkw 0x09602c0000000000 0x009602c000000000 0x01e00e0000000001 0x001e00e000000000

def z633 : W := mkw 0x0b607e1500950db4 0x40b607e1500950db 0xefe3fe3f01ff1fff 0xfefe3fe3f01ff1ff

def z634 : W := mkw 0x10c9288806084200 0x810c928880608420 0x01c000000e000000 0x001c000000e00000

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002103000000006 0xa800210300000000

def z636 : W := mkw 0x0000020000800904 0x0000002000080090 0x20001e0000001f84 0x020001e0000001f8

def z637 : W := mkw 0x26165160b060b04b 0x026165160b060b04 0x1e1e61c0f070e00a 0xf1e1e61c0f070e00

def z638 : W := mkw 0x26165370b0f0bd6f 0x026165370b0f0bd6 0xfe3e7ff0f1f0ffff 0xffe3e7ff0f1f0fff

def z639 : W := mkw 0x0004000084480000 0x0000400008448000 0x400000008e4c0008 0x0400000008e4c000

def z640 : W := mkw 0xa2407dfa1010b46b 0x0a2407dfa1010b46 0xb0007fff0000fc74 0x0b0007fff0000fc7

def z641 : W := mkw 0x4b607e004b804b04 0x04b607e004b804b0 0x4fe07e000f800385 0xe4fe07e000f80038

def z642 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x9fff81ff00000003 0xe9fff81ff0000000

def z643 : W := mkw 0x09a980004d0a0000 0x009a980004d0a000 0x4fe18000ff8f0009 0xf4fe18000ff8f000

def z644 : W := mkw 0x9fffffff86dd6ff6 0xc9fffffff86dd6ff 0xffffffff8fffffff 0xfffffffff8ffffff

def z645 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x61c1080c8e4ce3f9 0x061c1080c8e4ce3f

def z646 : W := mkw 0x10c9288c060c4290 0x810c9288c060c429 0xd1dd69cc0e0c0387 0x6d1dd69cc0e0c038

def z647 : W := mkw 0x269f5170b478b46b 0x0269f5170b478b46 0xffdf71f0fe7cfc7f 0xfffdf71f0fe7cfc7

def z648 : W := mkw 0x04160000a0600000 0x004160000a060000 0x001e000000700002 0x0001e00000070000

def z649 : W := mkw 0x0000020400840994 0x0000002040084099 0xe0211e0c01cc1fff 0xbe0211e0c01cc1ff

def z650 : W := mkw 0x0000021500950db4 0x40000021500950db 0xa0229e3f01b31ff4 0x9a0229e3f01b31ff

def z651 : W := mkw 0x2dbf8050fd7ab46b 0x02dbf8050fd7ab46 0x6fff8000fffffc7b 0xf6fff8000fffffc7

def z652 : W := mkw 0x10cd2acd86cd6bd6 0xc10cd2acd86cd6bd 0xf1fdefcf8fcfe3ff 0x6f1fdefcf8fcfe3f

def z653 : W := mkw 0x4be97e885b80db0c 0x04be97e885b80db0 0xfffd7fccff80ff8f 0xffffd7fccff80ff8

def z654 : W := mkw 0xcffbfdaa5b00d208 0x0cffbfdaa5b00d20 0x1fdc61c0fe00e000 0x41fdc61c0fe00e00

def z655 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x0fe07600ff80fc00 0xd0fe07600ff80fc0

def z656 : W := mkw 0x0004004080402042 0x0000400408040204 0x101c61c08000e000 0x4101c61c08000e00

def z657 : W := mkw 0x0040288800000000 0x0004028880000000 0x900069cc00000004 0x0900069cc0000000

def z658 : W := mkw 0x00000014001404b0 0x000000014001404b 0xe003183c007c1fff 0xbe003183c007c1ff

def z659 : W := mkw 0x869bd1aa00000000 0x0869bd1aa0000000 0x9e1ff1ff00000006 0xe9e1ff1ff0000000

def z660 : W := mkw 0xc2407faa1280db0c 0x0c2407faa1280db0 0xb0007fff0000ff84 0x0b0007fff0000ff8

def z661 : W := mkw 0xafffffffb0f5bdff 0x4afffffffb0f5bdf 0xfffffffff1ffffff 0xffffffffff1fffff

def z662 : W := mkw 0x2f32d13079329429 0x02f32d1307932942 0x0e22903071b31c00 0x90e22903071b31c0

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e000000f0000008 0xf0e000000f000000

def z664 : W := mkw 0x0ffbfc0000000000 0x00ffbfc000000000 0x0ffffe0000000007 0xe0ffffe000000000

def z665 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe0201e3f01801ffd 0xbe0201e3f01801ff

def z666 : W := mkw 0x89e9ae9f00950db4 0x489e9ae9f00950db 0xe1e39e3f01ff1fff 0xbe1e39e3f01ff1ff

def z667 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x1ffef7f300000000 0xc1ffef7f30000000

def z668 : W := mkw 0x0b607e0000800904 0x00b607e000080090 0x6fe07e0001801f8d 0xf6fe07e0001801f8

def z669 : W := mkw 0x2200513010109429 0x0220051301010942 0x0000103000001c00 0x00000103000001c0

def z670 : W := mkw 0x2fbfd170b070b46b 0x02fbfd170b070b46 0xbffff1f0f070fc7f 0xfbffff1f0f070fc7

def z671 : W := mkw 0x09ad0000cd480000 0x009ad0000cd48000 0x4ffd0000ffcc000b 0xf4ffd0000ffcc000

def z672 : W := mkw 0x5b647e44dfccfbde 0x85b647e44dfccfbd 0x6fe07e00ffccfffd 0xf6fe07e00ffccfff

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x80001e3f00000004 0x080001e3f0000000

def z675 : W := mkw 0x104028cc020462d2 0x8104028cc020462d 0xf1c069cc8e00e3fd 0x6f1c069cc8e00e3f

def z676 : W := mkw 0x8ffffdaaa46a0000 0x08ffffdaaa46a000 0x9fffffff007f0007 0xe9fffffff007f000

def z677 : W := mkw 0x8ffffdaaed6a0000 0x08ffffdaaed6a000 0x1fdc61c0fe000000 0x41fdc61c0fe00000

def z678 : W := mkw 0x89e9ac8a00000000 0x089e9ac8a0000000 0x91fdefcf00000007 0x691fdefcf0000000

def z679 : W := mkw 0x10cd2add86dd6ff6 0xc10cd2add86dd6ff 0xf1dd7fff8e4cffff 0x6f1dd7fff8e4cfff

def z680 : W := mkw 0x8dfbac8a00000000 0x08dfbac8a0000000 0x0fff8e0f00000003 0xe0fff8e0f0000000

def z681 : W := mkw 0x400002001280db0c 0x0400002001280db0 0x200000000000ff80 0x0200000000000ff8

def z682 : W := mkw 0x0004025580d52df6 0x40004025580d52df 0xf03fffff81ffffff 0xff03fffff81fffff

def z683 : W := mkw 0x0d32800069220000 0x00d3280006922000 0x4fe28000ffb30009 0xf4fe28000ffb3000

def z684 : W := mkw 0x26165375b0f5bdff 0x426165375b0f5bdf 0xfe1e71f0f1fffffe 0xffe1e71f0f1fffff

def z685 : W := mkw 0x0920000049000000 0x0092000004900000 0x41e000000f800001 0x041e000000f80000

def z686 : W := mkw 0x00040000a46a0000 0x000040000a46a000 0x00000000007f0000 0x000000000007f000

def z687 : W := mkw 0xbffffdfeb67cf6fb 0x8bffffdfeb67cf6f 0xfffffffffe7cffff 0xffffffffffe7cfff

def z688 : W := mkw 0x00c9288802004200 0x000c928880200420 0xf1dd69cc8e00e38f 0x6f1dd69cc8e00e38

def z689 : W := mkw 0x0d32821169b30d24 0x40d32821169b30d2 0x0e22963371b31c00 0x90e22963371b31c0

def z690 : W := mkw 0x104028cc020462d2 0x8104028cc020462d 0xf00169cc004ce3ff 0x2f00169cc004ce3f

def z691 : W := mkw 0x0000000400040090 0x0000000040004009 0x60000000004c03f8 0x060000000004c03f

def z692 : W := mkw 0x4b607e115b91df2c 0x44b607e115b91df2 0x6fe2fe33ffb3ff8d 0xf6fe2fe33ffb3ff8

def z693 : W := mkw 0x10040044864c62d2 0x810040044864c62d 0xe001080c8e4ce3ff 0x2e001080c8e4ce3f

def z694 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x4fe01e007f801f81 0x94fe01e007f801f8

def z695 : W := mkw 0x9ffffdeeef6e62d2 0x89ffffdeeef6e62d 0xffffffffffffe3ff 0xfffffffffffffe3f

def z696 : W := mkw 0x0000021500950db4 0x40000021500950db 0x60201e0001ff1ffd 0xb60201e0001ff1ff

def z697 : W := mkw 0x100000cc000420d2 0x8100000cc000420d 0x900001cc00000070 0x0900001cc0000007

def z698 : W := mkw 0x0000001000100420 0x0000000100010042 0x8002003000700072 0x0800200300070007

def z699 : W := mkw 0x104428cc824462d2 0x8104428cc824462d 0xb01c69cc8040e3fe 0x6b01c69cc8040e3f

def z700 : W := mkw 0x269fd170b47ab46b 0x0269fd170b47ab46 0xbe1ff1f0f07ffc7e 0xfbe1ff1f0f07ffc7

def z701 : W := mkw 0x0000000010009008 0x0000000001000900 0x20000000f000fc08 0x120000000f000fc0

def z702 : W := mkw 0x8089808a00000000 0x08089808a0000000 0x0001800f00000000 0x00001800f0000000

def z703 : W := mkw 0x0000020000800904 0x0000002000080090 0x40200e0001800381 0x040200e000180038

def z704 : W := mkw 0x365679fcb274f6fb 0x8365679fcb274f6f 0xbe1e79fcf070fffe 0xfbe1e79fcf070fff

def z705 : W := mkw 0x92cd7dee864c62d2 0x892cd7dee864c62d 0xf1dd7fff8e4ce3ff 0x6f1dd7fff8e4ce3f

def z706 : W := mkw 0x10cd2acc86cc6bd6 0x810cd2acc86cc6bd 0xf1fd7fcc8fccffff 0xff1fd7fcc8fccfff

def z707 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9ffdffff00000005 0x49ffdffff0000000

def z708 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff9633ffff000b 0xf4fff9633ffff000

def z709 : W := mkw 0x0dbf8040ed6a2042 0x00dbf8040ed6a204 0x6fff8000ffffe07b 0xf6fff8000ffffe07

def z710 : W := mkw 0x10cd28cca66e62d2 0x810cd28cca66e62d 0xf1dd69cc8e7fe3ff 0x6f1dd69cc8e7fe3f

def z711 : W := mkw 0x1004025584dd2df6 0xc1004025584dd2df 0x6000000001ff1ff8 0x16000000001ff1ff

def z712 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x2fe07e00fe00ff85 0xe2fe07e00fe00ff8

def z713 : W := mkw 0x0fbbd12000000000 0x00fbbd1200000000 0x9fffffff00000007 0xe9fffffff0000000

def z714 : W := mkw 0x492002005b80db0c 0x0492002005b80db0 0x6fc00000ff80ff88 0x56fc00000ff80ff8

def z715 : W := mkw 0x86527daa00000000 0x086527daa0000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z716 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff8000ffbf0001 0xd4fff8000ffbf000

def z717 : W := mkw 0x0dbb80006d2a0000 0x00dbb80006d2a000 0x4fe380007fff000b 0xb4fe380007fff000

def z718 : W := mkw 0x26165365b0e5b9df 0x426165365b0e5b9d 0x5e3defcff18fe381 0x45e3defcff18fe38

def z719 : W := mkw 0x4b607c155b15d6b8 0x44b607c155b15d6b 0x8fc3e03ffe7fe072 0x48fc3e03ffe7fe07

def z720 : W := mkw 0x8ffbfdaa04080000 0x08ffbfdaa0408000 0xdfffffff0e0c0007 0xedfffffff0e0c000

def z721 : W := mkw 0x49602a005b80db0c 0x049602a005b80db0 0x6fe06800ff80ff8d 0xf6fe06800ff80ff8

def z722 : W := mkw 0x90cd2cce864c62d2 0x890cd2cce864c62d 0xf1dd6fcf8e4ce3ff 0x6f1dd6fcf8e4ce3f

def z723 : W := mkw 0x82447daaed6a0000 0x082447daaed6a000 0xd0007fffffff000c 0x1d0007fffffff000

def z724 : W := mkw 0x0000021500950db4 0x40000021500950db 0xf03fffff01ff1fff 0xff03fffff01ff1ff

def z725 : W := mkw 0xcffbfdaa5b00d208 0x0cffbfdaa5b00d20 0xfffffffffe00e38f 0xefffffffffe00e38

def z726 : W := mkw 0x8ffbffbf00950db4 0x48ffbffbf00950db 0x7fdc61c001ff1ff8 0x57fdc61c001ff1ff

def z727 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9ffffffff000000f 0xf9ffffffff000000

def z728 : W := mkw 0x108d0044864c62d2 0x8108d0044864c62d 0xf1dd61c08e4ce3ff 0x6f1dd61c08e4ce3f

def z729 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903f97ff00000002 0x8903f97ff0000000

def z730 : W := mkw 0x1d72a8cc6b2662d2 0x81d72a8cc6b2662d 0xbe22e9cc71b3e3f4 0x9be22e9cc71b3e3f

def z731 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dfe9cc8e7fe3ff 0x6f1dfe9cc8e7fe3f

def z732 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff8000ffff0003 0x44fff8000ffff000

def z733 : W := mkw 0x26165170b47ab46b 0x026165170b47ab46 0xbe1e71f0f07ffc7e 0xfbe1e71f0f07ffc7

def z734 : W := mkw 0x8ffbfdaa49020000 0x08ffbfdaa4902000 0x9fffffff01830007 0xe9fffffff0183000

def z735 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xb1dd69cc8e00e3f7 0x6b1dd69cc8e00e3f

def z736 : W := mkw 0x0dbf8215edff0db4 0x40dbf8215edff0db 0xafdc1e3ffe001ff4 0x4afdc1e3ffe001ff

def z737 : W := mkw 0x8ffbfdaa69220000 0x08ffbfdaa6922000 0x9fffffff70000007 0xe9fffffff7000000

def z738 : W := mkw 0x4b60fe005b82db0c 0x04b60fe005b82db0 0x6fe0fe00ff83ff8d 0xf6fe0fe00ff83ff8

def z739 : W := mkw 0x0000000000000000 0x0000000000000000 0x903fffff00000007 0xe903fffff0000000

def z740 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fdd7fff00000007 0x69fdd7fff0000000

def z741 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd7fff8e4ce3ff 0x6f1dd7fff8e4ce3f

def z742 : W := mkw 0xcb60fe025b80db0c 0x0cb60fe025b80db0 0x6fe0fe03ff80ff8d 0xf6fe0fe03ff80ff8

def z743 : W := mkw 0x2f32d33179b39d2d 0x42f32d33179b39d2 0x0e22963371b31c00 0x90e22963371b31c0

def z744 : W := mkw 0x0920000049000000 0x0092000004900000 0x4fe00000ffff0009 0xf4fe00000ffff000

def z745 : W := mkw 0x220451709050b46b 0x0220451709050b46 0xbe1c71f0f040fc7e 0xfbe1c71f0f040fc7

def z746 : W := mkw 0xef32d73279b09d2d 0x0ef32d73279b09d2 0x0e22963371b01c00 0x90e22963371b01c0

def z747 : W := mkw 0x9f36d566864c62d2 0x89f36d566864c62d 0x6e2296338e4ce3f8 0x86e2296338e4ce3f

def z748 : W := mkw 0x10cd2ad986d96f66 0xc10cd2ad986d96f6 0x11fef7f38fb3fc00 0xd11fef7f38fb3fc0

def z749 : W := mkw 0x89e9ac8a00000000 0x089e9ac8a0000000 0x91ffffff00000007 0xe91ffffff0000000

def z750 : W := mkw 0x09240000ed6a0000 0x009240000ed6a000 0x4fe38000ffff000b 0xf4fe38000ffff000

def z751 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e71f0f000fc76 0xebe1e71f0f000fc7

def z752 : W := mkw 0x84dba9aa00000000 0x084dba9aa0000000 0x91ffffff00000007 0xe91ffffff0000000

def z753 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe023fe3f81ffffff 0xfe023fe3f81fffff

def z754 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1c61c0f070fc7e 0x7be1c61c0f070fc7

def z755 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4ffc0000ffff0009 0xf4ffc0000ffff000

def z756 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe1e39e3f8fff1fff 0xfe1e39e3f8fff1ff

def z757 : W := mkw 0x42407e001280db0c 0x042407e001280db0 0x6fc07e00fe00ff8d 0xf6fc07e00fe00ff8

def z758 : W := mkw 0x0000021500950db4 0x40000021500950db 0xee239e3ff1ff1fff 0xfee239e3ff1ff1ff

def z759 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe01e00ff80ff89 0x96fe01e00ff80ff8

def z760 : W := mkw 0x00cd28c882406242 0x000cd28c88240624 0xf1dd69cc8e40e3ff 0x6f1dd69cc8e40e3f

def z761 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e71f0f070fc76 0x4be1e71f0f070fc7

def z762 : W := mkw 0xcffbfdaa5b00d208 0x0cffbfdaa5b00d20 0xdfffffffff80e00f 0xfdfffffffff80e00

def z763 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e71f0f030fc74 0xdbe1e71f0f030fc7

def z764 : W := mkw 0x04160050a0702462 0x004160050a070246 0xbe1e71f0f070fc7e 0xfbe1e71f0f070fc7

def z765 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe07600ff80ff88 0xd6fe07600ff80ff8

def z766 : W := mkw 0xaffbfdaa30209009 0x0affbfdaa3020900 0x9fffffff70000007 0xe9fffffff7000000

def z767 : W := mkw 0x0dbb800049000000 0x00dbb80004900000 0x4fff8000ffff000b 0xf4fff8000ffff000

def z768 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9ffc7fff00000005 0xe9ffc7fff0000000

def z769 : W := mkw 0x4b607e885b80db0c 0x04b607e885b80db0 0xffe07fccff80ff8d 0xfffe07fccff80ff8

def z770 : W := mkw 0x8dbf81aaed6a0000 0x08dbf81aaed6a000 0x5fff81c0ffff000b 0xf5fff81c0ffff000

def z771 : W := mkw 0x8ffbfdaa6d2a0000 0x08ffbfdaa6d2a000 0xdfffffff7fbf0007 0xfdfffffff7fbf000

def z772 : W := mkw 0x10442844864c62d2 0x810442844864c62d 0xf1dc69c08e4ce3ff 0x6f1dc69c08e4ce3f

def z773 : W := mkw 0xc49b83aa5b80db0c 0x0c49b83aa5b80db0 0xf01f81ffff80ff8a 0x1f01f81ffff80ff8

def z774 : W := mkw 0x10cd28cd864d62d2 0xc10cd28cd864d62d 0xf1dde9cf8e4fe3ff 0x6f1dde9cf8e4fe3f

def z775 : W := mkw 0x5bad56ccddccb9de 0x85bad56ccddccb9d 0x9e3d17cc71cc1c72 0x99e3d17cc71cc1c7

def z776 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe17e00ffccff8f 0xf6fe17e00ffccff8

def z777 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x0fff8000ffff0002 0xd0fff8000ffff000

def z778 : W := mkw 0x8ffbfdaa4d0a0000 0x08ffbfdaa4d0a000 0xdfffffff0fff000f 0xfdfffffff0fff000

def z779 : W := mkw 0x8dbf81aaed6a0000 0x08dbf81aaed6a000 0xdfff9fffffff000f 0xfdfff9fffffff000

def z780 : W := mkw 0x90cda8ce864c62d2 0x890cda8ce864c62d 0xf1dde9cf8e4ce3ff 0x6f1dde9cf8e4ce3f

def z781 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xb1dc69cc8e40e3fe 0x6b1dc69cc8e40e3f

def z782 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xfe1e71f0f1fffc7e 0xffe1e71f0f1fffc7

def z783 : W := mkw 0x0612512000000000 0x0061251200000000 0x9e1e7fff00000006 0xe9e1e7fff0000000

def z784 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9ffff7ff00000002 0xc9ffff7ff0000000

def z785 : W := mkw 0xa9edacdab070b46b 0x0a9edacdab070b46 0x21e18e0ff070fc79 0x121e18e0ff070fc7

def z786 : W := mkw 0x20040255b0f5bdff 0x420040255b0f5bdf 0x20000000f070fff8 0x120000000f070fff

def z787 : W := mkw 0x8ffbfdaa49000000 0x08ffbfdaa4900000 0xdfffffffffff000f 0xfdfffffffffff000

def z788 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xfe1f71f0f07cfc7f 0xffe1f71f0f07cfc7

def z789 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1ffe9cc8e4ce3ff 0xef1ffe9cc8e4ce3f

def z790 : W := mkw 0x50040255dfddfffe 0xc50040255dfddfff 0x60000000fffffff8 0x160000000fffffff

def z791 : W := mkw 0xb49f81fea47c24f3 0x8b49f81fea47c24f 0x901f81ff007c0072 0x0901f81ff007c007

def z792 : W := mkw 0x8dfbadaa00000000 0x08dfbadaa0000000 0x91ffefff00000007 0x691ffefff0000000

def z793 : W := mkw 0x8ffbfdaa02004200 0x08ffbfdaa0200420 0xbfffffff0000e387 0xebfffffff0000e38

def z794 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd69cc0e4ce3f7 0x0f1dd69cc0e4ce3f

def z795 : W := mkw 0x46dffe00b6eadb0c 0x046dffe00b6eadb0 0x201ffe00007fff86 0x0201ffe00007fff8

def z796 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1df69cc8e7ce3ff 0xff1df69cc8e7ce3f

def z797 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe07e00ffffff8d 0xf6fe07e00ffffff8

def z798 : W := mkw 0x2ba9d1705d1ab46b 0x02ba9d1705d1ab46 0xf1e1f1f00f8ffc75 0x0f1e1f1f00f8ffc7

def z799 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x31dc61c08e00e3f0 0x431dc61c08e00e3f

def z800 : W := mkw 0x0412012000000000 0x0041201200000000 0x903f9fff00000007 0xa903f9fff0000000

def z801 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xfe3e71f0f1f0fc7f 0xffe3e71f0f1f0fc7

def z802 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x901f9fff00000006 0x0901f9fff0000000

def z803 : W := mkw 0x8ffbfdaa02004200 0x08ffbfdaa0200420 0xdfffffff0e000387 0xedfffffff0e00038

def z804 : W := mkw 0x869bd5aa00000000 0x0869bd5aa0000000 0x901f97ff00000002 0x0901f97ff0000000

def z805 : W := mkw 0x86db7daa00000000 0x086db7daa0000000 0x9fdf7fff00000007 0xe9fdf7fff0000000

def z806 : W := mkw 0x0000021500950db4 0x40000021500950db 0xe0239e3f01ff1ff7 0x0e0239e3f01ff1ff

def z807 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fe38000ffff0009 0x94fe38000ffff000

def z808 : W := mkw 0x8dbb85aa00000000 0x08dbb85aa0000000 0x903f87ff00000002 0x0903f87ff0000000

def z809 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe06000ff80ff89 0xf6fe06000ff80ff8

def z810 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x91ffffff00000007 0x091ffffff0000000

def z811 : W := mkw 0x86527daa00000000 0x086527daa0000000 0x9e1c7fff00000004 0x49e1c7fff0000000

def z812 : W := mkw 0x8f727daa00000000 0x08f727daa0000000 0x9ffe7fff00000007 0xe9ffe7fff0000000

def z813 : W := mkw 0x0004025580d52df6 0x40004025580d52df 0x6000000081fffff8 0x16000000081fffff

def z814 : W := mkw 0x0000021500950db4 0x40000021500950db 0xc0239e3f01ff1ff3 0x9c0239e3f01ff1ff

def z815 : W := mkw 0x36db79bc363cd6b9 0x836db79bc363cd6b 0x4fc3183c7e3c1f81 0x94fc3183c7e3c1f8

def z816 : W := mkw 0x249f8175a47f24f3 0x4249f8175a47f24f 0x901f81ff007f0072 0x0901f81ff007f007

def z817 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xdfffffff8e00000f 0xedfffffff8e00000

def z818 : W := mkw 0x10040255efff6ff6 0xc10040255efff6ff 0x60000000fffffff8 0x160000000fffffff

def z819 : W := mkw 0x6f32d73079b29d2d 0x06f32d73079b29d2 0x0e22963071b31c00 0x90e22963071b31c0

def z820 : W := mkw 0x0dbf8040ed6a2042 0x00dbf8040ed6a204 0xdfff81c0ffff007b 0xfdfff81c0ffff007

def z821 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe3ef7f3f070fc7e 0xfbe3ef7f3f070fc7

def z822 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xdfffffff018f0007 0xedfffffff018f000

def z823 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x71dc69c08e4ce3fd 0x671dc69c08e4ce3f

def z824 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd69cc8e0ce3f5 0x4f1dd69cc8e0ce3f

def z825 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1fde9cc8fcfe3ff 0x6f1fde9cc8fcfe3f

def z826 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xbfffffff0040007f 0xebfffffff0040007

def z827 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fde0000ffff000a 0xf4fde0000ffff000

def z828 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1fd7fcc8e4ce3ff 0xef1fd7fcc8e4ce3f

def z829 : W := mkw 0x20040255a0f52df7 0x420040255a0f52df 0x6000000001ff1ff8 0x16000000001ff1ff

def z830 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe3ef1f0f1f3fc7e 0xfbe3ef1f0f1f3fc7

def z831 : W := mkw 0x008d0044844c20d2 0x0008d0044844c20d 0xf1dd69cc8e4ce3ff 0x6f1dd69cc8e4ce3f

def z832 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4ffe8000ffff0008 0xd4ffe8000ffff000

def z833 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fc06800ff80ff8d 0x76fc06800ff80ff8

def z834 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x71dd69cc8e4ce3f9 0x471dd69cc8e4ce3f

def z835 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x2fe07e00ff80ff84 0xd2fe07e00ff80ff8

def z836 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x4fe07e00ff80ff81 0xd4fe07e00ff80ff8

def z837 : W := mkw 0x2dbf8160ed6a2043 0x02dbf8160ed6a204 0x5fff81c0ffff000b 0xf5fff81c0ffff000

def z838 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1ffffff8fffe3ff 0xff1ffffff8fffe3f

def z839 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe3ff1f0f070fc7f 0xfbe3ff1f0f070fc7

def z840 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd69cc8fffe3ff 0x7f1dd69cc8fffe3f

def z841 : W := mkw 0x60040255fbf5ffff 0x460040255fbf5fff 0x60000000fffffff8 0x160000000fffffff

def z842 : W := mkw 0xd9e9ae8e4f8c4b94 0x8d9e9ae8e4f8c4b9 0x41e18e0f0f8c0381 0x041e18e0f0f8c038

def z843 : W := mkw 0x82c97daa00000000 0x082c97daa0000000 0x901d7fff00000006 0x0901d7fff0000000

def z844 : W := mkw 0x6d762f70ebf06f67 0x06d762f70ebf06f6 0xd1fe0ff00ff003f3 0x0d1fe0ff00ff003f

def z845 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fffffff01b30007 0xf9fffffff01b3000

def z846 : W := mkw 0x19e9aa8d4f8f4b94 0xc19e9aa8d4f8f4b9 0x41e18e0f0f8f0381 0x041e18e0f0f8f038

def z847 : W := mkw 0x6f32573179b19d2d 0x46f32573179b19d2 0x0e22963371b31c00 0x90e22963371b31c0

def z848 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xffdd69ccfe4ce3ff 0xfffdd69ccfe4ce3f

def z849 : W := mkw 0x86dbfdaa00000000 0x086dbfdaa0000000 0x901c7fff00000004 0x0901c7fff0000000

def z850 : W := mkw 0x24160050b070b46b 0x024160050b070b46 0xbe1e61c0f070fc7e 0xfbe1e61c0f070fc7

def z851 : W := mkw 0x8ffbfdaa20200000 0x08ffbfdaa2020000 0x9fffffff70300007 0xf9fffffff7030000

def z852 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xfffc7fc0ff80ff8f 0xffffc7fc0ff80ff8

def z853 : W := mkw 0x0dbf8120ed6a0000 0x00dbf8120ed6a000 0xdfff81f0ffff000b 0xfdfff81f0ffff000

def z854 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fdfffff00000006 0x49fdfffff0000000

def z855 : W := mkw 0x00c9288800000000 0x000c928880000000 0x91dd7fff00000007 0x691dd7fff0000000

def z856 : W := mkw 0x4b607f205b80db0c 0x04b607f205b80db0 0xffe07ff0ff80ff8d 0xfffe07ff0ff80ff8

def z857 : W := mkw 0x0dbb80006d2a0000 0x00dbb80006d2a000 0x4fe38000ffbf0009 0xf4fe38000ffbf000

def z858 : W := mkw 0x8dbf808aed6a0000 0x08dbf808aed6a000 0x4fff800fffff000b 0xf4fff800fffff000

def z859 : W := mkw 0x8dfbadaa00000000 0x08dfbadaa0000000 0x9fff8fff00000003 0xe9fff8fff0000000

def z860 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fc07e00fe00ff8d 0x66fc07e00fe00ff8

def z861 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fc07000ff80ff8c 0xf6fc07000ff80ff8

def z862 : W := mkw 0x09240000ed6a0000 0x009240000ed6a000 0x4fc00000ffff0008 0x54fc00000ffff000

def z863 : W := mkw 0x061651609040b04a 0x0061651609040b04 0xbe1e71f0f040fc7e 0xfbe1e71f0f040fc7

def z864 : W := mkw 0x349f01fda47d24f3 0xc349f01fda47d24f 0x901f81ff007f0072 0x0901f81ff007f007

def z865 : W := mkw 0xcffbfdaa4b004200 0x0cffbfdaa4b00420 0x9fffffff0e000007 0xe9fffffff0e00000

def z866 : W := mkw 0x10cd28cca66c62d2 0x810cd28cca66c62d 0xf1dd69ccfe7ce3ff 0x7f1dd69ccfe7ce3f

def z867 : W := mkw 0x10c928cc060c62d2 0x810c928cc060c62d 0xf1dd69cc0e0ce3f7 0x6f1dd69cc0e0ce3f

def z868 : W := mkw 0x8ffbfdaa69220000 0x08ffbfdaa6922000 0xdfffffffffb3000f 0xfdfffffffffb3000

def z869 : W := mkw 0x0dbf8088ed6a0000 0x00dbf8088ed6a000 0xdfff81ccffff000b 0xfdfff81ccffff000

def z870 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fdd0000ffff000b 0x74fdd0000ffff000

def z871 : W := mkw 0x0d360000e9600000 0x00d360000e960000 0x4fff8000ffff000b 0xf4fff8000ffff000

def z872 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e71f07070fc76 0x9be1e71f07070fc7

def z873 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dc69cc8e4ce3fc 0x4f1dc69cc8e4ce3f

def z874 : W := mkw 0x09602a004b804b04 0x009602a004b804b0 0x6fe07e00ff80ff8d 0xf6fe07e00ff80ff8

def z875 : W := mkw 0x59e92e8d4f8d4b94 0xc59e92e8d4f8d4b9 0x41e18e0f0f8f0381 0x041e18e0f0f8f038

def z876 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0xcfff9030ffff000f 0xfcfff9030ffff000

def z877 : W := mkw 0x261251703030b46b 0x0261251703030b46 0xbe1e71f07030fc76 0xfbe1e71f07030fc7

def z878 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e7ffff070fc7e 0xfbe1e7ffff070fc7

def z879 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xefe3fe3fffffff8f 0xfefe3fe3fffffff8

def z880 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xd1dd69cc8e4ce3f3 0x4d1dd69cc8e4ce3f

def z881 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe1fe0fff80ff8d 0xf6fe1fe0fff80ff8

def z882 : W := mkw 0x8ffbfdaa040a0000 0x08ffbfdaa040a000 0x9fffffff000f0007 0xe9fffffff000f000

def z883 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9ffeffff00000004 0xc9ffeffff0000000

def z884 : W := mkw 0x0dbf8040ed6a2042 0x00dbf8040ed6a204 0x5fffe1c0ffffe00b 0xf5fffe1c0ffffe00

def z885 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0xefff8000ffff007f 0xfefff8000ffff007

def z886 : W := mkw 0x0be97c8800000000 0x00be97c880000000 0x9fffffff00000007 0xe9fffffff0000000

def z887 : W := mkw 0x0089008800000000 0x0008900880000000 0x903f9fff00000007 0xa903f9fff0000000

def z888 : W := mkw 0x02407a001280db0c 0x002407a001280db0 0x6fe07e00ff80ff8d 0xf6fe07e00ff80ff8

def z889 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1f79fcf070fc7f 0xfbe1f79fcf070fc7

def z890 : W := mkw 0x8ffbfdaa10009008 0x08ffbfdaa1000900 0xbfffffff0000fc07 0xebfffffff0000fc0

def z891 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0x71dd61c08e4ce3fb 0x671dd61c08e4ce3f

def z892 : W := mkw 0x06db79a800000000 0x006db79a80000000 0x9fffffff00000007 0xe9fffffff0000000

def z893 : W := mkw 0x020450509050b46a 0x0020450509050b46 0xbe1e71f0f070fc7e 0xfbe1e71f0f070fc7

def z894 : W := mkw 0x8fbbd5aa00000000 0x08fbbd5aa0000000 0x9e3f9fff00000007 0xa9e3f9fff0000000

def z895 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1fd69cc8fcce3ff 0xff1fd69cc8fcce3f

def z896 : W := mkw 0x26165171b071b46b 0x426165171b071b46 0xbe1ef1f3f073fc7e 0xfbe1ef1f3f073fc7

def z897 : W := mkw 0x0000021500950db4 0x40000021500950db 0x60239e3f01ff1ff9 0x960239e3f01ff1ff

def z898 : W := mkw 0x0d360000ed6a0000 0x00d360000ed6a000 0x4ffe0000ffff000b 0xf4ffe0000ffff000

def z899 : W := mkw 0x0b6078005b00d208 0x00b6078005b00d20 0x6fe07800ff80ff8d 0xf6fe07800ff80ff8

def z900 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xefe27e30ff80ff8f 0xfefe27e30ff80ff8

def z901 : W := mkw 0x86527daa00000000 0x086527daa0000000 0x901e7fff00000006 0x0901e7fff0000000

def z902 : W := mkw 0x8ffbfdaa20220000 0x08ffbfdaa2022000 0x9fffffff00330007 0xe9fffffff0033000

def z903 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fde7fff00000006 0xe9fde7fff0000000

def z904 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe27e00fff0ff8f 0xf6fe27e00fff0ff8

def z905 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe1fe00ff8fff8d 0xf6fe1fe00ff8fff8

def z906 : W := mkw 0x2616d170b072b46b 0x02616d170b072b46 0xbe1ef1f0f073fc7e 0xfbe1ef1f0f073fc7

def z907 : W := mkw 0x4b2056005b80db0c 0x04b2056005b80db0 0x6fe01600ff80ff89 0xf6fe01600ff80ff8

def z908 : W := mkw 0x0d368000ed6a0000 0x00d368000ed6a000 0x4fe28000ffff0009 0xf4fe28000ffff000

def z909 : W := mkw 0x9ffbfdaa06084200 0x89ffbfdaa0608420 0x9fffffff0e000007 0xe9fffffff0e00000

def z910 : W := mkw 0x1dbf80c8ed6a2042 0x81dbf80c8ed6a204 0x5fff81c0ffff000b 0xf5fff81c0ffff000

def z911 : W := mkw 0x62407f751295ffff 0x462407f751295fff 0xb0007fff0000fff4 0x0b0007fff0000fff

def z912 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1ff1fff070fc7e 0xfbe1ff1fff070fc7

def z913 : W := mkw 0x8ffbfdaa4b004200 0x08ffbfdaa4b00420 0xffffffffff80e38f 0xfffffffffff80e38

def z914 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe06e00ff80ff89 0x56fe06e00ff80ff8

def z915 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x3e1c61c0f000fc70 0x43e1c61c0f000fc7

def z916 : W := mkw 0x42407a005b80db0c 0x042407a005b80db0 0x6fc07800ff80ff8d 0xf6fc07800ff80ff8

def z917 : W := mkw 0xc9e9ae8f4b854b94 0x4c9e9ae8f4b854b9 0x41e18e0f0f8f0381 0x041e18e0f0f8f038

def z918 : W := mkw 0x8be97daa00000000 0x08be97daa0000000 0x9ffd7fff00000007 0xe9ffd7fff0000000

def z919 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0xcfff880cffff000f 0xfcfff880cffff000

def z920 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dc61c08e4ce3fe 0x6f1dc61c08e4ce3f

def z921 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dc69cc8e00e3fd 0x6f1dc69cc8e00e3f

def z922 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fdf8000ffff000a 0x54fdf8000ffff000

def z923 : W := mkw 0xa6165572b070b46b 0x0a6165572b070b46 0xbe1e77f3f070fc7e 0xfbe1e77f3f070fc7

def z924 : W := mkw 0x8ffbfdaa49000000 0x08ffbfdaa4900000 0xdfffffff0f800007 0xedfffffff0f80000

def z925 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xefe07e3fff80ff8d 0xfefe07e3fff80ff8

def z926 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x3e1e71f0f070fc78 0xd3e1e71f0f070fc7

def z927 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd61cc8e4ce3fa 0x4f1dd61cc8e4ce3f

def z928 : W := mkw 0x0612513010109428 0x0061251301010942 0xbe1e71f0f070fc7e 0xfbe1e71f0f070fc7

def z929 : W := mkw 0xcb607f225b80db0c 0x0cb607f225b80db0 0x6fe07e33ff80ff8d 0xf6fe07e33ff80ff8

def z930 : W := mkw 0x10cda8cc864e62d2 0x810cda8cc864e62d 0xf1dde9cc8e4fe3ff 0x6f1dde9cc8e4fe3f

def z931 : W := mkw 0x0b607c001200d208 0x00b607c001200d20 0x6fe07e00fe00ff8d 0xf6fe07e00fe00ff8

def z932 : W := mkw 0x82c97daa00000000 0x082c97daa0000000 0x91dc7fff00000004 0x491dc7fff0000000

def z933 : W := mkw 0xcffbfdaa5b00d208 0x0cffbfdaa5b00d20 0xbffffffffe00fc0f 0xfbffffffffe00fc0

def z934 : W := mkw 0x00c9288c02044290 0x000c9288c0204429 0xf1dd69cc8e4ce3ff 0x6f1dd69cc8e4ce3f

def z935 : W := mkw 0x8ffbfdaa1200d208 0x08ffbfdaa1200d20 0xfffffffffe00ff8f 0xffffffffffe00ff8

def z936 : W := mkw 0x8dbf8122ed6a0000 0x08dbf8122ed6a000 0x4fff8033ffff000b 0xf4fff8033ffff000

def z937 : W := mkw 0x0dfba88800000000 0x00dfba8880000000 0x9fffffff00000007 0xe9fffffff0000000

def z938 : W := mkw 0x86dbfdaa00000000 0x086dbfdaa0000000 0x903fffff00000007 0xa903fffff0000000

def z939 : W := mkw 0x0f727d2000000000 0x00f727d200000000 0x9fffffff00000007 0xe9fffffff0000000

def z940 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff8e0fffff000b 0xf4fff8e0fffff000

def z941 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x6fffe000ffffe00f 0xf6fffe000ffffe00

def z942 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff80007fff0003 0x94fff80007fff000

def z943 : W := mkw 0x84dbadaa00000000 0x084dbadaa0000000 0x901f8fff00000002 0x0901f8fff0000000

def z944 : W := mkw 0x049f0000a4680000 0x0049f0000a468000 0x4fff8000ffff000b 0xf4fff8000ffff000

def z945 : W := mkw 0x1004025586dd6ff6 0xc1004025586dd6ff 0x600000008e4cfff8 0x0600000008e4cfff

def z946 : W := mkw 0x4b607e015b81db0c 0x44b607e015b81db0 0x6fe0fe03ff83ff8d 0xf6fe0fe03ff83ff8

def z947 : W := mkw 0xc2407fbf1295dfbc 0x4c2407fbf1295dfb 0xb0007fff0000fff4 0x0b0007fff0000fff

def z948 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xfe3ffffff1fffc7f 0xffe3ffffff1fffc7

def z949 : W := mkw 0x09ad0000ed6a0000 0x009ad0000ed6a000 0x4ffd0000ffff000b 0xf4ffd0000ffff000

def z950 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xfe1e79f0f070ffff 0xffe1e79f0f070fff

def z951 : W := mkw 0x8be9fdaa00000000 0x08be9fdaa0000000 0x91fdffff00000007 0x691fdffff0000000

def z952 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe3e7ff0f070fc7f 0xfbe3e7ff0f070fc7

def z953 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9e3fffff00000006 0x89e3fffff0000000

def z954 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xffffffff0000038f 0xeffffffff0000038

def z955 : W := mkw 0xcf32d73359919d2c 0x4cf32d73359919d2 0x0e22963371b31c00 0x90e22963371b31c0

def z956 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x2fc06000fe00ff80 0x42fc06000fe00ff8

def z957 : W := mkw 0x82407daa00000000 0x082407daa0000000 0x901c7fff00000006 0x6901c7fff0000000

def z958 : W := mkw 0x149f80dda47f24f2 0xc149f80dda47f24f 0x901f81ff007f0072 0x0901f81ff007f007

def z959 : W := mkw 0x8fbbd5aa00000000 0x08fbbd5aa0000000 0x9e3ff7ff00000006 0xe9e3ff7ff0000000

def z960 : W := mkw 0x8ffbfdaa10009008 0x08ffbfdaa1000900 0x9ffffffff000e007 0xe9ffffffff000e00

def z961 : W := mkw 0x09ad8000ed6a0000 0x009ad8000ed6a000 0x4fe18000ffff0009 0xf4fe18000ffff000

def z962 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fc07e00ff80ff8c 0x56fc07e00ff80ff8

def z963 : W := mkw 0x8dfbadaa00000000 0x08dfbadaa0000000 0x91ff9fff00000007 0xa91ff9fff0000000

def z964 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xbfffffff8000e00f 0xebfffffff8000e00

def z965 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe2fe33ff80ff8d 0xf6fe2fe33ff80ff8

def z966 : W := mkw 0x00442844824462d2 0x000442844824462d 0xf1dd69cc8e4ce3ff 0x6f1dd69cc8e4ce3f

def z967 : W := mkw 0x0000021500950db4 0x40000021500950db 0xa0239e3f01ff1ff6 0x9a0239e3f01ff1ff

def z968 : W := mkw 0x104428cc824462d2 0x8104428cc824462d 0xf1dc69cc8e40e3ff 0x6f1dc69cc8e40e3f

def z969 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1ff1f0f07ffc7e 0xfbe1ff1f0f07ffc7

def z970 : W := mkw 0x8ffbfdaa4d0a0000 0x08ffbfdaa4d0a000 0x9fffffff0e000007 0xe9fffffff0e00000

def z971 : W := mkw 0x06165040b060b04a 0x006165040b060b04 0xbe1e71c0f070fc7e 0xfbe1e71c0f070fc7

def z972 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xefe17e0cff80ff8f 0xfefe17e0cff80ff8

def z973 : W := mkw 0x849b81aa00000000 0x0849b81aa0000000 0x903f8fff00000003 0x0903f8fff0000000

def z974 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1fdefcf8e4ce3ff 0x6f1fdefcf8e4ce3f

def z975 : W := mkw 0x00cd284086486242 0x000cd28408648624 0xf1dd69c08e4ce3ff 0x6f1dd69c08e4ce3f

def z976 : W := mkw 0x86dbfdaa00000000 0x086dbfdaa0000000 0x9e1fffff00000006 0xe9e1fffff0000000

def z977 : W := mkw 0x49602e005b80db0c 0x049602e005b80db0 0x6fe00e00ff80ff89 0xf6fe00e00ff80ff8

def z978 : W := mkw 0xcffbfdaa1200d208 0x0cffbfdaa1200d20 0x9fffffff0000e007 0xe9fffffff0000e00

def z979 : W := mkw 0x0dbb80006d2a0000 0x00dbb80006d2a000 0x4fff80007fbf0003 0xf4fff80007fbf000

def z980 : W := mkw 0x8ffbfdaa10009008 0x08ffbfdaa1000900 0x9fffffff70001c07 0xf9fffffff70001c0

def z981 : W := mkw 0xa616d172b070b46b 0x0a616d172b070b46 0xbe1ef1f3f070fc7e 0xfbe1ef1f3f070fc7

def z982 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x9e1e71f0f070fc72 0xd9e1e71f0f070fc7

def z983 : W := mkw 0x8ffbfdaa02004200 0x08ffbfdaa0200420 0x9fffffff8e00e007 0xe9fffffff8e00e00

def z984 : W := mkw 0x0d32800069220000 0x00d3280006922000 0x4fe38000ffff000b 0xf4fe38000ffff000

def z985 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xbfffffff00001c0f 0xfbfffffff00001c0

def z986 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4fff9e00ffff000f 0xf4fff9e00ffff000

def z987 : W := mkw 0x8f72fdaa00000000 0x08f72fdaa0000000 0x9e3effff00000006 0xe9e3effff0000000

def z988 : W := mkw 0x42407e151295dfbc 0x442407e151295dfb 0x20007e000000fff4 0x020007e000000fff

def z989 : W := mkw 0x4b2052005b80db0c 0x04b2052005b80db0 0x6fe07000ff80ff8d 0xf6fe07000ff80ff8

def z990 : W := mkw 0x349f81fca47e24f3 0x8349f81fca47e24f 0x901f81fc007f0072 0x0901f81fc007f007

def z991 : W := mkw 0x8ffbfdaa4d0a0000 0x08ffbfdaa4d0a000 0xdfffffffff8f000f 0xfdfffffffff8f000

def z992 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xdfffffff004c000f 0xedfffffff004c000

def z993 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe07e00ff80ff85 0x46fe07e00ff80ff8

def z994 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0xdfffffff0180000f 0xfdfffffff0180000

def z995 : W := mkw 0x0b2052005980990c 0x00b2052005980990 0x6fe07e00ff80ff8d 0xf6fe07e00ff80ff8

def z996 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x6fff9000ffff1c0f 0xf6fff9000ffff1c0

def z997 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0xcfff803fffff000b 0xfcfff803fffff000

def z998 : W := mkw 0x22045050b070b46b 0x022045050b070b46 0xbe1c71c0f070fc7e 0xfbe1c71c0f070fc7

def z999 : W := mkw 0xcffbfdaa59009008 0x0cffbfdaa5900900 0x9fffffff70000007 0xe9fffffff7000000

def z1000 : W := mkw 0x8ffbfdaa49000000 0x08ffbfdaa4900000 0x9ffffffffe000007 0xe9ffffffffe00000

def z1001 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x6fff8800ffff038f 0xf6fff8800ffff038

def z1002 : W := mkw 0x09a980004d0a0000 0x009a980004d0a000 0x4fe38000ffff000b 0xf4fe38000ffff000

def z1003 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x3e1c71c0f070fc7c 0xf3e1c71c0f070fc7

def z1004 : W := mkw 0x59e9ae8c4f8e4b94 0x859e9ae8c4f8e4b9 0x41e18e0c0f8f0381 0x041e18e0c0f8f038

def z1005 : W := mkw 0x492002005b80db0c 0x0492002005b80db0 0x6fe01e00ff80ff8d 0xf6fe01e00ff80ff8

def z1006 : W := mkw 0x26165160b060b04b 0x026165160b060b04 0xbe1c71c0f040fc7e 0xfbe1c71c0f040fc7

def z1007 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dd79cc8e4cffff 0xff1dd79cc8e4cfff

def z1008 : W := mkw 0x8ffbfdaa59009008 0x08ffbfdaa5900900 0xffffffffff80fc0f 0xfffffffffff80fc0

def z1009 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x1fffffff00000001 0xc1fffffff0000000

def z1010 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1c71f0f040fc7e 0x6be1c71f0f040fc7

def z1011 : W := mkw 0x049f0000ed6a0000 0x0049f0000ed6a000 0x4fdf0000ffff000b 0xf4fdf0000ffff000

def z1012 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1c71f0f000fc7c 0xfbe1c71f0f000fc7

def z1013 : W := mkw 0x82c97daa00000000 0x082c97daa0000000 0x91ffffff00000007 0xe91ffffff0000000

def z1014 : W := mkw 0xcb607faa5b80db0c 0x0cb607faa5b80db0 0xffe3ffffff80ff8f 0xfffe3ffffff80ff8

def z1015 : W := mkw 0x86dbfdaa00000000 0x086dbfdaa0000000 0x91dfffff00000007 0x691dfffff0000000

def z1016 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fffffff0070000f 0xf9fffffff0070000

def z1017 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1c71f0f070fc7c 0x5be1c71f0f070fc7

def z1018 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0x3e1e61c0f070fc7a 0xf3e1e61c0f070fc7

def z1019 : W := mkw 0x10c928cc020462d2 0x810c928cc020462d 0xf1dd69cc8e00e3ff 0x6f1dd69cc8e00e3f

def z1020 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xb1dd69cc8e4ce3f6 0x4b1dd69cc8e4ce3f

def z1021 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fffffff007f0007 0xe9fffffff007f000

def z1022 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe3fe00ff80ff8f 0xf6fe3fe00ff80ff8

def z1023 : W := mkw 0x869bd1aa00000000 0x0869bd1aa0000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z1024 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xffde71f0fe70fc7f 0xfffde71f0fe70fc7

def z1025 : W := mkw 0x8ffbfdaa49000000 0x08ffbfdaa4900000 0x9fffffff71800007 0xf9fffffff7180000

def z1026 : W := mkw 0xcb607e8a5b80db0c 0x0cb607e8a5b80db0 0x6fe07e0fff80ff8d 0xf6fe07e0fff80ff8

def z1027 : W := mkw 0x261251701010b46b 0x0261251701010b46 0xbe1e71f0f000fc7e 0xfbe1e71f0f000fc7

def z1028 : W := mkw 0x20040255fdffbdff 0x420040255fdffbdf 0x60000000fffffff8 0x160000000fffffff

def z1029 : W := mkw 0x32407bfd1295ffff 0xc32407bfd1295fff 0xb0007fff0000fff4 0x0b0007fff0000fff

def z1030 : W := mkw 0x8f32d52200000000 0x08f32d5220000000 0x9e3fffff00000007 0xe9e3fffff0000000

def z1031 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0x4ffd8000ffff0009 0x54ffd8000ffff000

def z1032 : W := mkw 0x26165170b478b46b 0x026165170b478b46 0xfe1e71f0fe7cfc7e 0xffe1e71f0fe7cfc7

def z1033 : W := mkw 0x10cd28c886486242 0x810cd28c88648624 0xf1dc69c08e40e3ff 0x6f1dc69c08e40e3f

def z1034 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x2fc07e00fe00ff8c 0xf2fc07e00fe00ff8

def z1035 : W := mkw 0x26165170b070b46b 0x026165170b070b46 0xbe1e61f0f070fc7a 0x5be1e61f0f070fc7

def z1036 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fffefff00000003 0x49fffefff0000000

def z1037 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0x6fe2fe00ffb3ff8d 0xf6fe2fe00ffb3ff8

def z1038 : W := mkw 0x0dbf8000ed6a0000 0x00dbf8000ed6a000 0xdfffe1c0ffff000f 0xfdfffe1c0ffff000

def z1039 : W := mkw 0x8ffbfdaa69220000 0x08ffbfdaa6922000 0xdfffffff71ff000f 0xfdfffffff71ff000

def z1040 : W := mkw 0x4b607e005b80db0c 0x04b607e005b80db0 0xefe07e00ffc0ffff 0xfefe07e00ffc0fff

def z1041 : W := mkw 0x30040255b6fdffff 0xc30040255b6fdfff 0x60000000fffffff8 0x160000000fffffff

def z1042 : W := mkw 0x52407edd1295fffe 0xc52407edd1295fff 0xb0007fff0000fff4 0x0b0007fff0000fff

def z1043 : W := mkw 0x8dbb81aa00000000 0x08dbb81aa0000000 0x9fff9fff00000007 0xe9fff9fff0000000

def z1044 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1dfe9ff8e4ce3ff 0x6f1dfe9ff8e4ce3f

def z1045 : W := mkw 0x8ffbfdaa00000000 0x08ffbfdaa0000000 0x9fff9fff00000003 0x89fff9fff0000000

def z1046 : W := mkw 0x4b607c005b00d208 0x04b607c005b00d20 0x6fc07800fe00ff8d 0xf6fc07800fe00ff8

def z1047 : W := mkw 0x8dbf8402ed6a0000 0x08dbf8402ed6a000 0x4fff8603ffff000b 0xf4fff8603ffff000

def z1048 : W := mkw 0xcb607faa5b80db0c 0x0cb607faa5b80db0 0x7fe07fc0ff80ff8d 0xf7fe07fc0ff80ff8

def z1049 : W := mkw 0x09ad0000cd480000 0x009ad0000cd48000 0x4fff8000ffff000b 0xf4fff8000ffff000

def z1050 : W := mkw 0x10cd28cc864c62d2 0x810cd28cc864c62d 0xf1df79fc8e4ce3ff 0xef1df79fc8e4ce3f

def z1051 : W := mkw 0x8fbbd5aa00000000 0x08fbbd5aa0000000 0x9fff97ff00000003 0xe9fff97ff0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z9,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6])],[(0,[z1,z11,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z12,z13])],[(0,[z1,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z15,z4,z16,z5]),(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z4,z5,z6])],[(1,[z1,z2,z19,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z21,z6])],[(1,[z22,z2,z3,z4,z23,z6]),(0,[z1,z2,z3,z24,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z25,z6])],[(0,[z1,z2,z26,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z28,z6]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z30,z4,z5,z6])],[(0,[z1,z2,z3,z31,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z32,z6]),(0,[z1,z2,z3,z4,z5,z6,z33]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z1,z2,z3,z36,z4,z5,z6]),(0,[z1,z37,z38,z2,z3,z5,z6]),(0,[z1,z38,z2,z3,z4,z5,z39]),(0,[z1,z40,z2,z3,z5,z6,z12])]],
   [[(0,[z41,z1,z42,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z45,z4,z6]),(0,[z1,z2,z3,z46,z5,z47,z6])],[(0,[z1,z2,z3,z4,z5,z48,z6]),(0,[z22,z1,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z23,z49,z6]),(0,[z1,z2,z3,z4,z50,z28,z6]),(0,[z1,z51,z2,z3,z4,z5,z6]),(0,[z1,z2,z52,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z53,z5,z6])],[(0,[z54,z1,z2,z55,z4,z5,z6]),(0,[z1,z56,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z58,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z6])],[(0,[z1,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z61,z4,z5,z6]),(1,[z1,z37,z2,z62,z5,z6]),(0,[z1,z2,z3,z5,z63,z64,z6]),(0,[z1,z40,z2,z3,z4,z5,z6])],[(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z66]),(0,[z1,z2,z67,z3,z4,z5,z6]),(0,[z1,z40,z2,z3,z68,z5,z6])],[(1,[z1,z69,z70,z4,z5,z6]),(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z72,z6]),(0,[z1,z2,z3,z4,z73,z5,z6]),(0,[z1,z74,z38,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z75,z76])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z77,z3,z4,z5,z6]),(0,[z1,z2,z3,z78,z4,z5,z6])],[(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z80]),(0,[z1,z2,z19,z3,z46,z5,z6]),(0,[z1,z81,z2,z3,z4,z5,z6]),(0,[z1,z82,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z84,z5,z6]),(0,[z1,z85,z2,z3,z4,z5,z6]),(0,[z1,z2,z86,z3,z4,z5,z6])],[(0,[z41,z1,z3,z4,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z87,z6]),(0,[z1,z2,z3,z4,z5,z88,z6]),(0,[z1,z2,z3,z89,z4,z5,z6])],[(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z69,z3,z4,z91,z5,z6]),(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z93]),(0,[z94,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z95,z4,z5,z6]),(0,[z1,z96,z2,z3,z4,z5,z6])],[(0,[z1,z97,z2,z3,z4,z5,z98]),(0,[z1,z99,z2,z3,z4,z49,z6]),(0,[z1,z100,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z101,z4,z5,z6]),(0,[z1,z102,z2,z3,z4,z5,z6]),(0,[z1,z103,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z104,z6]),(0,[z1,z2,z3,z105,z4,z5,z6]),(0,[z1,z106,z2,z3,z4,z5,z6])],[(0,[z1,z107,z2,z3,z4,z6,z13])],[(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z110,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6])]],
   [[(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z115,z4,z5,z6]),(0,[z116,z1,z96,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z117,z6])],[(0,[z118,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z120]),(0,[z1,z2,z3,z4,z5,z121,z6])],[(0,[z1,z42,z3,z4,z5,z6,z122]),(1,[z1,z2,z3,z15,z4,z5]),(0,[z1,z123,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z124])],[],[(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z1,z37,z2,z3,z46,z5,z6])],[(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z128,z3,z4,z5,z6]),(1,[z1,z51,z129,z4,z5,z6]),(0,[z1,z51,z2,z129,z4,z5,z6])],[(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z131,z4,z5,z6])],[(0,[z1,z107,z2,z3,z4,z27,z6])]],
   [[(0,[z1,z51,z3,z129,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z132]),(0,[z1,z2,z3,z4,z5,z133,z6]),(0,[z1,z2,z3,z4,z5,z134,z6])],[(0,[z1,z69,z70,z3,z4,z5,z6]),(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z136,z6])],[(0,[z1,z2,z3,z4,z137,z5,z6]),(0,[z1,z3,z129,z4,z91,z5,z6])],[(0,[z1,z2,z3,z138,z4,z5,z6]),(0,[z1,z139,z3,z4,z5,z6,z122]),(0,[z1,z2,z3,z4,z5,z140,z6]),(0,[z54,z2,z55,z3,z4,z5,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z142,z6]),(0,[z1,z143,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z144]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z75,z146,z6])],[(0,[z41,z1,z2,z138,z4,z5,z6]),(0,[z147,z42,z2,z3,z4,z5,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z149,z5,z6]),(0,[z1,z150,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z151,z5,z6]),(0,[z152,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z153,z4,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6])],[(0,[z155,z1,z2,z156,z4,z5,z6]),(0,[z157,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z158,z3,z4,z5,z6]),(0,[z155,z1,z2,z3,z68,z4,z5]),(0,[z1,z2,z3,z159,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z6]),(0,[z1,z2,z3,z4,z5,z6,z160])],[(1,[z1,z2,z161,z4,z5,z6]),(0,[z1,z2,z3,z162,z4,z5,z6]),(0,[z1,z2,z3,z4,z163,z5,z6]),(0,[z1,z2,z164,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z165,z6])],[(0,[z1,z2,z3,z166,z4,z5,z6]),(0,[z1,z167,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z168,z6]),(0,[z1,z69,z2,z70,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z169,z6]),(1,[z1,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z170,z5,z6])],[(0,[z171,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z172])],[(1,[z1,z2,z3,z173,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z174]),(0,[z1,z2,z3,z4,z5,z6,z175]),(0,[z1,z176,z2,z3,z4,z5,z6]),(0,[z177,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z50,z5,z6,z122])],[(0,[z1,z178,z2,z3,z4,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z180,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z46,z5,z6]),(0,[z1,z107,z2,z3,z4,z5,z75])],[(1,[z1,z2,z3,z4,z5,z181]),(0,[z1,z2,z70,z182,z4,z5,z6]),(0,[z1,z70,z3,z129,z4,z5,z6]),(0,[z1,z183,z184,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z2,z3,z4,z5,z186,z6])],[(0,[z2,z3,z187,z4,z16,z5,z6]),(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z189,z6]),(0,[z1,z2,z3,z4,z5,z6,z190])]],
   [[(1,[z1,z183,z3,z91,z5,z6]),(0,[z1,z97,z3,z4,z5,z49,z6]),(0,[z1,z191,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z192,z6]),(0,[z1,z2,z3,z193,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z194])],[(0,[z1,z2,z3,z4,z28,z5,z195]),(1,[z1,z2,z3,z4,z5,z196]),(0,[z1,z2,z19,z3,z20,z5,z6]),(0,[z1,z2,z3,z45,z46,z5,z6]),(0,[z1,z2,z3,z4,z5,z197,z6])],[(0,[z1,z2,z3,z4,z5,z198,z6]),(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z200,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z201]),(0,[z1,z2,z202,z4,z5,z203,z6]),(0,[z1,z2,z3,z204,z4,z5,z6])],[(0,[z1,z2,z205,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z206,z6]),(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z1,z96,z2,z3,z4,z5,z122]),(0,[z1,z38,z2,z3,z4,z47,z6])],[(0,[z1,z208,z2,z3,z4,z5,z6]),(0,[z1,z107,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z27,z75,z6])],[(0,[z54,z1,z2,z182,z4,z5,z6]),(0,[z1,z2,z209,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z16,z5,z6]),(0,[z210,z1,z2,z3,z187,z5,z6]),(1,[z1,z211,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z27,z6]),(0,[z1,z2,z3,z4,z5,z75,z12]),(0,[z1,z212,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z213]),(0,[z1,z214,z2,z3,z4,z5,z6]),(0,[z1,z215,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z27,z6])]],
   [[(0,[z1,z2,z3,z4,z216,z5,z6]),(0,[z1,z2,z202,z55,z4,z5,z6]),(0,[z1,z217,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z203,z6,z218]),(0,[z1,z38,z2,z3,z45,z5,z6])],[(0,[z1,z2,z3,z219,z4,z5,z6])],[(0,[z1,z220,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z221,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z222]),(1,[z1,z184,z3,z223,z5,z6]),(0,[z1,z2,z224,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z225]),(0,[z1,z2,z3,z4,z5,z6,z226]),(0,[z1,z2,z3,z4,z227,z5,z6]),(0,[z1,z2,z3,z4,z228,z5,z6]),(1,[z1,z107,z2,z3,z4,z13])],[(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z1,z2,z3,z4,z5,z122,z13]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z231])],[(0,[z1,z2,z3,z4,z232,z5,z6]),(0,[z1,z2,z3,z4,z233,z5,z6])],[(0,[z155,z1,z2,z3,z4,z234,z6]),(0,[z1,z2,z235,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z236]),(0,[z1,z2,z3,z4,z5,z237,z6]),(0,[z1,z37,z2,z3,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z238])],[(0,[z1,z2,z239,z3,z4,z5,z6])]],
   [[(0,[z1,z240,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z241]),(0,[z1,z2,z3,z4,z5,z64,z6])],[(0,[z1,z2,z242,z3,z4,z5,z6])],[(0,[z243,z1,z2,z3,z4,z5,z6]),(0,[z2,z55,z3,z182,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z244]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z3,z4,z5,z246,z6])],[(0,[z1,z2,z3,z4,z5,z175,z122]),(0,[z1,z247,z2,z3,z4,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z248]),(0,[z1,z2,z3,z249,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z250,z6]),(0,[z1,z2,z3,z4,z28,z5,z6]),(0,[z1,z96,z2,z3,z4,z5,z203]),(0,[z1,z251,z2,z3,z4,z5,z6])],[(0,[z1,z252,z2,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z5,z169]),(0,[z1,z2,z3,z4,z253,z5,z6]),(0,[z1,z254,z2,z3,z4,z62,z6]),(0,[z1,z2,z3,z4,z5,z203,z13])],[(1,[z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z3,z4,z5,z6,z256])]],
   [[(0,[z257,z1,z2,z3,z4,z5,z6]),(1,[z1,z258,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z259,z6]),(0,[z1,z2,z44,z3,z4,z5,z6])],[(0,[z260,z1,z2,z3,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z6]),(0,[z1,z184,z3,z129,z4,z5,z6]),(0,[z1,z2,z3,z262,z4,z5,z6]),(0,[z263,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z182,z4,z5,z6,z218]),(0,[z1,z96,z2,z3,z4,z5,z248]),(0,[z264,z1,z2,z3,z4,z5,z6]),(0,[z1,z265,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z266])],[(0,[z1,z267,z2,z3,z4,z5,z6]),(0,[z1,z268,z2,z3,z4,z5,z6]),(0,[z269,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z148,z1,z2,z55,z4,z5,z6]),(1,[z1,z2,z3,z271,z5,z6]),(1,[z1,z99,z3,z4,z50,z6]),(0,[z1,z2,z19,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z146,z6])],[(0,[z210,z1,z2,z3,z16,z5,z6]),(0,[z1,z272,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z273,z5,z6]),(0,[z1,z74,z2,z3,z4,z64,z6]),(0,[z1,z2,z3,z4,z5,z6,z274]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z75,z6])],[(0,[z1,z276,z2,z3,z4,z5,z6]),(0,[z1,z102,z2,z3,z4,z16,z5]),(0,[z116,z1,z2,z3,z4,z5,z175]),(0,[z1,z2,z3,z68,z4,z5,z122]),(0,[z1,z2,z3,z277,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z278,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z1,z2,z3,z4,z280,z5,z6]),(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z282,z6]),(0,[z1,z2,z3,z4,z5,z6,z283]),(0,[z1,z284,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z285,z5,z6]),(0,[z1,z107,z2,z3,z4,z5,z6])],[(0,[z147,z1,z3,z4,z50,z5,z6]),(0,[z1,z286,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z287,z4,z5,z6]),(0,[z1,z2,z288,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z289,z6])],[(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z291,z6]),(0,[z1,z2,z292,z3,z4,z5,z6]),(0,[z293,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z294,z4,z5,z6]),(0,[z1,z295,z2,z3,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(0,[z1,z2,z3,z68,z5,z76,z6]),(0,[z1,z2,z3,z4,z5,z296,z6])],[(0,[z1,z2,z3,z4,z297,z5,z6]),(0,[z1,z2,z3,z129,z4,z5,z6]),(0,[z1,z2,z3,z298,z4,z5,z6]),(0,[z1,z299,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z300]),(0,[z155,z1,z2,z3,z4,z5,z175]),(1,[z116,z2,z3,z4,z5,z229]),(0,[z1,z301,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z302,z5,z6])],[(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z1,z184,z2,z3,z4,z5,z196])],[(0,[z1,z2,z3,z303,z4,z5,z6])]],
   [[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z304,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z305,z6]),(0,[z1,z2,z3,z4,z5,z306,z6]),(0,[z1,z307,z2,z3,z4,z5,z6]),(0,[z308,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z309]),(1,[z1,z2,z3,z45,z46,z6])],[(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z1,z183,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z311,z5,z6]),(0,[z1,z312,z2,z3,z4,z5,z6])],[(0,[z1,z313,z2,z3,z4,z5,z6]),(0,[z1,z314,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z315]),(0,[z1,z2,z3,z4,z5,z316,z6]),(0,[z1,z317,z2,z3,z4,z5,z6]),(0,[z1,z318,z2,z3,z4,z5,z6]),(0,[z1,z2,z319,z3,z4,z5,z6]),(0,[z1,z2,z320,z3,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z229,z122])],[(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z323,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(1,[z1,z96,z2,z4,z5,z218])],[(0,[z1,z325,z2,z3,z4,z5,z6]),(0,[z1,z326,z2,z3,z4,z5,z6]),(1,[z1,z74,z2,z4,z64,z6]),(0,[z1,z327,z2,z3,z5,z64,z6])],[(0,[z1,z2,z3,z4,z5,z328,z6]),(0,[z1,z2,z3,z4,z329,z5,z6]),(0,[z1,z2,z3,z4,z330,z5,z6]),(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z1,z2,z3,z332,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z333,z6])]],
   [[(0,[z334,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z335,z5,z6]),(0,[z1,z2,z3,z4,z5,z336,z6]),(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z1,z2,z3,z4,z339,z5,z6])],[(0,[z1,z340,z2,z3,z4,z5,z6]),(0,[z1,z51,z69,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z341,z5,z6]),(1,[z1,z254,z2,z3,z4,z6]),(0,[z1,z2,z4,z5,z165,z47,z6]),(0,[z1,z2,z3,z4,z5,z342,z6])],[(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z344,z6]),(0,[z1,z2,z345,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z203,z6])],[(0,[z1,z2,z202,z182,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z155,z1,z2,z3,z294,z5,z6]),(0,[z347,z1,z2,z3,z4,z5,z6]),(0,[z1,z74,z2,z3,z4,z5,z241]),(0,[z1,z2,z3,z4,z5,z348,z6]),(0,[z1,z2,z3,z4,z5,z6,z349]),(0,[z1,z2,z3,z4,z5,z6,z13])],[(0,[z1,z2,z3,z223,z187,z5,z6]),(0,[z1,z350,z2,z3,z4,z5,z6])],[(0,[z351,z1,z2,z3,z4,z23,z6]),(0,[z116,z1,z2,z3,z68,z4,z5]),(0,[z1,z2,z3,z352,z4,z5,z6])],[(0,[z1,z2,z161,z3,z4,z5,z6]),(0,[z1,z353,z2,z3,z4,z5,z6]),(1,[z1,z299,z3,z4,z5,z248])],[(0,[z1,z299,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z248,z175]),(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z68,z4,z5,z248]),(0,[z1,z2,z3,z4,z5,z6,z12]),(0,[z1,z355,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z219,z5,z6]),(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z1,z357,z2,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6])],[(0,[z358,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z129,z4,z5,z6]),(0,[z1,z2,z3,z187,z5,z6,z12]),(0,[z359,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z181,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z360,z4,z5,z6]),(0,[z1,z2,z361,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z362,z6]),(0,[z1,z2,z3,z363,z4,z5,z6])],[(1,[z155,z2,z3,z4,z5,z175]),(1,[z1,z2,z3,z4,z364,z6])],[(0,[z1,z2,z365,z3,z4,z5,z6]),(0,[z1,z74,z2,z20,z4,z5,z6])],[(0,[z1,z2,z3,z187,z4,z5,z6]),(0,[z351,z2,z3,z4,z28,z5,z6]),(0,[z1,z2,z3,z4,z28,z5,z213]),(0,[z155,z1,z40,z2,z3,z4,z5]),(0,[z1,z2,z3,z366,z4,z5,z6]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z368,z3,z4,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z241,z6])],[(0,[z1,z2,z3,z4,z5,z6,z98]),(0,[z1,z37,z292,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z63,z6]),(0,[z1,z2,z3,z45,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z369,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z370]),(1,[z1,z371,z2,z4,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6])],[(0,[z1,z373,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z374]),(0,[z1,z2,z3,z375,z4,z5,z6])],[(0,[z1,z2,z376,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z377]),(0,[z1,z2,z202,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z378,z6])],[(0,[z1,z2,z3,z4,z5,z379,z6]),(0,[z1,z2,z3,z4,z380,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z1,z371,z2,z4,z5,z47,z6])],[(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z50,z6]),(1,[z1,z2,z3,z4,z58,z6]),(0,[z1,z383,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z384,z6]),(0,[z1,z184,z2,z3,z4,z5,z6]),(0,[z1,z299,z97,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z50,z6])],[(1,[z1,z2,z3,z4,z259,z6]),(0,[z1,z385,z2,z3,z4,z5,z6]),(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z28,z5,z23,z6])]],
   [[(0,[z148,z1,z2,z182,z4,z5,z6]),(0,[z22,z2,z3,z4,z5,z23,z6]),(0,[z1,z2,z3,z4,z5,z387,z6]),(0,[z1,z388,z2,z3,z4,z5,z6]),(0,[z1,z96,z2,z4,z5,z6,z218])],[(0,[z1,z2,z3,z4,z389,z5,z6])],[(0,[z1,z2,z390,z3,z182,z4,z5]),(0,[z391,z1,z2,z3,z187,z5,z6]),(0,[z155,z1,z2,z392,z4,z5,z6]),(0,[z1,z393,z2,z3,z4,z5,z6]),(0,[z1,z2,z394,z3,z4,z5,z6])],[(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z1,z396,z2,z3,z4,z5,z6]),(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z400,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z223,z16,z5,z6]),(0,[z155,z2,z3,z4,z5,z6,z175]),(0,[z1,z37,z401,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z62,z5,z6]),(0,[z1,z96,z2,z3,z4,z5,z218]),(0,[z1,z2,z3,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z403,z5,z6])],[(0,[z1,z2,z3,z4,z234,z5,z6])],[(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z1,z405,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z406]),(0,[z1,z407,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z408]),(0,[z1,z2,z3,z4,z5,z6,z6])]],
   [[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z409,z6])],[(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z410,z6]),(0,[z1,z401,z2,z3,z4,z5,z6]),(0,[z1,z411,z2,z3,z4,z5,z6])],[(0,[z1,z2,z20,z4,z62,z5,z6]),(0,[z1,z412,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z414,z2,z3,z4,z5,z6]),(0,[z1,z2,z415,z3,z4,z5,z6]),(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z416,z5,z6]),(0,[z1,z2,z3,z4,z364,z62,z6])],[(0,[z1,z2,z417,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z418,z6])],[(0,[z41,z1,z2,z3,z4,z5,z6]),(1,[z54,z2,z55,z4,z5,z6]),(0,[z155,z1,z2,z3,z4,z5,z75]),(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z203]),(0,[z1,z2,z3,z421,z4,z5,z6])],[(0,[z1,z2,z3,z422,z4,z5,z6]),(0,[z116,z2,z3,z4,z5,z229,z6]),(0,[z1,z2,z3,z423,z4,z5,z6]),(0,[z1,z2,z424,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z425])],[(0,[z1,z3,z4,z335,z5,z23,z6]),(0,[z1,z2,z3,z4,z426,z5,z6]),(0,[z1,z427,z2,z3,z4,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z76]),(1,[z1,z82,z3,z4,z5,z6])]],
   [[(0,[z1,z74,z2,z3,z4,z5,z120])],[(0,[z1,z2,z3,z4,z173,z5,z6]),(0,[z1,z428,z2,z3,z4,z5,z6]),(1,[z1,z252,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z429,z6])],[(0,[z1,z430,z2,z3,z4,z5,z6]),(1,[z1,z414,z2,z3,z4,z5]),(0,[z1,z431,z2,z3,z4,z5,z6]),(0,[z1,z99,z97,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z432])],[(0,[z1,z2,z3,z4,z5,z433,z6]),(0,[z147,z1,z42,z3,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z248]),(0,[z1,z2,z3,z4,z5,z6,z434]),(0,[z1,z2,z435,z3,z4,z5,z6])],[(0,[z155,z1,z2,z3,z4,z5,z13]),(0,[z1,z436,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z6])],[(0,[z1,z2,z3,z4,z5,z437,z6]),(1,[z1,z2,z156,z4,z5,z6]),(0,[z1,z37,z74,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z438,z5,z6]),(0,[z1,z299,z3,z4,z5,z248,z6]),(0,[z1,z2,z3,z4,z5,z6,z439]),(0,[z1,z2,z440,z3,z4,z5,z6])],[(0,[z1,z2,z3,z441,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z442,z6]),(0,[z1,z443,z2,z3,z4,z5,z6]),(0,[z444,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z255,z5,z6]),(0,[z1,z414,z2,z3,z182,z4,z5]),(0,[z445,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z20,z4,z192,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z132]),(0,[z1,z2,z4,z192,z5,z64,z6])],[(0,[z391,z1,z2,z3,z16,z5,z6]),(0,[z1,z447,z2,z3,z4,z5,z6])],[(0,[z1,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z182,z4,z5,z6]),(0,[z351,z22,z2,z3,z4,z5,z6]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z449,z2,z3,z4,z5,z6]),(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z192,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z451])],[(0,[z1,z452,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z454,z6]),(0,[z1,z455,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z456,z5,z6]),(0,[z1,z457,z2,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z132]),(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z1,z2,z459,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z460])],[(0,[z1,z2,z3,z4,z461,z5,z6]),(0,[z1,z37,z2,z4,z62,z5,z6])],[(0,[z1,z462,z2,z3,z4,z5,z6]),(0,[z1,z69,z2,z129,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z463]),(0,[z1,z2,z3,z4,z5,z248,z75]),(0,[z1,z2,z3,z4,z464,z5,z6])]],
   [[(0,[z41,z1,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z465,z6]),(0,[z1,z466,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z467,z4,z5,z6])],[(0,[z1,z468,z2,z3,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z210,z2,z3,z187,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z4,z470,z5,z6]),(0,[z1,z471,z2,z3,z4,z5,z6])],[(0,[z1,z217,z3,z4,z5,z6,z122]),(0,[z1,z472,z2,z3,z4,z5,z6])],[(0,[z473,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z474,z3,z4,z5,z6]),(0,[z1,z217,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z6,z39])],[(0,[z1,z2,z3,z4,z475,z5,z6])],[(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z477,z4,z5,z6]),(0,[z1,z37,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z364,z5,z6]),(0,[z1,z2,z3,z5,z76,z6,z12])],[(0,[z1,z2,z3,z4,z5,z248,z13]),(0,[z1,z2,z3,z4,z5,z165,z6])],[(0,[z1,z2,z3,z68,z187,z5,z6]),(0,[z1,z2,z3,z478,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z479,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z480,z6]),(0,[z1,z2,z19,z3,z62,z5,z6]),(0,[z1,z481,z2,z3,z4,z5,z6])],[(1,[z391,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z4,z482,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z483,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z484])],[(0,[z41,z1,z2,z3,z173,z5,z6]),(0,[z148,z2,z3,z182,z4,z5,z6]),(0,[z1,z2,z3,z485,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z486,z6]),(0,[z1,z2,z487,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z75])],[(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z490]),(1,[z1,z2,z3,z4,z234,z6]),(1,[z1,z217,z3,z4,z5,z122])],[(0,[z41,z1,z2,z3,z4,z5,z181]),(0,[z391,z2,z3,z4,z16,z5,z6]),(0,[z1,z183,z3,z4,z91,z5,z6])],[(0,[z1,z2,z3,z491,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z492,z6]),(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z1,z2,z3,z4,z494,z5,z6])],[(0,[z41,z1,z97,z3,z4,z5,z6]),(0,[z1,z184,z3,z223,z4,z5,z6]),(0,[z1,z495,z2,z3,z4,z5,z6]),(0,[z1,z38,z2,z44,z3,z4,z6])]],
   [[(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z497,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z213]),(0,[z155,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z498,z6]),(0,[z1,z2,z3,z4,z499,z5,z6]),(0,[z1,z500,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z501,z6]),(1,[z1,z2,z3,z4,z5,z120]),(0,[z1,z38,z2,z3,z5,z47,z6])],[(0,[z1,z2,z3,z4,z5,z502,z6]),(0,[z155,z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z44,z3,z4,z64,z6]),(0,[z1,z503,z2,z3,z4,z5,z6])],[(0,[z1,z504,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z23,z6]),(0,[z1,z2,z3,z4,z271,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z13])],[(0,[z155,z116,z2,z3,z4,z5,z6]),(0,[z116,z1,z2,z202,z3,z4,z5]),(0,[z116,z1,z40,z2,z3,z4,z5]),(0,[z1,z2,z505,z3,z4,z5,z6]),(0,[z1,z2,z3,z506,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z507]),(0,[z1,z2,z3,z68,z4,z5,z76]),(0,[z1,z2,z508,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z509,z6]),(1,[z210,z2,z3,z187,z5,z6]),(0,[z1,z2,z3,z4,z510,z5,z6])],[(0,[z1,z2,z3,z4,z5,z511,z6]),(0,[z1,z512,z2,z3,z4,z5,z6]),(0,[z1,z74,z2,z44,z4,z5,z6]),(0,[z1,z74,z2,z3,z45,z4,z6])],[(1,[z1,z2,z138,z4,z5,z6]),(0,[z1,z2,z3,z4,z513,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z514]),(0,[z1,z37,z2,z3,z62,z5,z6]),(0,[z515,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z516,z3,z4,z5,z6]),(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z518,z4,z5,z6]),(0,[z1,z2,z3,z45,z4,z46,z6])]],
   [[(0,[z1,z2,z390,z3,z4,z5,z6]),(0,[z1,z51,z2,z70,z4,z5,z6]),(0,[z1,z2,z519,z3,z4,z5,z6]),(0,[z1,z183,z2,z3,z223,z5,z6]),(0,[z1,z2,z3,z4,z520,z5,z6]),(0,[z1,z2,z3,z4,z5,z521,z6])],[(0,[z155,z1,z2,z202,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z1,z2,z3,z4,z5,z523,z6]),(0,[z1,z2,z3,z223,z4,z5,z6]),(0,[z524,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z525,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z75,z122])],[],[(0,[z1,z2,z3,z4,z5,z6,z526]),(0,[z1,z527,z2,z3,z4,z5,z6]),(0,[z1,z217,z2,z3,z4,z5,z248])],[(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z530,z6]),(0,[z1,z2,z3,z4,z248,z6,z531]),(0,[z1,z2,z3,z4,z532,z5,z6]),(0,[z1,z2,z3,z4,z5,z533,z6]),(1,[z1,z2,z44,z4,z192,z6])],[(0,[z1,z2,z3,z4,z534,z5,z6])],[(0,[z535,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z536,z6]),(0,[z1,z2,z3,z4,z5,z6,z537]),(0,[z1,z2,z3,z4,z5,z538,z6]),(0,[z1,z2,z3,z4,z539,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z13])],[(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z148,z54,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z68,z16,z5,z6]),(0,[z1,z299,z2,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z541,z6]),(0,[z1,z2,z3,z4,z5,z75,z218]),(0,[z1,z2,z3,z45,z4,z47,z6])]],
   [[(0,[z1,z42,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z195,z6]),(0,[z1,z2,z542,z3,z4,z5,z6])],[(0,[z41,z1,z2,z3,z4,z5,z526])],[(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z545,z1,z2,z3,z4,z5,z6]),(0,[z1,z183,z2,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z248,z6]),(1,[z1,z2,z3,z4,z27,z75])],[(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z248,z229]),(1,[z1,z2,z3,z4,z5,z98]),(0,[z1,z547,z2,z3,z4,z5,z6])],[(0,[z1,z548,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z531]),(0,[z1,z2,z202,z3,z4,z5,z218])],[(0,[z41,z147,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z3,z4,z5,z248,z6,z122]),(1,[z1,z2,z3,z4,z5,z142])],[(0,[z41,z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z3,z4,z550,z5,z6]),(0,[z1,z551,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z552,z5,z6]),(0,[z1,z2,z3,z4,z553,z5,z6]),(0,[z1,z2,z3,z554,z4,z5,z6])],[(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z156,z4,z5,z6]),(0,[z1,z2,z3,z20,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z13]),(0,[z1,z2,z3,z4,z5,z146,z6])]],
   [[(0,[z41,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z70,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z556,z5,z6]),(0,[z1,z557,z2,z3,z4,z5,z6]),(0,[z1,z2,z558,z3,z4,z5,z6]),(0,[z1,z559,z2,z3,z4,z5,z6]),(1,[z1,z38,z2,z3,z47,z6]),(0,[z1,z2,z3,z4,z5,z6,z560])],[(0,[z1,z561,z2,z3,z4,z5,z6]),(0,[z1,z562,z2,z3,z4,z5,z6]),(0,[z351,z1,z2,z3,z4,z28,z6])],[(0,[z116,z1,z2,z3,z4,z5,z75]),(0,[z1,z2,z3,z563,z4,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z565,z6])],[(0,[z1,z2,z3,z4,z5,z6,z566]),(0,[z1,z2,z567,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z75,z203]),(0,[z1,z2,z3,z4,z5,z6,z568])],[(0,[z1,z569,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z570,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z6]),(0,[z155,z1,z2,z3,z4,z168,z6]),(0,[z1,z2,z3,z4,z571,z5,z6])],[(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z572,z4,z5,z6]),(0,[z1,z573,z2,z3,z4,z5,z6]),(0,[z1,z574,z2,z3,z4,z5,z6])],[(1,[z148,z2,z182,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z6])],[(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z6,z13])],[(1,[z147,z42,z3,z4,z5,z6]),(0,[z1,z576,z2,z3,z4,z5,z6]),(0,[z1,z258,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z294,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z50,z5,z6]),(0,[z1,z97,z3,z4,z5,z6,z122]),(0,[z1,z2,z3,z4,z577,z5,z6]),(0,[z1,z2,z3,z4,z578,z5,z6]),(0,[z1,z2,z579,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z580,z6]),(0,[z1,z2,z581,z3,z4,z5,z6]),(0,[z1,z299,z217,z3,z4,z5,z6]),(0,[z1,z38,z2,z19,z3,z5,z6])],[(0,[z1,z2,z582,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z583,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z584]),(0,[z1,z2,z3,z4,z5,z585,z6])],[(0,[z42,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z5,z6]),(0,[z1,z2,z19,z20,z4,z5,z6]),(0,[z1,z327,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z6])],[(0,[z1,z252,z3,z4,z5,z23,z6]),(0,[z1,z184,z2,z3,z223,z5,z6]),(0,[z1,z586,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z587,z6]),(0,[z1,z2,z3,z4,z192,z5,z6]),(0,[z1,z2,z3,z4,z588,z5,z6])],[(0,[z1,z2,z3,z4,z5,z589,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(0,[z1,z184,z69,z3,z4,z5,z6]),(0,[z1,z590,z2,z3,z4,z5,z6])],[(0,[z591,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z592,z4,z5,z6]),(0,[z1,z2,z3,z187,z91,z5,z6]),(0,[z1,z299,z2,z3,z4,z5,z248]),(0,[z1,z2,z3,z4,z5,z593,z6]),(0,[z1,z96,z2,z202,z4,z5,z6]),(0,[z1,z371,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z594,z5,z6])]],
   [[(0,[z155,z1,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z595]),(0,[z1,z97,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z596,z4,z5,z6]),(0,[z1,z2,z3,z4,z597,z5,z6])],[(0,[z1,z2,z3,z4,z598,z5,z6]),(0,[z1,z2,z3,z4,z5,z599,z6])],[(0,[z1,z2,z3,z4,z335,z5,z6]),(0,[z1,z600,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z6])],[(0,[z1,z2,z601,z3,z4,z5,z6]),(0,[z1,z602,z2,z3,z4,z5,z6]),(0,[z603,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z68,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z604,z6]),(0,[z1,z74,z2,z3,z4,z192,z6])],[(0,[z1,z2,z3,z4,z605,z5,z6]),(0,[z1,z606,z2,z3,z4,z5,z6]),(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z50,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z6,z608]),(0,[z1,z2,z609,z3,z4,z5,z6])],[(0,[z1,z299,z42,z3,z4,z5,z6]),(0,[z1,z610,z2,z3,z4,z5,z6]),(0,[z1,z184,z2,z3,z91,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z612,z5,z6]),(0,[z1,z2,z3,z4,z5,z613,z6])]],
   [[(0,[z147,z1,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z5,z6,z12]),(0,[z1,z614,z2,z3,z4,z5,z6]),(0,[z1,z615,z2,z3,z4,z5,z6]),(0,[z1,z616,z2,z3,z4,z5,z6])],[(0,[z1,z617,z2,z3,z4,z5,z6]),(0,[z618,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z1,z184,z2,z3,z4,z5,z374])],[(0,[z155,z1,z96,z2,z3,z4,z5]),(0,[z1,z2,z70,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z196,z6]),(0,[z1,z2,z3,z620,z4,z5,z6])],[(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z622,z5,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(1,[z1,z97,z3,z4,z49,z6])],[(0,[z1,z624,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z625,z5,z6]),(0,[z1,z38,z2,z3,z4,z5,z142]),(0,[z1,z82,z3,z4,z5,z75,z6])],[(0,[z1,z626,z2,z3,z4,z5,z6]),(0,[z1,z2,z627,z3,z4,z5,z6]),(0,[z1,z2,z392,z3,z4,z5,z6]),(0,[z1,z628,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z629,z4,z5,z6])],[(0,[z41,z1,z2,z3,z219,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z631,z4,z5,z6]),(0,[z1,z632,z2,z3,z4,z5,z6]),(0,[z1,z633,z2,z3,z4,z5,z6])]],
   [[(1,[z41,z139,z3,z4,z5,z6]),(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z635,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z23,z6,z13]),(1,[z1,z2,z392,z4,z5,z6]),(0,[z1,z299,z3,z4,z50,z5,z6]),(1,[z1,z292,z3,z4,z5,z6])],[(0,[z636,z1,z2,z3,z4,z5,z6])],[(0,[z155,z1,z258,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z122])],[(0,[z41,z1,z2,z161,z4,z5,z6]),(0,[z1,z2,z3,z637,z4,z5,z6]),(0,[z1,z2,z3,z4,z638,z5,z6]),(0,[z1,z639,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z374]),(0,[z1,z2,z3,z4,z5,z6,z640]),(0,[z1,z2,z3,z4,z641,z5,z6])],[(0,[z1,z2,z3,z4,z58,z248,z6])],[(0,[z1,z2,z3,z4,z75,z6,z13])],[(0,[z116,z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z4,z5,z642,z6]),(0,[z1,z643,z2,z3,z4,z5,z6])],[(0,[z147,z1,z97,z3,z4,z5,z6]),(0,[z155,z1,z2,z3,z271,z5,z6]),(0,[z1,z37,z2,z4,z192,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z644]),(0,[z1,z2,z3,z4,z5,z6,z218]),(0,[z1,z38,z2,z3,z4,z46,z6]),(0,[z1,z2,z645,z3,z4,z5,z6]),(0,[z1,z2,z646,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z647,z5,z6]),(0,[z1,z648,z2,z3,z4,z5,z6]),(0,[z649,z1,z2,z3,z4,z5,z6])],[(0,[z650,z1,z2,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z6,z13]),(1,[z1,z2,z3,z4,z6,z531])],[(1,[z1,z2,z390,z3,z4,z5]),(0,[z1,z3,z223,z4,z91,z5,z6]),(0,[z1,z99,z2,z3,z4,z6,z13]),(1,[z1,z327,z2,z3,z5,z6]),(0,[z1,z38,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z651,z5,z6])],[(0,[z1,z2,z3,z652,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z653,z6]),(0,[z1,z2,z3,z68,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z654])],[(0,[z1,z2,z3,z4,z655,z5,z6]),(0,[z1,z656,z2,z3,z4,z5,z6]),(0,[z1,z657,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z169]),(1,[z1,z401,z3,z4,z5,z6]),(0,[z658,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z659,z6])],[(0,[z41,z1,z2,z3,z4,z259,z6]),(0,[z1,z74,z2,z3,z4,z5,z6]),(0,[z1,z74,z2,z4,z5,z64,z6]),(0,[z1,z2,z3,z4,z5,z6,z660])],[(0,[z1,z2,z3,z4,z5,z6,z661]),(0,[z1,z2,z3,z4,z662,z5,z6])]],
   [[(0,[z22,z1,z2,z3,z4,z23,z6]),(0,[z1,z2,z3,z4,z50,z23,z6]),(1,[z351,z2,z3,z4,z28,z6]),(0,[z663,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z664,z3,z4,z5,z6]),(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z666,z6])],[(0,[z1,z2,z3,z4,z5,z667,z6]),(0,[z1,z2,z3,z4,z28,z49,z6]),(0,[z1,z668,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z669,z4,z5,z6]),(0,[z1,z2,z3,z4,z670,z5,z6]),(0,[z1,z37,z2,z19,z4,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z672,z6])],[(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z674,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z675,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z676]),(0,[z1,z2,z3,z4,z5,z6,z677]),(0,[z1,z2,z3,z4,z5,z678,z6])],[(0,[z1,z2,z3,z679,z4,z5,z6]),(0,[z2,z3,z4,z5,z229,z6,z175]),(0,[z1,z2,z3,z4,z5,z680,z6]),(0,[z1,z2,z3,z4,z681,z5,z6]),(0,[z1,z40,z2,z3,z4,z5,z12])],[(0,[z1,z99,z3,z4,z50,z5,z6])],[(0,[z391,z210,z2,z3,z4,z5,z6])],[(0,[z1,z682,z2,z3,z4,z5,z6]),(0,[z1,z683,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z684,z5,z6]),(0,[z1,z685,z2,z3,z4,z5,z6]),(0,[z1,z686,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z687]),(0,[z1,z688,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z689,z2,z3,z4,z5,z6]),(0,[z1,z2,z690,z3,z4,z5,z6]),(0,[z691,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z1,z2,z693,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z694,z5,z6])],[(0,[z1,z2,z182,z129,z4,z5,z6]),(0,[z1,z2,z3,z16,z91,z5,z6]),(1,[z1,z2,z3,z4,z5,z195]),(0,[z1,z2,z3,z4,z5,z6,z695]),(1,[z1,z40,z2,z3,z5,z12]),(0,[z696,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z697,z3,z4,z5,z6])],[(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z168,z6]),(0,[z1,z2,z699,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z700,z5,z6]),(1,[z1,z2,z202,z4,z5,z203]),(0,[z701,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z702,z6])],[(0,[z1,z2,z55,z4,z5,z6,z218]),(1,[z1,z102,z2,z3,z4,z5]),(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z704,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z705])],[(1,[z1,z2,z3,z4,z5,z526]),(0,[z1,z2,z3,z706,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z5,z707]),(0,[z1,z2,z3,z219,z5,z526]),(0,[z1,z708,z3,z4,z5,z6]),(0,[z358,z2,z3,z4,z28,z6]),(0,[z1,z2,z3,z4,z499,z13]),(0,[z1,z709,z3,z4,z5,z6])],[(0,[z1,z40,z2,z3,z271,z5]),(0,[z1,z51,z129,z4,z5,z6]),(0,[z1,z2,z710,z4,z5,z6]),(0,[z1,z40,z2,z3,z5,z432]),(0,[z1,z2,z711,z3,z4,z5]),(1,[z1,z371,z38,z2,z6])],[(0,[z1,z2,z3,z4,z712,z6]),(0,[z41,z427,z3,z4,z5,z6]),(0,[z1,z2,z713,z3,z4,z5]),(0,[z1,z2,z3,z4,z714,z6]),(0,[z391,z2,z3,z15,z16,z5]),(0,[z1,z436,z3,z4,z5,z122]),(0,[z1,z184,z3,z223,z5,z374])],[(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z716,z3,z4,z5,z6]),(0,[z1,z717,z3,z4,z5,z6]),(0,[z2,z3,z4,z718,z5,z6]),(0,[z372,z2,z3,z187,z5,z6]),(0,[z2,z3,z4,z719,z23,z6]),(0,[z2,z3,z4,z28,z719,z6]),(0,[z351,z2,z3,z4,z28,z195]),(0,[z1,z40,z211,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z720]),(0,[z1,z2,z3,z4,z721,z6]),(0,[z1,z69,z70,z4,z5,z132]),(0,[z1,z2,z4,z5,z6,z722]),(0,[z1,z217,z3,z4,z5,z723]),(0,[z724,z2,z3,z4,z5,z6]),(0,[z1,z38,z2,z3,z47,z39])]],
   [[(0,[z1,z2,z3,z4,z5,z725]),(0,[z155,z600,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z229,z726]),(0,[z1,z2,z3,z4,z5,z132]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z728,z4,z5,z6]),(0,[z1,z96,z2,z4,z5,z218])],[(0,[z1,z2,z3,z219,z255,z6]),(0,[z1,z569,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z729]),(0,[z1,z258,z3,z4,z234,z6]),(0,[z1,z69,z730,z4,z5,z6]),(0,[z1,z3,z4,z5,z723,z6]),(0,[z1,z74,z2,z4,z64,z6])],[(0,[z1,z2,z731,z4,z5,z6]),(0,[z391,z2,z3,z16,z5,z6]),(0,[z1,z732,z3,z4,z5,z6]),(0,[z2,z3,z187,z718,z5,z6]),(0,[z1,z2,z3,z294,z234,z6]),(0,[z1,z2,z3,z733,z5,z6])],[(0,[z1,z3,z4,z335,z5,z6]),(0,[z1,z2,z392,z4,z5,z6]),(0,[z1,z292,z3,z4,z5,z6]),(0,[z1,z69,z70,z4,z5,z144]),(0,[z1,z3,z4,z27,z75,z146])]],
   [[(0,[z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z70,z730,z4,z5,z6]),(0,[z1,z37,z74,z38,z2,z6]),(0,[z1,z254,z2,z3,z4,z6])],[(0,[z1,z2,z161,z4,z255,z6]),(0,[z1,z2,z735,z4,z5,z6]),(0,[z1,z371,z38,z2,z5,z6])],[(0,[z41,z736,z3,z4,z5,z6]),(0,[z420,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z1,z414,z2,z4,z5,z218]),(0,[z381,z2,z3,z4,z23,z6]),(0,[z1,z2,z3,z271,z234,z6]),(0,[z2,z3,z4,z5,z6,z726]),(0,[z1,z2,z3,z4,z738,z6]),(0,[z1,z3,z4,z5,z248,z723]),(0,[z739,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z740]),(0,[z1,z2,z741,z4,z5,z6]),(0,[z448,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z742])]],
   [[(0,[z1,z2,z4,z743,z5,z6]),(0,[z1,z744,z3,z4,z5,z6]),(0,[z1,z2,z3,z745,z5,z6]),(0,[z1,z2,z3,z4,z5,z120]),(0,[z1,z2,z4,z5,z6,z746])],[(0,[z1,z2,z156,z4,z168,z6]),(0,[z1,z82,z3,z4,z5,z169]),(0,[z1,z299,z3,z4,z5,z248]),(0,[z1,z2,z4,z5,z165,z6]),(0,[z1,z2,z3,z4,z5,z747])],[(0,[z1,z2,z138,z4,z255,z6]),(0,[z1,z2,z3,z4,z255,z181]),(0,[z1,z150,z70,z4,z5,z6]),(0,[z1,z2,z3,z4,z168,z6]),(0,[z1,z2,z3,z271,z5,z75]),(0,[z1,z2,z3,z4,z5,z39])],[(0,[z1,z2,z3,z4,z259,z526]),(0,[z148,z2,z748,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z750,z3,z4,z5,z6]),(0,[z155,z2,z3,z271,z5,z175]),(1,[z1,z730,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z173,z5,z6]),(0,[z1,z2,z3,z751,z5,z6]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z444,z2,z3,z16,z5,z6]),(0,[z753,z2,z3,z4,z5,z6]),(0,[z1,z38,z2,z3,z289,z6])],[(0,[z1,z2,z3,z754,z5,z6]),(0,[z1,z755,z3,z4,z5,z6]),(0,[z618,z2,z3,z4,z28,z6]),(0,[z756,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z757,z6]),(0,[z758,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z531]),(0,[z1,z2,z3,z4,z759,z6]),(0,[z1,z760,z2,z4,z5,z6])],[(0,[z1,z2,z138,z4,z5,z6]),(0,[z1,z2,z3,z761,z5,z6]),(0,[z1,z2,z3,z4,z5,z762]),(0,[z1,z327,z2,z3,z5,z6])],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z764,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z148,z414,z2,z182,z4,z5]),(0,[z261,z2,z182,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z457,z3,z223,z5,z6]),(0,[z1,z767,z3,z4,z5,z6]),(0,[z155,z2,z3,z4,z5,z175]),(0,[z1,z97,z3,z4,z126,z6]),(0,[z1,z2,z3,z4,z364,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z768]),(0,[z155,z2,z3,z4,z5,z726]),(0,[z1,z2,z3,z4,z769,z6]),(0,[z1,z183,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z5,z169]),(0,[z1,z371,z2,z45,z4,z6])],[(0,[z1,z3,z4,z5,z770,z6]),(0,[z1,z2,z3,z271,z5,z13]),(0,[z1,z2,z3,z4,z5,z196]),(0,[z1,z512,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z771]),(1,[z1,z2,z4,z5,z747]),(0,[z1,z2,z772,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z773])],[(0,[z1,z2,z774,z4,z5,z6]),(0,[z1,z2,z3,z4,z719,z6]),(0,[z1,z307,z129,z4,z5,z6]),(0,[z1,z74,z2,z4,z289,z6]),(0,[z1,z2,z3,z5,z63,z6]),(0,[z1,z74,z327,z2,z64,z6]),(0,[z1,z2,z4,z5,z775,z6]),(0,[z1,z2,z4,z5,z747,z218]),(0,[z1,z38,z2,z3,z47,z142])],[(0,[z1,z2,z3,z4,z776,z6]),(0,[z1,z777,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z351,z2,z3,z4,z28,z6]),(0,[z1,z208,z2,z3,z4,z13]),(0,[z1,z371,z2,z46,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z195,z779]),(0,[z1,z371,z2,z4,z5,z6]),(0,[z1,z2,z44,z4,z192,z6]),(0,[z1,z2,z4,z5,z6,z780])],[(0,[z1,z2,z781,z4,z5,z6]),(0,[z1,z252,z3,z4,z259,z6]),(0,[z1,z2,z3,z782,z5,z6]),(0,[z1,z783,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z784]),(0,[z1,z252,z3,z4,z49,z6]),(0,[z1,z211,z156,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z374]),(0,[z1,z74,z327,z2,z3,z6]),(0,[z1,z2,z3,z4,z5,z785])],[(0,[z1,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z786,z4,z5]),(0,[z1,z252,z3,z4,z5,z787]),(0,[z1,z254,z2,z19,z3,z6])],[(0,[z1,z2,z3,z788,z5,z6]),(0,[z1,z2,z789,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z14,z3,z91,z5,z6]),(0,[z1,z2,z3,z4,z6,z791]),(0,[z1,z2,z3,z4,z5,z792]),(1,[z1,z74,z327,z2,z6])],[(0,[z1,z2,z392,z4,z234,z6]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z2,z794,z4,z5,z6]),(0,[z1,z3,z4,z795,z49,z6]),(0,[z1,z40,z2,z3,z5,z785])],[(0,[z1,z2,z796,z4,z5,z6]),(0,[z41,z139,z3,z219,z5,z6]),(0,[z1,z2,z3,z4,z797,z6]),(0,[z1,z184,z3,z223,z5,z6]),(0,[z1,z3,z223,z798,z5,z6]),(0,[z1,z2,z799,z4,z5,z6]),(0,[z1,z254,z2,z20,z4,z6]),(0,[z1,z800,z2,z3,z4,z5])],[(0,[z1,z2,z3,z801,z5,z6]),(0,[z1,z2,z3,z4,z5,z802]),(0,[z2,z3,z4,z719,z5,z6]),(0,[z1,z2,z3,z4,z5,z787]),(0,[z1,z327,z2,z44,z3,z6]),(0,[z1,z107,z2,z3,z4,z13])]],
   [[(0,[z1,z2,z3,z4,z169,z13]),(0,[z1,z99,z3,z4,z795,z6]),(0,[z1,z2,z3,z4,z5,z803]),(0,[z1,z2,z3,z45,z285,z6])],[(0,[z1,z2,z3,z4,z5,z804]),(0,[z1,z2,z3,z4,z5,z805]),(0,[z806,z2,z3,z4,z5,z6]),(0,[z1,z807,z3,z4,z5,z6]),(0,[z1,z254,z2,z3,z4,z808]),(0,[z1,z40,z2,z3,z5,z12])],[(0,[z41,z139,z161,z4,z5,z6]),(0,[z1,z2,z3,z4,z809,z6]),(0,[z1,z2,z3,z4,z5,z810])],[(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z211,z202,z3,z4,z5]),(0,[z1,z2,z392,z4,z168,z6]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z503,z3,z4,z5,z122]),(0,[z1,z813,z2,z3,z4,z5]),(0,[z814,z2,z3,z4,z5,z6]),(0,[z1,z2,z815,z62,z5,z6]),(0,[z1,z2,z3,z46,z593,z6]),(0,[z1,z2,z202,z4,z5,z203])]],
   [[(0,[z1,z2,z3,z816,z4,z6]),(0,[z420,z2,z3,z4,z5,z175]),(0,[z1,z2,z3,z4,z5,z817]),(0,[z1,z355,z3,z4,z5,z122])],[(0,[z1,z2,z818,z3,z4,z5]),(0,[z1,z2,z202,z303,z4,z5]),(0,[z1,z2,z4,z5,z819,z6])],[(0,[z1,z2,z3,z4,z5,z526]),(0,[z736,z139,z3,z4,z5,z6]),(0,[z22,z252,z3,z4,z23,z6]),(0,[z1,z820,z3,z4,z5,z6])],[(0,[z41,z139,z3,z4,z5,z181]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z97,z3,z4,z521,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z2,z823,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z75]),(0,[z1,z51,z730,z4,z5,z6]),(0,[z1,z74,z327,z2,z4,z6])],[(0,[z1,z42,z3,z4,z5,z526]),(0,[z1,z2,z824,z4,z5,z6]),(0,[z1,z2,z825,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z826]),(1,[z2,z748,z4,z5,z6]),(0,[z1,z827,z3,z4,z5,z6]),(0,[z1,z2,z828,z4,z5,z6]),(0,[z155,z2,z3,z4,z234,z175]),(0,[z1,z500,z3,z91,z5,z6]),(0,[z1,z74,z2,z92,z4,z6]),(0,[z1,z2,z3,z829,z4,z5])],[(0,[z1,z2,z3,z830,z5,z6]),(0,[z1,z831,z2,z4,z5,z6]),(0,[z148,z2,z182,z4,z5,z6]),(0,[z1,z832,z3,z4,z5,z6]),(0,[z1,z2,z748,z4,z5,z6]),(0,[z1,z2,z3,z4,z833,z6]),(0,[z1,z2,z834,z4,z5,z6]),(0,[z1,z258,z3,z294,z5,z6]),(0,[z1,z2,z3,z798,z5,z6]),(0,[z1,z2,z19,z20,z5,z6]),(0,[z1,z37,z254,z2,z3,z6])],[(0,[z1,z2,z3,z4,z835,z6]),(0,[z1,z2,z3,z4,z836,z6]),(0,[z1,z102,z2,z3,z271,z5]),(0,[z1,z3,z4,z837,z5,z6]),(0,[z22,z2,z3,z4,z23,z6]),(0,[z1,z258,z156,z4,z5,z6]),(0,[z1,z2,z838,z4,z5,z6])]],
   [[(0,[z1,z258,z3,z4,z5,z6]),(0,[z1,z2,z3,z839,z5,z6]),(0,[z1,z2,z840,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z841]),(0,[z1,z2,z156,z294,z5,z6]),(0,[z1,z2,z3,z4,z795,z6]),(1,[z1,z2,z815,z5,z6]),(0,[z1,z2,z19,z5,z599,z6]),(0,[z1,z2,z3,z5,z6,z842])],[(0,[z147,z42,z3,z4,z5,z6]),(0,[z41,z139,z3,z4,z259,z6]),(0,[z1,z2,z3,z294,z5,z6]),(0,[z1,z2,z3,z4,z27,z195]),(0,[z1,z2,z730,z4,z5,z6]),(0,[z1,z299,z3,z4,z5,z723]),(0,[z1,z2,z3,z4,z5,z843]),(0,[z1,z2,z3,z5,z6,z785])],[(0,[z1,z2,z3,z4,z195,z13]),(0,[z1,z2,z3,z844,z47,z6])],[(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z2,z3,z846,z5,z6]),(0,[z177,z2,z3,z187,z5,z6]),(0,[z1,z211,z392,z4,z5,z6]),(0,[z155,z2,z3,z4,z168,z175]),(0,[z1,z2,z3,z4,z234,z13]),(0,[z1,z2,z4,z5,z203,z747]),(0,[z1,z2,z3,z4,z773,z13])]],
   [[(0,[z1,z2,z138,z173,z5,z6]),(0,[z1,z2,z3,z173,z5,z181]),(0,[z1,z252,z3,z4,z5,z6]),(0,[z2,z736,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z847,z6]),(0,[z1,z2,z156,z271,z5,z6]),(0,[z1,z3,z730,z4,z5,z6]),(0,[z1,z2,z848,z4,z5,z6]),(0,[z1,z97,z3,z4,z49,z98])],[(0,[z1,z2,z3,z271,z5,z6]),(0,[z1,z252,z3,z4,z5,z849]),(0,[z1,z2,z3,z850,z5,z6]),(0,[z1,z2,z3,z4,z5,z851]),(0,[z1,z3,z4,z5,z146,z6]),(0,[z1,z2,z3,z4,z852,z6]),(0,[z1,z82,z3,z4,z6,z13])],[(1,[z1,z3,z4,z5,z723]),(0,[z1,z37,z2,z62,z5,z6]),(0,[z1,z853,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z854]),(0,[z1,z855,z2,z3,z4,z5]),(0,[z293,z2,z55,z4,z5,z6]),(0,[z1,z252,z3,z4,z6,z13]),(0,[z1,z2,z3,z4,z856,z6]),(0,[z1,z97,z3,z4,z122,z13]),(0,[z1,z857,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z858,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z299,z3,z4,z5,z169]),(0,[z1,z38,z2,z609,z3,z6])],[(0,[z1,z2,z3,z4,z860,z6]),(0,[z1,z2,z3,z219,z259,z6]),(0,[z1,z102,z2,z3,z68,z5]),(0,[z1,z2,z3,z4,z861,z6]),(0,[z1,z862,z3,z4,z5,z195]),(0,[z1,z2,z202,z4,z5,z418]),(0,[z1,z863,z2,z3,z5,z6]),(0,[z1,z38,z2,z165,z47,z6])],[(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z2,z3,z4,z5,z849]),(0,[z1,z211,z3,z4,z168,z6]),(0,[z1,z2,z866,z4,z5,z6]),(0,[z1,z2,z867,z4,z5,z6]),(0,[z1,z2,z3,z4,z58,z75]),(0,[z1,z74,z327,z2,z5,z6]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z869,z3,z4,z5,z6]),(0,[z1,z96,z2,z4,z5,z747])],[(0,[z1,z870,z3,z4,z5,z6]),(0,[z1,z871,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z195]),(0,[z1,z99,z3,z4,z6,z660]),(0,[z1,z74,z2,z4,z64,z241])]],
   [[(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z3,z4,z50,z795,z6]),(1,[z1,z2,z3,z4,z773])],[(0,[z1,z2,z161,z4,z259,z6]),(0,[z1,z2,z873,z4,z5,z6]),(0,[z1,z139,z3,z4,z5,z526]),(0,[z1,z874,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z875,z6]),(0,[z1,z876,z3,z4,z5,z6]),(0,[z391,z2,z3,z718,z5,z6]),(0,[z116,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z877,z5,z6]),(0,[z1,z37,z2,z364,z62,z6]),(0,[z1,z37,z254,z2,z4,z6]),(0,[z1,z2,z3,z4,z775,z6]),(0,[z1,z688,z2,z4,z5,z218])],[(0,[z1,z2,z3,z878,z5,z6]),(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z82,z3,z4,z27,z6])],[(0,[z1,z2,z880,z4,z5,z6]),(0,[z1,z2,z3,z4,z881,z6]),(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z3,z4,z5,z642,z122]),(1,[z1,z37,z254,z2,z6]),(0,[z1,z2,z19,z815,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z883]),(0,[z54,z2,z748,z4,z5,z6]),(0,[z1,z884,z3,z4,z5,z6]),(0,[z155,z2,z3,z4,z5,z121]),(0,[z1,z2,z4,z775,z64,z6])],[(0,[z1,z885,z3,z4,z5,z6]),(0,[z1,z886,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z58,z13]),(0,[z1,z887,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z403,z75])],[(0,[z1,z2,z3,z4,z259,z181]),(0,[z1,z888,z2,z3,z4,z6]),(0,[z1,z252,z3,z4,z50,z6])],[(0,[z1,z2,z3,z889,z5,z6]),(0,[z1,z2,z3,z4,z5,z890])]],
   [[(0,[z41,z139,z3,z4,z255,z6]),(0,[z1,z2,z891,z4,z5,z6]),(0,[z147,z736,z3,z4,z5,z6]),(0,[z147,z3,z4,z461,z5,z6]),(0,[z1,z892,z2,z3,z4,z5]),(0,[z1,z893,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z351,z2,z3,z4,z28,z213]),(0,[z1,z97,z3,z4,z49,z6])],[(0,[z1,z2,z161,z4,z5,z526]),(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z2,z3,z896,z5,z6]),(0,[z1,z2,z3,z15,z4,z5]),(0,[z1,z258,z392,z4,z5,z6]),(0,[z1,z184,z3,z223,z5,z196]),(1,[z1,z2,z4,z775,z6])],[(0,[z1,z2,z392,z294,z5,z6])],[(0,[z897,z2,z3,z4,z5,z6]),(0,[z1,z898,z3,z4,z5,z6])]],
   [[(0,[z41,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z5,z526]),(0,[z2,z3,z718,z16,z5,z6]),(0,[z1,z3,z4,z5,z779,z6]),(0,[z1,z899,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z2,z3,z4,z5,z901]),(0,[z1,z2,z3,z4,z27,z773])],[(0,[z1,z2,z138,z4,z5,z526]),(0,[z1,z2,z392,z271,z5,z6]),(0,[z1,z2,z3,z4,z5,z902]),(0,[z1,z37,z401,z62,z5,z6]),(0,[z1,z2,z4,z192,z775,z6])],[(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z414,z2,z156,z4,z5]),(0,[z1,z211,z3,z4,z5,z175]),(0,[z1,z37,z254,z2,z5,z6]),(0,[z1,z2,z3,z45,z844,z6])]],
   [[(0,[z1,z2,z3,z4,z904,z6]),(0,[z1,z2,z3,z4,z905,z6]),(0,[z1,z97,z3,z4,z5,z526]),(0,[z1,z258,z3,z4,z168,z6]),(0,[z116,z2,z3,z204,z4,z5]),(0,[z1,z2,z3,z906,z5,z6]),(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z2,z3,z4,z291,z13]),(0,[z1,z908,z3,z4,z5,z6])],[(0,[z1,z2,z3,z173,z255,z6]),(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z3,z910,z4,z5,z6]),(0,[z1,z3,z4,z5,z911,z6]),(0,[z1,z2,z3,z912,z5,z6]),(0,[z1,z862,z3,z4,z5,z6]),(0,[z1,z2,z3,z294,z168,z6]),(0,[z1,z2,z202,z4,z5,z747])],[(1,[z736,z3,z4,z5,z6]),(0,[z1,z2,z156,z4,z234,z6]),(0,[z1,z2,z3,z4,z5,z913]),(1,[z1,z2,z3,z844,z6])],[(0,[z1,z736,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z102,z2,z3,z5,z12]),(0,[z1,z2,z3,z4,z234,z6]),(0,[z1,z217,z3,z4,z5,z122]),(0,[z1,z2,z3,z915,z5,z6])]],
   [[(0,[z1,z2,z3,z219,z5,z6]),(0,[z1,z2,z4,z5,z6,z747])],[(0,[z155,z258,z3,z4,z5,z175]),(0,[z1,z2,z3,z271,z168,z6]),(0,[z1,z97,z3,z4,z6,z608]),(0,[z1,z37,z2,z464,z5,z6]),(0,[z1,z2,z3,z4,z916,z6])],[(0,[z1,z2,z3,z5,z6,z917]),(0,[z1,z2,z156,z4,z5,z75]),(0,[z155,z2,z3,z294,z5,z175]),(0,[z1,z2,z3,z4,z5,z918]),(0,[z1,z97,z3,z4,z795,z6]),(0,[z1,z82,z3,z4,z5,z122]),(0,[z1,z2,z3,z4,z5,z808])],[(0,[z1,z919,z3,z4,z5,z6]),(0,[z1,z2,z390,z3,z4,z5]),(0,[z1,z2,z920,z4,z5,z6]),(0,[z155,z2,z156,z4,z5,z175]),(1,[z1,z3,z798,z5,z6]),(0,[z1,z2,z4,z815,z5,z6])]],
   [[(0,[z1,z2,z161,z4,z5,z6]),(0,[z1,z2,z921,z4,z5,z6]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z923]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z2,z3,z4,z5,z723])],[(0,[z1,z2,z3,z4,z925,z6]),(0,[z1,z2,z3,z926,z5,z6]),(0,[z1,z2,z927,z4,z5,z6]),(0,[z1,z928,z2,z3,z5,z6]),(0,[z1,z401,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z929]),(0,[z1,z2,z930,z4,z5,z6]),(1,[z1,z3,z4,z795,z6]),(0,[z1,z931,z2,z3,z4,z6]),(0,[z1,z371,z38,z2,z47,z6])],[(0,[z1,z2,z3,z4,z5,z932]),(0,[z1,z2,z3,z4,z5,z933]),(0,[z1,z934,z2,z4,z5,z6]),(0,[z1,z586,z3,z4,z5,z122]),(0,[z1,z254,z2,z3,z4,z935]),(0,[z1,z3,z4,z5,z936,z6])],[(0,[z1,z2,z937,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z414,z2,z202,z4,z5]),(0,[z210,z2,z3,z187,z5,z6]),(0,[z1,z2,z939,z3,z4,z5]),(0,[z1,z940,z3,z4,z5,z6]),(0,[z1,z60,z3,z4,z5,z248]),(0,[z1,z941,z3,z4,z5,z6]),(0,[z1,z942,z3,z4,z5,z6]),(0,[z1,z37,z2,z815,z5,z6])]],
   [[(0,[z1,z2,z202,z156,z4,z5]),(0,[z1,z184,z3,z477,z5,z6])],[(0,[z1,z2,z3,z4,z5,z181]),(0,[z2,z3,z748,z4,z5,z6]),(0,[z1,z286,z3,z4,z50,z6]),(0,[z1,z211,z3,z294,z5,z6]),(0,[z1,z2,z156,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z943]),(0,[z1,z2,z4,z192,z541,z6])],[(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z96,z2,z4,z5,z705])]],
   [[(0,[z1,z2,z945,z3,z4,z5]),(0,[z1,z2,z3,z4,z946,z6]),(1,[z2,z3,z4,z719,z6]),(0,[z1,z3,z4,z5,z6,z947]),(0,[z1,z3,z4,z798,z5,z6]),(0,[z1,z2,z3,z948,z5,z6]),(0,[z1,z949,z3,z4,z5,z6])],[(0,[z1,z2,z3,z950,z5,z6]),(0,[z1,z211,z3,z271,z5,z6]),(0,[z1,z2,z3,z4,z5,z951]),(0,[z1,z2,z3,z4,z58,z6]),(0,[z1,z38,z2,z3,z464,z6])],[(0,[z1,z2,z3,z952,z5,z6]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z400,z2,z3,z4,z13]),(0,[z1,z82,z3,z4,z27,z75])],[(0,[z1,z2,z3,z4,z259,z6]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z210,z2,z3,z718,z5,z6]),(0,[z1,z2,z4,z5,z6,z955]),(0,[z1,z2,z3,z4,z956,z6]),(0,[z1,z401,z3,z4,z5,z957])]],
   [[(0,[z1,z2,z3,z958,z4,z6]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z74,z2,z4,z64,z120]),(0,[z1,z212,z2,z3,z5,z12])],[(0,[z515,z2,z182,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z960]),(0,[z1,z211,z3,z68,z4,z5]),(0,[z1,z69,z699,z4,z5,z6]),(0,[z1,z961,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z962,z6]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z2,z3,z4,z5,z213]),(0,[z1,z2,z3,z4,z5,z195]),(0,[z1,z211,z3,z4,z5,z229]),(0,[z1,z2,z3,z4,z5,z964])],[(0,[z1,z2,z3,z4,z255,z526]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z1,z966,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z785,z12])]],
   [[],[(0,[z1,z373,z129,z4,z5,z6]),(0,[z967,z2,z3,z4,z5,z6]),(0,[z1,z2,z968,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z75])],[(0,[z41,z139,z3,z173,z5,z6]),(0,[z1,z102,z2,z3,z4,z5]),(1,[z2,z3,z4,z5,z726]),(0,[z116,z2,z3,z4,z5,z654]),(0,[z1,z2,z3,z4,z5,z98]),(0,[z1,z97,z3,z4,z49,z169]),(0,[z1,z97,z3,z4,z311,z6])],[(0,[z1,z2,z3,z969,z5,z6]),(0,[z1,z2,z3,z4,z5,z970]),(0,[z1,z2,z3,z4,z5,z726]),(0,[z1,z971,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z27,z169])]],
   [[(0,[z41,z139,z138,z4,z5,z6]),(0,[z397,z42,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z972,z6]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z2,z974,z4,z5,z6]),(0,[z2,z3,z4,z5,z726,z175]),(0,[z1,z2,z3,z68,z684,z5]),(0,[z1,z975,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z976]),(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z2,z3,z4,z5,z142]),(0,[z1,z38,z2,z3,z844,z6]),(0,[z1,z2,z3,z4,z75,z773])],[(0,[z1,z2,z3,z4,z5,z978]),(0,[z155,z2,z392,z4,z5,z175]),(0,[z1,z979,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z5,z6,z981])],[(0,[z1,z2,z3,z982,z5,z6]),(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z391,z102,z2,z3,z16,z5]),(0,[z1,z986,z3,z4,z5,z6]),(0,[z116,z2,z3,z4,z5,z726]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z730,z129,z4,z5,z6]),(0,[z1,z82,z3,z4,z5,z248]),(0,[z1,z2,z20,z815,z5,z6]),(0,[z1,z2,z20,z5,z338,z6])],[(0,[z1,z2,z161,z219,z5,z6]),(0,[z1,z3,z4,z50,z259,z6]),(0,[z1,z3,z4,z988,z5,z6]),(0,[z1,z2,z3,z4,z989,z6]),(0,[z1,z2,z3,z815,z5,z6]),(0,[z1,z2,z3,z4,z5,z241]),(0,[z1,z38,z2,z3,z47,z6])]],
   [[(0,[z42,z736,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z990,z6]),(0,[z1,z3,z4,z5,z723,z122]),(0,[z1,z2,z3,z4,z5,z991])],[(0,[z1,z2,z3,z4,z5,z992]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z1,z995,z2,z3,z4,z6]),(0,[z54,z2,z55,z4,z5,z6]),(0,[z2,z748,z182,z4,z5,z6]),(0,[z1,z996,z3,z4,z5,z6]),(0,[z1,z997,z3,z4,z5,z6]),(0,[z1,z74,z2,z63,z64,z6]),(0,[z1,z327,z2,z192,z5,z6]),(0,[z1,z2,z3,z998,z5,z6])],[(0,[z1,z2,z3,z4,z5,z999])],[(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1,z1001,z3,z4,z5,z6]),(0,[z2,z55,z748,z4,z5,z6]),(0,[z1,z1002,z3,z4,z5,z6]),(0,[z22,z2,z3,z4,z719,z6]),(0,[z157,z2,z3,z4,z23,z6]),(0,[z1,z2,z3,z1003,z5,z6]),(0,[z1,z258,z3,z271,z5,z6]),(0,[z1,z2,z3,z5,z1004,z6]),(0,[z1,z183,z3,z798,z5,z6]),(0,[z1,z82,z3,z4,z5,z6]),(0,[z1,z3,z4,z50,z587,z6]),(0,[z1,z2,z44,z4,z520,z6])]],
   [[(0,[z1,z2,z138,z219,z5,z6]),(0,[z1,z2,z3,z219,z5,z181]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z1,z2,z3,z1006,z5,z6]),(0,[z1,z2,z1007,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z299,z3,z4,z248,z531]),(0,[z1,z74,z2,z4,z775,z6]),(0,[z1,z371,z38,z2,z3,z6])],[(0,[z1,z299,z3,z4,z5,z589]),(0,[z1,z2,z3,z4,z5,z1009])],[(0,[z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z3,z1010,z5,z6]),(0,[z1,z2,z161,z173,z5,z6]),(0,[z1,z414,z2,z3,z4,z5]),(0,[z1,z1011,z3,z4,z5,z6]),(0,[z1,z74,z2,z193,z4,z6])],[(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z3,z4,z50,z5,z526]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z3,z4,z6,z1014]),(1,[z2,z3,z718,z5,z6]),(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z5,z844,z6])]],
   [[(0,[z1,z2,z161,z4,z5,z181]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z2,z3,z718,z5,z6]),(0,[z1,z96,z211,z3,z4,z5]),(0,[z308,z2,z3,z4,z5,z229]),(0,[z1,z37,z254,z2,z62,z6])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z2,z3,z1018,z5,z6]),(0,[z1,z2,z156,z4,z5,z6]),(0,[z1,z69,z70,z4,z5,z6]),(0,[z1,z3,z4,z795,z5,z6]),(0,[z1,z2,z1019,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z1020,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z2,z3,z4,z1022,z6]),(0,[z524,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z2,z3,z1024,z5,z6]),(0,[z1,z37,z292,z62,z5,z6]),(0,[z1,z2,z3,z4,z577,z75])],[(0,[z1,z562,z3,z4,z5,z122]),(0,[z1,z211,z3,z4,z234,z6]),(0,[z1,z2,z3,z4,z5,z1025]),(0,[z1,z2,z3,z4,z6,z1026]),(0,[z1,z2,z3,z1027,z5,z6]),(0,[z1,z443,z3,z4,z5,z248])]],
   [[(0,[z148,z2,z390,z182,z4,z5]),(0,[z1,z99,z3,z4,z50,z6]),(0,[z1,z299,z3,z4,z58,z248]),(0,[z1,z401,z3,z4,z5,z771]),(0,[z1,z37,z2,z553,z5,z6]),(0,[z1,z2,z459,z4,z5,z203])],[(0,[z1,z2,z138,z4,z5,z181]),(0,[z1,z2,z3,z1028,z4,z5]),(0,[z1,z3,z4,z1029,z5,z6]),(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z1031,z3,z4,z5,z6]),(0,[z1,z2,z3,z1032,z5,z6])],[(0,[z1,z2,z1033,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z773])],[(0,[z1,z2,z3,z4,z1034,z6]),(0,[z1,z2,z3,z1035,z5,z6]),(0,[z1,z602,z2,z3,z4,z13]),(0,[z1,z211,z3,z4,z5,z75]),(0,[z1,z314,z3,z4,z5,z248])]],
   [[(0,[z41,z139,z3,z4,z5,z526]),(0,[z1,z2,z202,z4,z5,z206]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z155,z211,z3,z4,z5,z175]),(0,[z155,z350,z2,z3,z4,z5]),(0,[z1,z37,z2,z193,z5,z6]),(0,[z1,z2,z44,z4,z775,z6])],[(0,[z1,z2,z3,z4,z1037,z6]),(0,[z1,z2,z3,z173,z259,z6]),(0,[z1,z3,z4,z50,z316,z6]),(0,[z1,z299,z3,z4,z58,z6]),(0,[z1,z1038,z3,z4,z5,z6]),(0,[z1,z2,z3,z46,z844,z6])],[(0,[z1,z3,z798,z91,z5,z6]),(0,[z1,z2,z3,z4,z844,z6])],[(0,[z1,z2,z138,z4,z259,z6]),(0,[z1,z2,z3,z4,z5,z1039]),(0,[z351,z2,z3,z4,z719,z6]),(0,[z1,z2,z3,z4,z58,z169]),(0,[z1,z371,z38,z2,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z1040,z6]),(0,[z1,z2,z3,z4,z1041,z5]),(0,[z1,z3,z4,z5,z1042,z6]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z107,z2,z3,z4,z773])],[(0,[z1,z97,z3,z4,z259,z6]),(0,[z1,z2,z3,z4,z5,z1043]),(0,[z22,z3,z4,z335,z23,z6]),(0,[z1,z2,z1044,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1045])],[(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z211,z3,z4,z5,z13]),(0,[z1,z96,z2,z156,z4,z5]),(0,[z1,z2,z3,z68,z271,z5]),(0,[z1,z3,z4,z58,z6,z122]),(0,[z1,z616,z3,z4,z5,z122]),(0,[z1,z3,z4,z5,z1047,z6])],[(0,[z1,z2,z3,z4,z6,z1048]),(0,[z1,z1049,z3,z4,z5,z6]),(0,[z1,z2,z1050,z4,z5,z6]),(0,[z1,z252,z3,z4,z27,z6]),(0,[z116,z2,z321,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z184,z3,z798,z5,z6]),(0,[z1,z3,z4,z5,z169,z122]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z3,z45,z46,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 558) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 558).take 483) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1041)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [558, 483] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 86).take 42).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [86, 42] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_43474

theorem PEqualNP.Outside.L_meta_43474 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272613504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272613504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43474.solve