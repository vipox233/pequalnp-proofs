import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38901

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x04000a471822a798#64 ++ 0x020005238c1153cc#64 ++ 0xfb813ecf3a67ef99#64 ++ 0xfdc09f679d33f7cc#64 : BitVec 256),
   (0x88025851408980aa#64 ++ 0x44012c28a044c055#64 ++ 0xf786d971c59991ff#64 ++ 0xfbc36cb8e2ccc8ff#64 : BitVec 256),
   (0x5038a180ae161a15#64 ++ 0x281c50c0570b0d0a#64 ++ 0xef78e181fe1e1e1f#64 ++ 0x77bc70c0ff0f0f0f#64 : BitVec 256),
   (0x605d01aa07601d41#64 ++ 0xb02e80d503b00ea0#64 ++ 0xdfff01fe07e01fe0#64 ++ 0xefff80ff03f00ff0#64 : BitVec 256),
   (0x806ff40007dd4001#64 ++ 0xc037fa0003eea000#64 ++ 0xbe7ffe0007ffe001#64 ++ 0xdf3fff0003fff000#64 : BitVec 256),
   (0x00f7fffdf0000000#64 ++ 0x007bfffef8000000#64 ++ 0x7efffffff8000000#64 ++ 0x3f7ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffff8000000 0x3f7ffffffc000000

def z1 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb813ecf3a67ef99 0xfdc09f679d33f7cc

def z2 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xef78e181fe1e1e1f 0x77bc70c0ff0f0f0f

def z3 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfff01fe07e01fe0 0xefff80ff03f00ff0

def z4 : W := mkw 0x60df5fff57601d41 0xb06fafffabb00ea0 0xdfff1ffe07e01fe0 0xefff8fff03f00ff0

def z5 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbe7ffe0007ffe001 0xdf3fff0003fff000

def z6 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xf786d971c59991ff 0xfbc36cb8e2ccc8ff

def z7 : W := mkw 0xd00800000fdf5a15 0xe804000007efad0a 0x8100000007fffe1f 0xc080000003ffff0f

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xe700c101c418101f 0x73806080e20c080f

def z9 : W := mkw 0x005759f940000000 0x002bacfca0000000 0x7effd9ffc0000000 0x3f7fecffe0000000

def z10 : W := mkw 0x8002500000890000 0x4001280000448000 0xb606d80005998001 0xdb036c0002ccc000

def z11 : W := mkw 0x886ffc5147ddc0ab 0xc437fe28a3eee055 0xffffff71c7fff1ff 0xffffffb8e3fff8ff

def z12 : W := mkw 0x88025010408980aa 0x440128082044c055 0x8506c130c59991ff 0xc283609862ccc8ff

def z13 : W := mkw 0x04f7fffff822a798 0x027bfffffc1153cc 0xfffffffffa67ef99 0xfffffffffd33f7cc

def z14 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfffffffffd9991ff 0xfffffffffeccc8ff

def z15 : W := mkw 0x6008000207601d41 0xb004000103b00ea0 0x8100000007e01fe0 0xc080000003f00ff0

def z16 : W := mkw 0x80fffffdf7dd4001 0xc07ffffefbeea000 0xfeffffffffffe001 0xff7ffffffffff000

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0xba013e000267e001 0xdd009f000133f000

def z18 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x0879268e38000000 0x043c93471c000000

def z19 : W := mkw 0xe85f59fb47e99deb 0xf42facfda3f4cef5 0xffffd9ffc7f99fff 0xffffecffe3fccfff

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0xa600c00004180001 0x53006000020c0000

def z21 : W := mkw 0xe07ff5a807dd5841 0xf03ffad403eeac20 0x047ec13005981060 0x023f609802cc0830

def z22 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x10861870018181e0 0x88430c3800c0c0f0

def z23 : W := mkw 0x8802501040890022 0x4401280820448011 0x0406c130c5981066 0x0203609862cc0833

def z24 : W := mkw 0x8c025a5758aba7ba 0x46012d2bac55d3dd 0xff87ffffffffffff 0xffc3ffffffffffff

def z25 : W := mkw 0x1020a000a8160214 0x08105000540b010a 0x2000e001f81e001f 0x10007000fc0f000f

def z26 : W := mkw 0x04000a471020a588 0x02000523881052c4 0xba813e4e0267e181 0xdd409f270133f0c0

def z27 : W := mkw 0x8047540001c94000 0xc023aa0000e4a000 0xb607de0005f9e001 0xdb03ef0002fcf000

def z28 : W := mkw 0x0028a00006140001 0x00145000030a0000 0xbe79fe00067fe001 0xdf3cff00033ff000

def z29 : W := mkw 0x00f7f5b8e0000000 0x007bfadc70000000 0x6e7ee1b1f8000000 0x373f70d8fc000000

def z30 : W := mkw 0x00825e5550000000 0x00412f2aa8000000 0x00001e0000000000 0x00000f0000000000

def z31 : W := mkw 0x50baffd5fe161a15 0x285d7feaff0b0d0a 0xef78ff81fe1e1e1f 0x77bc7fc0ff0f0f0f

def z32 : W := mkw 0x2045002a01600540 0x9022801500b002a0 0x0001000e00600000 0x0000800700300000

def z33 : W := mkw 0x507da580af565a15 0xa83ed2c057ab2d0a 0x087926803a666e00 0x043c93401d333700

def z34 : W := mkw 0x50fffffdfe161a15 0x287ffffeff0b0d0a 0xfffffffffe1e1e1f 0x7fffffffff0f0f0f

def z35 : W := mkw 0x88c75e7d508980aa 0x4463af3ea844c055 0x10871e7e018181e0 0x88438f3f00c0c0f0

def z36 : W := mkw 0x04f7fffdf802a298 0x027bfffefc01514c 0x7efffffff807e019 0x3f7ffffffc03f00c

def z37 : W := mkw 0x601001aa00201d40 0x300800d500100ea0 0xd78601fe05801fe0 0xebc300ff02c00ff0

def z38 : W := mkw 0x00900bfdf0000000 0x004805fef8000000 0x408001fff8000000 0x204000fffc000000

def z39 : W := mkw 0x00c75e7d50000000 0x0063af3ea8000000 0x10871e7e00000000 0x08438f3f00000000

def z40 : W := mkw 0x00a2fe55f0000000 0x00517f2af8000000 0x2000fe01f8000000 0x10007f00fc000000

def z41 : W := mkw 0x707da1aaaf761f55 0xb83ed0d557bb0faa 0x0879208e3a660e00 0x043c90471d330700

def z42 : W := mkw 0x8022f400009d4000 0x40117a00004ea000 0xba01fe00027fe001 0xdd00ff00013ff000

def z43 : W := mkw 0x8067f400009d4000 0x4033fa00004ea000 0x3e7ffe00001fe001 0x1f3fff00000ff000

def z44 : W := mkw 0x601001aa00201d40 0x300800d500100ea0 0x418001fe00001fe0 0x20c000ff00000ff0

def z45 : W := mkw 0x00a2f410e0000000 0x00517a0870000000 0x0000c000c0000000 0x0000600060000000

def z46 : W := mkw 0x4018018006001801 0x200c00c003000c00 0xcf78018006001e00 0x67bc00c003000f00

def z47 : W := mkw 0x8802501040890022 0x4401280820448011 0xb606d930c5999067 0xdb036c9862ccc833

def z48 : W := mkw 0x00b0abfdf0000000 0x005855fef8000000 0x6ef8e1fff8000000 0x377c70fffc000000

def z49 : W := mkw 0x8047540001c94000 0xc023aa0000e4a000 0x10071e0001e1e000 0x88038f0000f0f000

def z50 : W := mkw 0x04a2fe55f802a298 0x02517f2afc01514c 0x2000fe01f807e019 0x10007f00fc03f00c

def z51 : W := mkw 0x0020a00000000000 0x0010500000000000 0x2e78e00000000000 0x173c700000000000

def z52 : W := mkw 0x0000084100008088 0x0000042080004044 0x2000180100018019 0x10000c008000c00c

def z53 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdbf900ce02600f80 0xedfc8067013007c0

def z54 : W := mkw 0x8cf7fffff8aba7ba 0x467bfffffc55d3dd 0xffffffffffffffff 0xffffffffffffffff

def z55 : W := mkw 0x5438abc7be36bf9d 0x2a1c55e3df1b5fce 0xfff9ffcffe7fff9f 0xfffcffe7ff3fffcf

def z56 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff87ff71c7fff1ff 0xffc3ffb8e3fff8ff

def z57 : W := mkw 0x40fffffdf6001801 0x207ffffefb000c00 0xfffffffffe001e00 0x7fffffffff000f00

def z58 : W := mkw 0x5438abc7be36bf9d 0x2a1c55e3df1b5fce 0xfbf93ecf3a67ef99 0xfdfc9f679d33f7cc

def z59 : W := mkw 0x2045002a01600540 0x9022801500b002a0 0xd787017e05e011e0 0xebc380bf02f008f0

def z60 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x48f927fff8000000 0x247c93fffc000000

def z61 : W := mkw 0x0008000007400001 0x8004000003a00000 0x8000000007e00000 0xc000000003f00000

def z62 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x897820803e1e1e1f 0x44bc10401f0f0f0f

def z63 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x8979008e07e01fe0 0xc4bc804703f00ff0

def z64 : W := mkw 0x00f7fdf9e0000000 0x007bfefcf0000000 0x76fed971c0000000 0x3b7f6cb8e0000000

def z65 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0x0879260002666000 0x043c930001333000

def z66 : W := mkw 0x08000851400080aa 0x04000428a0004055 0x41800171c00011fe 0x20c000b8e00008ff

def z67 : W := mkw 0x0400020618222710 0x020001030c111388 0x0801268e3a666e00 0x040093471d333700

def z68 : W := mkw 0x8067f40000890000 0x4033fa0000448000 0xbe7ffe0005998001 0xdf3fff0002ccc000

def z69 : W := mkw 0x004d000007400001 0x8026800003a00000 0x9e7f000007e00000 0xcf3f800003f00000

def z70 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x418000cf38000f98 0x20c000679c0007cc

def z71 : W := mkw 0x50100180a8021a14 0x280800c054010d0a 0x41000181f8001e1e 0x208000c0fc000f0f

def z72 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x087820803a060e00 0x043c10401d030700

def z73 : W := mkw 0xe07ff5aa07fd5d41 0xf03ffad503feaea0 0xfffffffe07ffffe1 0xffffffff03fffff0

def z74 : W := mkw 0x00f7f5b8e0000000 0x007bfadc70000000 0x047ec130c0000000 0x023f609860000000

def z75 : W := mkw 0x88000000008980aa 0x440000000044c055 0xd7860170059991ff 0xebc300b802ccc8ff

def z76 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x18ff3efe38000000 0x0c7f9f7f1c000000

def z77 : W := mkw 0x00000a4510000000 0x0000052288000000 0x408000cf38000000 0x204000679c000000

def z78 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfefffffffa67e001 0xff7ffffffd33f000

def z79 : W := mkw 0x8822fc51409dc0aa 0x44117e28a04ee055 0xf786ff71c59ff1ff 0xfbc37fb8e2cff8ff

def z80 : W := mkw 0x00000a4510000000 0x0000052288000000 0x7a813ecf38000000 0x3d409f679c000000

def z81 : W := mkw 0x60fffffff7601d41 0xb07ffffffbb00ea0 0xffffffffffe01fe0 0xfffffffffff00ff0

def z82 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x047ec00005980000 0x023f600002cc0000

def z83 : W := mkw 0x60fda7aeb7601d41 0xb07ed3d75bb00ea0 0x0879268e3a600e00 0x043c93471d300700

def z84 : W := mkw 0x5038a180a6141805 0x281c50c0530a0c02 0x0478c100c4181006 0x023c6080620c0803

def z85 : W := mkw 0xd07ff580a7dd5805 0xe83ffac053eeac02 0xbe7fff00c7fff007 0xdf3fff8063fff803

def z86 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xb606d801c599801f 0xdb036c00e2ccc00f

def z87 : W := mkw 0x840800020fffe799 0xc204000107fff3cc 0x8100000007ffef99 0xc080000003fff7cc

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0xd7860170058011e0 0xebc300b802c008f0

def z89 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x28013e8f3a67ee19 0x14009f479d33f70c

def z90 : W := mkw 0x1420aa47b836a79c 0x0a105523dc1b53ce 0xfb81fecffa7fef9f 0xfdc0ff67fd3ff7cf

def z91 : W := mkw 0xe06ff40207fd5d41 0xf037fa0103feaea0 0xbf7ffe0007ffffe1 0xdfbfff0003fffff0

def z92 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xff79ff81fe7ffe1f 0xffbcffc0ff3fff0f

def z93 : W := mkw 0x2045002a01600540 0x9022801500b002a0 0x1087007e01e001e0 0x8843803f00f000f0

def z94 : W := mkw 0x707da1aaaf761f55 0xb83ed0d557bb0faa 0xffffe1fffffe1fff 0xfffff0ffffff0fff

def z95 : W := mkw 0x0028a00006140001 0x00145000030a0000 0xae78e000061e0001 0x573c7000030f0000

def z96 : W := mkw 0xd07ff580afdf5a15 0xe83ffac057efad0a 0xff7fff81fffffe1f 0xffbfffc0ffffff0f

def z97 : W := mkw 0x04000a471020a588 0x02000523881052c4 0x10811e4e0061e180 0x88408f270030f0c0

def z98 : W := mkw 0x00c75e7d50000000 0x0063af3ea8000000 0x7687df7fc0000000 0x3b43efbfe0000000

def z99 : W := mkw 0x0067f40000000000 0x0033fa0000000000 0x047ec00000000000 0x023f600000000000

def z100 : W := mkw 0x0400000208222710 0x0200000104111388 0x0000000002666e00 0x0000000001333700

def z101 : W := mkw 0x6008000207601d41 0xb004000103b00ea0 0x0000000002600e00 0x0000000001300700

def z102 : W := mkw 0x8022f400009d4000 0x40117a00004ea000 0x2000fe00001fe001 0x10007f00000ff000

def z103 : W := mkw 0x2045002801400040 0x9022801400a00020 0x0006003001800060 0x0003001800c00030

def z104 : W := mkw 0x8c02585348aba7ba 0x46012c29a455d3dd 0xf786d971c7ffffff 0xfbc36cb8e3ffffff

def z105 : W := mkw 0x04c75e7f5822a798 0x0263af3fac1153cc 0xfb873eff3a67ef99 0xfdc39f7f9d33f7cc

def z106 : W := mkw 0x4038a180a6001801 0x201c50c053000c00 0xef78e181fe001e00 0x77bc70c0ff000f00

def z107 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x187f3e0003e7e000 0x8c3f9f0001f3f000

def z108 : W := mkw 0x040000020822a798 0x02000001041153cc 0x0100000000000f98 0x00800000000007cc

def z109 : W := mkw 0x88000000008980aa 0x440000000044c055 0x81000000059991ff 0xc080000002ccc8ff

def z110 : W := mkw 0x04000a451802a298 0x020005228c01514c 0x20003e013807e019 0x10001f009c03f00c

def z111 : W := mkw 0xe008000207fd5d41 0xf004000103feaea0 0x8100000007ffffe1 0xc080000003fffff0

def z112 : W := mkw 0x0000084100008088 0x0000042080004044 0xfb813e410267e199 0xfdc09f208133f0cc

def z113 : W := mkw 0x0030a180a0000000 0x001850c050000000 0x6e78e181f8000000 0x373c70c0fc000000

def z114 : W := mkw 0x0038a180a6140001 0x001c50c0530a0000 0xee78e181fe1e0001 0x773c70c0ff0f0000

def z115 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0xba793e000267e001 0xdd3c9f000133f000

def z116 : W := mkw 0xd83af9d1ee9f9abf 0x6c1d7ce8f74fcd5f 0xfffef9f1ff9f9fff 0xffff7cf8ffcfcfff

def z117 : W := mkw 0x50fda7acbe161a15 0x287ed3d65f0b0d0a 0xef79e78ffe1e1e1f 0x77bcf3c7ff0f0f0f

def z118 : W := mkw 0x806ff40207fd4501 0xc037fa0103fea280 0xfffffece07ffef81 0xffffff6703fff7c0

def z119 : W := mkw 0x64100bef1822bfd8 0x320805f78c115fec 0x418001ff38001ff8 0x20c000ff9c000ffc

def z120 : W := mkw 0x645d0bef1f62bfd9 0xb22e85f78fb15fec 0xffff3fff3fe7fff9 0xffff9fff9ff3fffc

def z121 : W := mkw 0x500800000e161a15 0x28040000070b0d0a 0xeb0020813e1e1e1f 0x758010409f0f0f0f

def z122 : W := mkw 0x7038a182af761f55 0xb81c50c157bb0faa 0xef78e181fffe1fff 0xf7bc70c0ffff0fff

def z123 : W := mkw 0x605d01a807401841 0xb02e80d403a00c20 0xcf7e01b007801e60 0x67bf00d803c00f30

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a01000002600000 0xcd00800001300000

def z125 : W := mkw 0x605d01a807401841 0xb02e80d403a00c20 0xd7fe0170058011e0 0xebff00b802c008f0

def z126 : W := mkw 0x04000a471020a588 0x02000523881052c4 0xdb811ece0261ef80 0xedc08f670130f7c0

def z127 : W := mkw 0x0077f580a0000000 0x003bfac050000000 0x7e7fff81f8000000 0x3f3fffc0fc000000

def z128 : W := mkw 0x04000a451802a298 0x020005228c01514c 0x7a813ecf3807e019 0x3d409f679c03f00c

def z129 : W := mkw 0x0030a180a0000000 0x001850c050000000 0xef78e181fc18101f 0x77bc70c0fe0c080f

def z130 : W := mkw 0x0045040001404000 0x8022820000a02000 0x0001060000606000 0x0000830000303000

def z131 : W := mkw 0x0067f40000000000 0x0033fa0000000000 0xbe7ffe000267e001 0xdf3fff000133f000

def z132 : W := mkw 0x040000020822a798 0x02000001041153cc 0x810000000267ef99 0xc08000000133f7cc

def z133 : W := mkw 0x00f5afedb0000000 0x007ad7f6d8000000 0x7af93ecf38000000 0x3d7c9f679c000000

def z134 : W := mkw 0x645d03ae1f623f51 0xb22e81d70fb11fa8 0xdfff27fe3fe67fe0 0xefff93ff1ff33ff0

def z135 : W := mkw 0x886ff41047dd4023 0xc437fa0823eea011 0xbe7fff30c7fff067 0xdf3fff9863fff833

def z136 : W := mkw 0xe07ff5aa07fd5d41 0xf03ffad503feaea0 0xbe7ffe8e07ffee01 0xdf3fff4703fff700

def z137 : W := mkw 0xec5f5bff5febbffb 0xf62fadffaff5dffd 0xffffffffffffffff 0xffffffffffffffff

def z138 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x4586c171c59811fe 0x22c360b8e2cc08ff

def z139 : W := mkw 0x9822f851e89f82be 0x4c117c28f44fc15f 0x2000f801f81f801f 0x10007c00fc0fc00f

def z140 : W := mkw 0x802af40007dd4001 0xc0157a0003eea000 0xa000fe0007ffe001 0xd0007f0003fff000

def z141 : W := mkw 0x8008000007dd4001 0xc004000003eea000 0x8000000007ffe001 0xc000000003fff000

def z142 : W := mkw 0x503af9d1ee161a15 0x281d7ce8f70b0d0a 0xfffef9f1fe1e1e1f 0x7fff7cf8ff0f0f0f

def z143 : W := mkw 0x0002585140000000 0x00012c28a0000000 0x7686d971c0000000 0x3b436cb8e0000000

def z144 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x2478e101fc1e101f 0x123c7080fe0f080f

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0x10860070018001e0 0x8843003800c000f0

def z146 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x2879fe00027fe001 0x143cff00013ff000

def z147 : W := mkw 0x88025a55508980aa 0x44012d2aa844c055 0xff87fffffd9991ff 0xffc3fffffeccc8ff

def z148 : W := mkw 0x0067f40000000000 0x0033fa0000000000 0x3e7ffe0000000000 0x1f3fff0000000000

def z149 : W := mkw 0x88025000008980aa 0x440128000044c055 0xb706d800059991ff 0xdb836c0002ccc8ff

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z151 : W := mkw 0x886ff40007ddc0ab 0xc437fa0003eee055 0xbf7ffe0007fff1ff 0xdfbfff0003fff8ff

def z152 : W := mkw 0x4018018006001801 0x200c00c003000c00 0x0478010004001000 0x023c008002000800

def z153 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x247efe00059fe001 0x123f7f0002cff000

def z154 : W := mkw 0xe47fffef1fffffd9 0xf23ffff78fffffec 0xffffffff3ffffff9 0xffffffff9ffffffc

def z155 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x0879008e02600e00 0x043c804701300700

def z156 : W := mkw 0x500800000e161a15 0x28040000070b0d0a 0x81000000061e1e1f 0x40800000030f0f0f

def z157 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x2406d931c599907f 0x12036c98e2ccc83f

def z158 : W := mkw 0x0000084100008088 0x0000042080004044 0xf7861971058191f9 0xfbc30cb882c0c8fc

def z159 : W := mkw 0x84025a4718aba798 0x42012d238c55d3cc 0xff87fecf3fffef99 0xffc3ff679ffff7cc

def z160 : W := mkw 0x005501a800000000 0x002a80d400000000 0x0879008e00000000 0x043c804700000000

def z161 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xae7ee000079e0001 0x573f700003cf0000

def z162 : W := mkw 0x50f7fffdf8021a14 0x287bfffefc010d0a 0x7ffffffff8001e1e 0x3ffffffffc000f0f

def z163 : W := mkw 0x0002501040000000 0x0001280820000000 0x0406c130c0000000 0x0203609860000000

def z164 : W := mkw 0x806ffc5147dd4001 0xc037fe28a3eea000 0xfeffff71c7ffe001 0xff7fffb8e3fff000

def z165 : W := mkw 0x00f7fffdf8020210 0x007bfffefc010108 0xfffffffffa060e19 0x7ffffffffd03070c

def z166 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffffc1ffc7f81fff 0xffffe0ffe3fc0fff

def z167 : W := mkw 0x04000a451802a298 0x020005228c01514c 0xf3803e413807e199 0xf9c01f209c03f0cc

def z168 : W := mkw 0x005501a800000000 0x002a80d400000000 0x5eff01fe00000000 0x2f7f80ff00000000

def z169 : W := mkw 0x08900bfdf00080aa 0x044805fef8004055 0x418001fff80011fe 0x20c000fffc0008ff

def z170 : W := mkw 0x605d01a807401841 0xb02e80d403a00c20 0x047e013005801060 0x023f009802c00830

def z171 : W := mkw 0x08000851400080aa 0x04000428a0004055 0xf3801971c00191ff 0xf9c00cb8e000c8ff

def z172 : W := mkw 0xd80800000e9f9abf 0x6c040000074fcd5f 0x81000000079f9fff 0xc080000003cfcfff

def z173 : W := mkw 0x8002500000890000 0x4001280000448000 0x2000d80000198001 0x10006c00000cc000

def z174 : W := mkw 0x005501aa00200500 0x002a80d500100280 0xdfff01fe02600f80 0xefff80ff013007c0

def z175 : W := mkw 0x040000020020a588 0x02000001001052c4 0x000000000061e180 0x800000000030f0c0

def z176 : W := mkw 0xe8fffffff7e99deb 0xf47ffffffbf4cef5 0xfffffffffff99fff 0xfffffffffffccfff

def z177 : W := mkw 0x0400020618222710 0x020001030c111388 0x0000008e38000e00 0x000000471c000700

def z178 : W := mkw 0x10f7fffdf8160214 0x087bfffefc0b010a 0x7efffffff81e001f 0x3f7ffffffc0f000f

def z179 : W := mkw 0x8808000007ddc0ab 0xc404000003eee055 0x8100000007fff1ff 0xc080000003fff8ff

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x6a00208138000000 0x350010409c000000

def z181 : W := mkw 0x8022f400009d4000 0x40117a00004ea000 0xb606fe00059fe001 0xdb037f0002cff000

def z182 : W := mkw 0x0067fc5140000000 0x0033fe28a0000000 0x7effff71c0000000 0x3f7fffb8e0000000

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x20003e000007e001 0x10001f000003f000

def z184 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x0000180000018000 0x00000c000000c000

def z185 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7efffffff819801f 0x3f7ffffffc0cc00f

def z186 : W := mkw 0xe80a585347e99deb 0xf4052c29a3f4cef5 0xf786d971c7f99fff 0xfbc36cb8e3fccfff

def z187 : W := mkw 0x009001b8e0000000 0x004800dc70000000 0x00000130c0000000 0x0000009860000000

def z188 : W := mkw 0x88000000008980aa 0x440000000044c055 0x00000000018181e0 0x8000000000c0c0f0

def z189 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x14ff017e05e011e0 0x8a7f80bf02f008f0

def z190 : W := mkw 0x0020a40000144000 0x00105200000a2000 0x0000260000066000 0x0000130000033000

def z191 : W := mkw 0x70ffffffff761f55 0xb87fffffffbb0faa 0xfffffffffffe1fff 0xffffffffffff0fff

def z192 : W := mkw 0x00000a4510000000 0x0000052288000000 0xfa813ecf3a67e001 0xfd409f679d33f000

def z193 : W := mkw 0x04000a471020a588 0x02000523881052c4 0x0080004e00000180 0x00400027000000c0

def z194 : W := mkw 0x846ffe471fffe799 0xc237ff238ffff3cc 0xfffffecf3fffef99 0xffffff679ffff7cc

def z195 : W := mkw 0x507da180af561a15 0xa83ed0c057ab0d0a 0xff7fe181fffe1e1f 0xffbff0c0ffff0f0f

def z196 : W := mkw 0x1028a000ae160215 0x08145000570b010a 0xae78e001fe1e001f 0x573c7000ff0f000f

def z197 : W := mkw 0x20f7fffff1600540 0x907bfffff8b002a0 0x7efffffff9e001e0 0xbf7ffffffcf000f0

def z198 : W := mkw 0x80f7fffdf09d4000 0x407bfffef84ea000 0x7efffffff81fe001 0x3f7ffffffc0ff000

def z199 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x2000d801c019801f 0x10006c00e00cc00f

def z200 : W := mkw 0x884f585147c980ab 0xc427ac28a3e4c055 0xffffd971c7f991ff 0xffffecb8e3fcc8ff

def z201 : W := mkw 0x405d01a806001801 0x202e80d403000c00 0xdfff01fe06001e00 0x6fff80ff03000f00

def z202 : W := mkw 0x8422fe45189fe298 0x42117f228c4ff14c 0x2000fe01381fe019 0x10007f009c0ff00c

def z203 : W := mkw 0x08f7fffdf00080aa 0x047bfffef8004055 0x7ffffffff80011fe 0x3ffffffffc0008ff

def z204 : W := mkw 0x0000000000008088 0x0000000000004044 0x8100000000018199 0xc08000000000c0cc

def z205 : W := mkw 0x50fda7acbe161a15 0x287ed3d65f0b0d0a 0x0879268e3a060e00 0x043c93471d030700

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0x81000000058011e0 0xc080000002c008f0

def z207 : W := mkw 0x0000084100000000 0x0000042080000000 0x7280184100000000 0x39400c2080000000

def z208 : W := mkw 0x00c7543840000000 0x0063aa1c20000000 0x0006003000000000 0x0003001800000000

def z209 : W := mkw 0x64080a471f62bfd9 0xb20405238fb15fec 0xfb813ecf3fe7fff9 0xfdc09f679ff3fffc

def z210 : W := mkw 0x88a2fe55f08980aa 0x44517f2af844c055 0x2000fe01f819801f 0x10007f00fc0cc00f

def z211 : W := mkw 0x00f5a5a8a0000000 0x007ad2d450000000 0x0078000000000000 0x003c000000000000

def z212 : W := mkw 0x707da1aaaf761f55 0xb83ed0d557bb0faa 0xef79e18ffe7e1e1f 0x77bcf0c7ff3f0f0f

def z213 : W := mkw 0x80000000009d4000 0x40000000004ea000 0x00000000001fe001 0x00000000000ff000

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x41000101c000101e 0x20800080e000080f

def z215 : W := mkw 0x5028a000ae161a15 0x28145000570b0d0a 0xa100e001fe1e1e1f 0x50807000ff0f0f0f

def z216 : W := mkw 0x540800020e36bf9d 0x2a040001071b5fce 0x81000000067fff9f 0xc0800000033fffcf

def z217 : W := mkw 0x8002540000894000 0x40012a000044a000 0x00001e000001e000 0x00000f000000f000

def z218 : W := mkw 0x4008000006001801 0x2004000003000c00 0x8100000006001e00 0x4080000003000f00

def z219 : W := mkw 0x1030a180a8160214 0x081850c0540b010a 0x6e78e181f81e001f 0x373c70c0fc0f000f

def z220 : W := mkw 0x8002500000890000 0x4001280000448000 0xf706d901c599901f 0xfb836c80e2ccc80f

def z221 : W := mkw 0x0030abc5b0000000 0x001855e2d8000000 0x7ef9ffcff8000000 0x3f7cffe7fc000000

def z222 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x0c7fe7bef8000000 0x063ff3df7c000000

def z223 : W := mkw 0x0000084100008088 0x0000042080004044 0xf380184100018199 0xf9c00c208000c0cc

def z224 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0xfffffffff8018199 0xfffffffffc00c0cc

def z225 : W := mkw 0x006da00007540001 0x8036d00003aa0000 0xbe7fe00007fe0001 0xdf3ff00003ff0000

def z226 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xffffff7007fff1e1 0xffffffb803fff8f0

def z227 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0xfefffffffd998001 0xff7ffffffeccc000

def z228 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x49782181fa061e1e 0x24bc10c0fd030f0f

def z229 : W := mkw 0x88c75e7d508980aa 0x4463af3ea844c055 0xf787df7fc59991ff 0xfbc3efbfe2ccc8ff

def z230 : W := mkw 0xd06ff4000fdf5a15 0xe837fa0007efad0a 0xbf7ffe0007fffe1f 0xdfbfff0003ffff0f

def z231 : W := mkw 0x0000000008020210 0x0000000004010108 0xeb0020813a060e19 0x758010409d03070c

def z232 : W := mkw 0xa06ff42a07fd4541 0xd037fa1503fea2a0 0xbefffe7e07ffe1e1 0xdf7fff3f03fff0f0

def z233 : W := mkw 0x0000084300208588 0x00000421801042c4 0xfb8118cf02618f99 0xfdc08c678130c7cc

def z234 : W := mkw 0x645d0bef1f62bfd9 0xb22e85f78fb15fec 0xfbf93ecf3a67ef99 0xfdfc9f679d33f7cc

def z235 : W := mkw 0x006ff40007400001 0x8037fa0003a00000 0xbe7ffe0007e00000 0xdf3fff0003f00000

def z236 : W := mkw 0xd83af9d1e69d98af 0x6c1d7ce8f34ecc57 0xf7fed971c59991ff 0xfbff6cb8e2ccc8ff

def z237 : W := mkw 0x8802585340a985aa 0x44012c29a054c2d5 0xff87d9ffc7f99fff 0xffc3ecffe3fccfff

def z238 : W := mkw 0x846ffe451fdfe299 0xc237ff228feff14c 0xbe7ffe013fffe019 0xdf3fff009ffff00c

def z239 : W := mkw 0x8002500000890000 0x4001280000448000 0x0406c00005980000 0x0203600002cc0000

def z240 : W := mkw 0x84475e4719ebe798 0xc223af238cf5f3cc 0xfb873ecf3be7ef99 0xfdc39f679df3f7cc

def z241 : W := mkw 0x6008000207601d41 0xb004000103b00ea0 0xdb8100ce07e01fe0 0xedc0806703f00ff0

def z242 : W := mkw 0x00c5062c10000000 0x0062831608000000 0x0001060e00000000 0x0000830700000000

def z243 : W := mkw 0x5030a180a8161a14 0x281850c0540b0d0a 0x6100e181f81e1e1f 0x308070c0fc0f0f0f

def z244 : W := mkw 0x64ffffffff62bfd9 0xb27fffffffb15fec 0xffffffffffe7fff9 0xfffffffffff3fffc

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0xf786c171c59811ff 0xfbc360b8e2cc08ff

def z246 : W := mkw 0x0010018000000000 0x000800c000000000 0x4e78018000000000 0x273c00c000000000

def z247 : W := mkw 0x04550bef1822a798 0x022a85f78c1153cc 0xffff3fff3a67ef99 0xffff9fff9d33f7cc

def z248 : W := mkw 0x0400020610202500 0x0200010308101280 0x0001060e00606000 0x0000830700303000

def z249 : W := mkw 0x60fffffdf7401841 0xb07ffffefba00c20 0x7efffffffd801060 0x3f7ffffffec00830

def z250 : W := mkw 0x806ffc4107ddc089 0xc037fe2083eee044 0xfffffe4107ffe199 0xffffff2083fff0cc

def z251 : W := mkw 0x405d018007401801 0xa02e80c003a00c00 0xdf7f018007e01e00 0xefbf80c003f00f00

def z252 : W := mkw 0x0430abc7b822a798 0x021855e3dc1153cc 0xfff9ffcffa67ef99 0xfffcffe7fd33f7cc

def z253 : W := mkw 0x001001a800000000 0x000800d400000000 0x408001fe00000000 0x204000ff00000000

def z254 : W := mkw 0x009003acb0000000 0x004801d658000000 0x0000008e38000000 0x000000471c000000

def z255 : W := mkw 0x08000851400080aa 0x04000428a0004055 0xe780c171c41811ff 0x73c060b8e20c08ff

def z256 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xdb8100cf3a600f98 0xedc080679d3007cc

def z257 : W := mkw 0x50fffffdfe161a15 0x287ffffeff0b0d0a 0x7efffffffa060e00 0x3f7ffffffd030700

def z258 : W := mkw 0x88000000008980aa 0x440000000044c055 0x000000000019801f 0x00000000000cc00f

def z259 : W := mkw 0x88925bfdf08980aa 0x44492dfef844c055 0xf786d9fffd9991ff 0xfbc36cfffeccc8ff

def z260 : W := mkw 0x8800000000890022 0x4400000000448011 0x0000000005981066 0x0000000002cc0833

def z261 : W := mkw 0x8c025a5750a9a5aa 0x46012d2ba854d2d5 0xf787df7fc5f9f1ff 0xfbc3efbfe2fcf8ff

def z262 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffff3ffe07e7ffe1 0xffff9fff03f3fff0

def z263 : W := mkw 0x804d000007dd4001 0xc026800003eea000 0x9e7f000007ffe001 0xcf3f800003fff000

def z264 : W := mkw 0xd838a180ae9f9abf 0x6c1c50c0574fcd5f 0xef78e181ff9f9fff 0xf7bc70c0ffcfcfff

def z265 : W := mkw 0x60fda7aeb7601d41 0xb07ed3d75bb00ea0 0xdfff27fe3fe01fe0 0xefff93ff1ff00ff0

def z266 : W := mkw 0x8c00000208aba7ba 0x460000010455d3dd 0x8100000007ffffff 0xc080000003ffffff

def z267 : W := mkw 0x0400020618222710 0x020001030c111388 0xdb8126ce3a666f80 0xedc093671d3337c0

def z268 : W := mkw 0xe85d01aa07e99deb 0xf42e80d503f4cef5 0xdfff01fe07f99fff 0xefff80ff03fccfff

def z269 : W := mkw 0x50100180a8021a14 0x280800c054010d0a 0xe700c181fc181e1f 0x738060c0fe0c0f0f

def z270 : W := mkw 0x0002585140000000 0x00012c28a0000000 0x2000d801c0000000 0x10006c00e0000000

def z271 : W := mkw 0x1020a000a8160214 0x08105000540b010a 0xeb00e081fa1e0e1f 0x75807040fd0f070f

def z272 : W := mkw 0x24450a6f1962a7d8 0x922285378cb153ec 0xfb873eff3be7eff9 0xfdc39f7f9df3f7fc

def z273 : W := mkw 0xe07ff5a807dd5841 0xf03ffad403eeac20 0xbe7fff3007fff061 0xdf3fff9803fff830

def z274 : W := mkw 0x0008000006140001 0x00040000030a0000 0x80000000061e0001 0x40000000030f0000

def z275 : W := mkw 0x20c75e7f51600540 0x9063af3fa8b002a0 0x10871e7e01e001e0 0x88438f3f00f000f0

def z276 : W := mkw 0x80fff5b8e7dd4001 0xc07ffadc73eea000 0x047ec130c5980000 0x023f609862cc0000

def z277 : W := mkw 0x0075a1a8a0000000 0x003ad0d450000000 0x7effe1fff8000000 0x3f7ff0fffc000000

def z278 : W := mkw 0x54fffffffe36bf9d 0x2a7fffffff1b5fce 0xfffffffffe7fff9f 0xffffffffff3fffcf

def z279 : W := mkw 0x00800a7d50000000 0x0040053ea8000000 0x0080007e00000000 0x0040003f00000000

def z280 : W := mkw 0x88025851488b82ba 0x44012c28a445c15d 0xff86f9f1ff9f9fff 0xffc37cf8ffcfcfff

def z281 : W := mkw 0x8002500000890000 0x4001280000448000 0xf786d970059991e1 0xfbc36cb802ccc8f0

def z282 : W := mkw 0x685d09fb47609deb 0xb42e84fda3b04ef5 0xdfff01ffc7e01ffe 0xefff80ffe3f00fff

def z283 : W := mkw 0x5438a386be363f15 0x2a1c51c35f1b1f8a 0x0879268e3a666e00 0x043c93471d333700

def z284 : W := mkw 0x5038a180a6141805 0x281c50c0530a0c02 0xe778c101c418101f 0x73bc6080e20c080f

def z285 : W := mkw 0x605f59fb47601d41 0xb02facfda3b00ea0 0xffffd9ffc7e01fe0 0xffffecffe3f00ff0

def z286 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x45fe01fe05801fe0 0x22ff00ff02c00ff0

def z287 : W := mkw 0x88f7fdf9e08980aa 0x447bfefcf044c055 0xf7fed971c59991ff 0xfbff6cb8e2ccc8ff

def z288 : W := mkw 0x5438a182ae36bf9d 0x2a1c50c1571b5fce 0xef78e181fe7fff9f 0xf7bc70c0ff3fffcf

def z289 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xc18000cf3a67ef99 0xe0c000679d33f7cc

def z290 : W := mkw 0x0065a40000000000 0x0032d20000000000 0x0879260000000000 0x043c930000000000

def z291 : W := mkw 0x5038a180a6141805 0x281c50c0530a0c02 0xae78e100c61e1007 0x573c7080630f0803

def z292 : W := mkw 0x701001aaa8221f54 0x380800d554110faa 0x418001fff8001ffe 0x20c000fffc000fff

def z293 : W := mkw 0xa847587b41e985ea 0xd423ac3da0f4c2f5 0x1087187e01e181e0 0x88438c3f00f0c0f0

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x5686017000000000 0x2b4300b800000000

def z295 : W := mkw 0x64100bef1822bfd8 0x320805f78c115fec 0xfb813fff3a67fff9 0xfdc09fff9d33fffc

def z296 : W := mkw 0x0000000200200500 0x0000000100100280 0xdb8100ce02600f80 0xedc08067013007c0

def z297 : W := mkw 0x500800000e161a15 0x28040000070b0d0a 0xe700c101c61e1e1f 0x73806080e30f0f0f

def z298 : W := mkw 0x605d09eb07609dc9 0xb02e84f583b04ee4 0xffff19ff07e19ff9 0xffff8cff83f0cffc

def z299 : W := mkw 0x1000000008160214 0x08000000040b010a 0x00000000001e001f 0x00000000000f000f

def z300 : W := mkw 0x205501aa01600540 0x902a80d500b002a0 0x5eff01fe01e001e0 0xaf7f80ff00f000f0

def z301 : W := mkw 0x8022f400009d4000 0x40117a00004ea000 0x0000c00000180000 0x00006000000c0000

def z302 : W := mkw 0x0030a180a0000000 0x001850c050000000 0x0878208038000000 0x043c10401c000000

def z303 : W := mkw 0x50900bfdf8021a14 0x284805fefc010d0a 0x418001fff8001e1e 0x20c000fffc000f0f

def z304 : W := mkw 0x80a2fe55f09d4000 0x40517f2af84ea000 0x2000fe01f81fe001 0x10007f00fc0ff000

def z305 : W := mkw 0x0000000008020210 0x0000000004010108 0x080020803a060e00 0x040010401d030700

def z306 : W := mkw 0x6018018207601d41 0xb00c00c103b00ea0 0xcf78018007e01fe0 0xe7bc00c003f00ff0

def z307 : W := mkw 0x44180bc71e22bf99 0x220c05e38f115fcc 0xfff93fcf3e67ff99 0xfffc9fe79f33ffcc

def z308 : W := mkw 0x00000a4518020210 0x000005228c010108 0xfb813ecf3a060e19 0x7dc09f679d03070c

def z309 : W := mkw 0x6008000207601d41 0xb004000103b00ea0 0xd786017007e01fe0 0xebc300b803f00ff0

def z310 : W := mkw 0x046da6061f766711 0x8236d3030fbb3388 0x0879268e3a666e00 0x043c93471d333700

def z311 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7efffffff98181e0 0xbf7ffffffcc0c0f0

def z312 : W := mkw 0x0000000200200500 0x0000000100100280 0xdf8701fe07e01fe0 0xefc380ff03f00ff0

def z313 : W := mkw 0x846ff6061fff6711 0xc237fb030fffb388 0xbe7ffe8e3fffee01 0xdf3fff471ffff700

def z314 : W := mkw 0x80f7fffdf1c94000 0xc07bfffef8e4a000 0x7efffffff9e1e000 0xbf7ffffffcf0f000

def z315 : W := mkw 0x2000000201600540 0x9000000100b002a0 0x0000000001e001e0 0x8000000000f000f0

def z316 : W := mkw 0x040008430822a798 0x02000421841153cc 0xf38018410267ef99 0xf9c00c208133f7cc

def z317 : W := mkw 0x80effe7d57dd4001 0xc077ff3eabeea000 0xbefffe7e07ffe001 0xdf7fff3f03fff000

def z318 : W := mkw 0x04a2fe57f822a798 0x02517f2bfc1153cc 0xfb81fecffa67ef99 0xfdc0ff67fd33f7cc

def z319 : W := mkw 0x501801800e161a15 0x280c00c0070b0d0a 0xcf780180061e1e1f 0x67bc00c0030f0f0f

def z320 : W := mkw 0x0000000200200500 0x0000000100100280 0xfb813ece0267ef81 0xfdc09f670133f7c0

def z321 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x2879fe8ff8000000 0x143cff47fc000000

def z322 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xf38018cf38018f99 0xf9c00c679c00c7cc

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0xd380004000000180 0xe9c00020000000c0

def z324 : W := mkw 0x00f7f5b8e0000000 0x007bfadc70000000 0x3e7fff30c0000000 0x1f3fff9860000000

def z325 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffffc18101f 0x7ffffffffe0c080f

def z326 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x18ff00fe03e00fe0 0x8c7f807f01f007f0

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x9606000005800000 0xcb03000002c00000

def z328 : W := mkw 0xa047542a01e94540 0xd023aa1500f4a2a0 0x10871e7e01e1e1e0 0x88438f3f00f0f0f0

def z329 : W := mkw 0x50fff5b8e6141805 0x287ffadc730a0c02 0x047ec130c4181006 0x023f6098620c0803

def z330 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x498126cf3a666f98 0x24c093679d3337cc

def z331 : W := mkw 0xf87ff9fbefff9fff 0xfc3ffcfdf7ffcfff 0xfffff9ffffff9fff 0xfffffcffffffcfff

def z332 : W := mkw 0x0000020410000000 0x0000010208000000 0x0801268e38000000 0x040093471c000000

def z333 : W := mkw 0xd038a180afdf5a15 0xe81c50c057efad0a 0xef78e181fffffe1f 0xf7bc70c0ffffff0f

def z334 : W := mkw 0x0000000008020210 0x0000000004010108 0x4100008138000e18 0x208000409c00070c

def z335 : W := mkw 0x80effe55f7dd4001 0xc077ff2afbeea000 0xbe7ffe01ffffe001 0xdf3fff00fffff000

def z336 : W := mkw 0x88a2fe55f08980aa 0x44517f2af844c055 0xf786ff71fd9991ff 0xfbc37fb8feccc8ff

def z337 : W := mkw 0x50fffffdf6141805 0x287ffffefb0a0c02 0x7efffffffc181006 0x3f7ffffffe0c0803

def z338 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xf3861871018181f9 0xf9c30c3880c0c0fc

def z339 : W := mkw 0x0000000008020210 0x0000000004010108 0xef00e181fe1e1e1f 0x778070c0ff0f0f0f

def z340 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x30813e4f3867e199 0x98409f279c33f0cc

def z341 : W := mkw 0x507da580af565a15 0xa83ed2c057ab2d0a 0xef79e781fe7e7e1f 0x77bcf3c0ff3f3f0f

def z342 : W := mkw 0x806ffe4517dd4001 0xc037ff228beea000 0xfefffecf3fffe001 0xff7fff679ffff000

def z343 : W := mkw 0x84080a471fffe799 0xc20405238ffff3cc 0xfb813ecf3fffef99 0xfdc09f679ffff7cc

def z344 : W := mkw 0x50100180a0001804 0x280800c050000c02 0x00000100c0001006 0x0000008060000803

def z345 : W := mkw 0x00d75ffdf0000000 0x006baffef8000000 0x50871ffff8000000 0x28438ffffc000000

def z346 : W := mkw 0x6000000200201d40 0x3000000100100ea0 0x0100000000001fe0 0x0080000000000ff0

def z347 : W := mkw 0x00550bed10000000 0x002a85f688000000 0x7eff3fff38000000 0x3f7f9fff9c000000

def z348 : W := mkw 0x0028a00006140001 0x00145000030a0000 0xef78e101c61e101f 0x77bc7080e30f080f

def z349 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xae78e0803e1e0e01 0x573c70401f0f0700

def z350 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x147fde0005f9e000 0x8a3fef0002fcf000

def z351 : W := mkw 0x5038a182ae361f15 0x281c50c1571b0f8a 0xfff9e1cffe7e1f9f 0xfffcf0e7ff3f0fcf

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0xc700010004001000 0x6380008002000800

def z353 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x5eff27fe38000000 0x2f7f93ff1c000000

def z354 : W := mkw 0x0002585140008088 0x00012c28a0004044 0xf786d971c0018199 0xfbc36cb8e000c0cc

def z355 : W := mkw 0x0002585140000000 0x00012c28a0000000 0xf786d971c58011e0 0xfbc36cb8e2c008f0

def z356 : W := mkw 0x581009d1e8029abe 0x2c0804e8f4014d5f 0x418001f1f8001ffe 0x20c000f8fc000fff

def z357 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x2878e081fa1e0e1f 0x143c7040fd0f070f

def z358 : W := mkw 0x004d000007400001 0x8026800003a00000 0xbe7f3e0007e7e001 0xdf3f9f0003f3f000

def z359 : W := mkw 0xe05f51aa07e91d41 0xf02fa8d503f48ea0 0xffffd9fe07f99fe1 0xffffecff03fccff0

def z360 : W := mkw 0x040000020822a798 0x02000001041153cc 0xdb8100ce0267ef99 0xedc080670133f7cc

def z361 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x7b813ecf38000f98 0x3dc09f679c0007cc

def z362 : W := mkw 0x0c000a575822a7ba 0x0600052bac1153dd 0x418001fff8001ffe 0x20c000fffc000fff

def z363 : W := mkw 0x88f7fffdf0890022 0x447bfffef8448011 0x7efffffffd981066 0x3f7ffffffecc0833

def z364 : W := mkw 0x2045002a01600540 0x9022801500b002a0 0xdb8700fe03e00fe0 0xedc3807f01f007f0

def z365 : W := mkw 0x04f7fffff8222710 0x027bfffffc111388 0x7efffffffa666e00 0x3f7ffffffd333700

def z366 : W := mkw 0x60f7fffff0201d40 0x307bfffff8100ea0 0x7ffffffff8001fe0 0x3ffffffffc000ff0

def z367 : W := mkw 0x601001aa00201d40 0x300800d500100ea0 0x0000008e00000e00 0x0000004700000700

def z368 : W := mkw 0x601001a800001840 0x300800d400000c20 0x0000013000001060 0x0000009800000830

def z369 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xf380d841c019819f 0xf9c06c20e00cc0cf

def z370 : W := mkw 0x5438a386be363f15 0x2a1c51c35f1b1f8a 0xef79e78ffe7e7e1f 0x77bcf3c7ff3f3f0f

def z371 : W := mkw 0x804f540007dd4001 0xc027aa0003eea000 0x90071e0007ffe001 0xc8038f0003fff000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0xb200180000018001 0xd9000c000000c000

def z373 : W := mkw 0x00fffffdf6140001 0x007ffffefb0a0000 0xfefffffffe1e0001 0x7f7fffffff0f0000

def z374 : W := mkw 0x08000851400080aa 0x04000428a0004055 0x00800070000001e0 0x00400038000000f0

def z375 : W := mkw 0x507da1a8ae161a15 0x283ed0d4570b0d0a 0xffffe1fffe1e1e1f 0x7ffff0ffff0f0f0f

def z376 : W := mkw 0x8c000a4718aba7ba 0x460005238c55d3dd 0xfb813ecf3fffffff 0xfdc09f679fffffff

def z377 : W := mkw 0x00e7fe55f0000000 0x0073ff2af8000000 0x3e7ffe01f8000000 0x1f3fff00fc000000

def z378 : W := mkw 0xd8fffffdfe9f9abf 0x6c7ffffeff4fcd5f 0xffffffffff9f9fff 0xffffffffffcfcfff

def z379 : W := mkw 0x885759f9408980aa 0x442bacfca044c055 0xffffd9ffc59991ff 0xffffecffe2ccc8ff

def z380 : W := mkw 0x00a0a604b0000000 0x0050530258000000 0x0000260038000000 0x000013001c000000

def z381 : W := mkw 0x80c75e7d51c94000 0xc063af3ea8e4a000 0x10871e7e01e1e000 0x88438f3f00f0f000

def z382 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x5eff01fe02600e00 0x2f7f80ff01300700

def z383 : W := mkw 0x00e7fe7df0000000 0x0073ff3ef8000000 0x3087fe7ff8000000 0x1843ff3ffc000000

def z384 : W := mkw 0x88fffffdf7ddc0ab 0xc47ffffefbeee055 0xfffffffffffff1ff 0xfffffffffffff8ff

def z385 : W := mkw 0x802af400069d4001 0x40157a00034ea000 0xae78fe00061fe001 0x573c7f00030ff000

def z386 : W := mkw 0x9022f400a89f4214 0x48117a00544fa10a 0x2000fe01f81fe01f 0x10007f00fc0ff00f

def z387 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x0c7f01be07e01e60 0x063f80df03f00f30

def z388 : W := mkw 0x5038a9c1ae169a9d 0x281c54e0d70b4d4e 0xfff8f9c1fe1f9f9f 0xfffc7ce0ff0fcfcf

def z389 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffffd8011e0 0xfffffffffec008f0

def z390 : W := mkw 0x04f5a7aeb8222710 0x027ad3d75c111388 0x0879268e3a666e00 0x043c93471d333700

def z391 : W := mkw 0x0077f5a800000000 0x003bfad400000000 0x7efffffe00000000 0x3f7fffff00000000

def z392 : W := mkw 0x6008000007401841 0xb004000003a00c20 0x0000000005801060 0x0000000002c00830

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400c100c4181006 0x02006080620c0803

def z394 : W := mkw 0x50100180a8021a14 0x280800c054010d0a 0x0000008038000e00 0x000000401c000700

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa00200002060001 0x5500100001030000

def z396 : W := mkw 0x00a2fe55f0000000 0x00517f2af8000000 0x7a81fecff8000000 0x3d40ff67fc000000

def z397 : W := mkw 0x00925bfdf0000000 0x00492dfef8000000 0x7686d9fff8000000 0x3b436cfffc000000

def z398 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x8578c100c61e1e1f 0x42bc6080630f0f0f

def z399 : W := mkw 0x88475c5141c9c0aa 0xc423ae28a0e4e055 0xf787df71c5f9f1ff 0xfbc3efb8e2fcf8ff

def z400 : W := mkw 0x0000000200200500 0x0000000100100280 0x8100000002600f80 0xc0800000013007c0

def z401 : W := mkw 0x705d01aa0f761f55 0xb82e80d507bb0faa 0xdfff01fe07fe1fff 0xefff80ff03ff0fff

def z402 : W := mkw 0x54100bc7b822bf9c 0x2a0805e3dc115fce 0x418001cff8001f9e 0x20c000e7fc000fcf

def z403 : W := mkw 0x00fffffdf7544001 0x807ffffefbaa2000 0x7efffffffa666000 0x3f7ffffffd333000

def z404 : W := mkw 0x886ffc5147ddc0ab 0xc437fe28a3eee055 0xf7fed971c59991ff 0xfbff6cb8e2ccc8ff

def z405 : W := mkw 0xd07ff580afdf5a15 0xe83ffac057efad0a 0xbe7ffe803fffee01 0xdf3fff401ffff700

def z406 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x61803ecf3807ef99 0x30c01f679c03f7cc

def z407 : W := mkw 0x0030a180a8020210 0x001850c054010108 0xef78e181fa060e19 0x77bc70c0fd03070c

def z408 : W := mkw 0x5438abc5be16ba9d 0x2a1c55e2df0b5d4e 0xef78ff81fe1ffe1f 0x77bc7fc0ff0fff0f

def z409 : W := mkw 0x8067f40001dd4000 0xc033fa0000eea000 0x3007fe0001ffe001 0x9803ff0000fff000

def z410 : W := mkw 0x8422fe4718bfe798 0x42117f238c5ff3cc 0xfb81fecf3a7fef99 0xfdc0ff679d3ff7cc

def z411 : W := mkw 0x84ffffffffffe799 0xc27ffffffffff3cc 0xffffffffffffef99 0xfffffffffffff7cc

def z412 : W := mkw 0x5038a180a6141805 0x281c50c0530a0c02 0x0078000000000000 0x003c000000000000

def z413 : W := mkw 0x0020a00000140000 0x00105000000a0000 0x2000e000001e0001 0x10007000000f0000

def z414 : W := mkw 0x04025a575822a798 0x02012d2bac1153cc 0xff87fffffa67ef99 0xffc3fffffd33f7cc

def z415 : W := mkw 0x040000020822a798 0x02000001041153cc 0xeb0020813a67ef99 0xf58010409d33f7cc

def z416 : W := mkw 0x88f7f5b8e0890022 0x447bfadc70448011 0x047ec130c5981066 0x023f609862cc0833

def z417 : W := mkw 0x8c025a5758aba7ba 0x46012d2bac55d3dd 0xfb873eff3be7eff9 0xfdc39f7f9df3f7fc

def z418 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x7686d971c18181e0 0xbb436cb8e0c0c0f0

def z419 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x51811ecf3861ef98 0xa8c08f679c30f7cc

def z420 : W := mkw 0x804f500007c90001 0xc027a80003e48000 0xbe7fd80007f98001 0xdf3fec0003fcc000

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0xe300000100000019 0x718000008000000c

def z422 : W := mkw 0x8002584100898088 0x40012c208044c044 0xf786d84105998199 0xfbc36c2082ccc0cc

def z423 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x6180d971c01991ff 0x30c06cb8e00cc8ff

def z424 : W := mkw 0x04000a451802a298 0x020005228c01514c 0xba013e013a67e019 0xdd009f009d33f00c

def z425 : W := mkw 0x0000000008020210 0x0000000004010108 0xfb013e813a67ee19 0xfd809f409d33f70c

def z426 : W := mkw 0x00f7f7acb0000000 0x007bfbd658000000 0x3e7ffe8e38000000 0x1f3fff471c000000

def z427 : W := mkw 0x00f7fffff0200500 0x007bfffff8100280 0xfffffffffa600f80 0xfffffffffd3007c0

def z428 : W := mkw 0x0000000200200500 0x0000000100100280 0x418000ce00000f80 0x20c00067000007c0

def z429 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xeb8020cf3a060f99 0x75c010679d0307cc

def z430 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x91811e4e0267ef99 0xc8c08f270133f7cc

def z431 : W := mkw 0x10000000a8020214 0x080000005401010a 0x00000001f800001e 0x00000000fc00000f

def z432 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xff7fff01c7fff01f 0xffbfff80e3fff80f

def z433 : W := mkw 0x604d002a07601d41 0xb026801503b00ea0 0x9187007e07e01fe0 0xc8c3803f03f00ff0

def z434 : W := mkw 0x0000000008020210 0x0000000004010108 0x2000200138060019 0x100010009c03000c

def z435 : W := mkw 0x0067fe4510000000 0x0033ff2288000000 0x7efffecf38000000 0x3f7fff679c000000

def z436 : W := mkw 0x605d01a807401841 0xb02e80d403a00c20 0x0078000000000000 0x003c000000000000

def z437 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x51861971c18191fe 0xa8c30cb8e0c0c8ff

def z438 : W := mkw 0x607da5aa07745d41 0xb03ed2d503ba2ea0 0x0879268e02666e00 0x043c934701333700

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a013e0000000000 0x1d009f0000000000

def z440 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x14ffdf7ec0000000 0x0a7fefbf60000000

def z441 : W := mkw 0x04000a451000a088 0x0200052288005044 0x00001e000001e000 0x00000f000000f000

def z442 : W := mkw 0xd03af180ae9f1a15 0x681d78c0574f8d0a 0xff7ef981ff9f9e1f 0xffbf7cc0ffcfcf0f

def z443 : W := mkw 0x0467fe471822a798 0x0233ff238c1153cc 0xfffffecf3a67ef99 0xffffff679d33f7cc

def z444 : W := mkw 0x0400020618222710 0x020001030c111388 0xba013e8e3a67ee01 0xdd009f471d33f700

def z445 : W := mkw 0xd0fffffdffdf5a15 0xe87ffffeffefad0a 0xfffffffffffffe1f 0xffffffffffffff0f

def z446 : W := mkw 0x645d01aa0f62bfd9 0xb22e80d507b15fec 0xdfff01fe07e7fff9 0xefff80ff03f3fffc

def z447 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x247eff31f8000000 0x123f7f98fc000000

def z448 : W := mkw 0x8802501040890022 0x4401280820448011 0xd786c170c59811e6 0xebc360b862cc08f3

def z449 : W := mkw 0x0032f9d1e0000000 0x00197ce8f0000000 0x7efef9f1f8000000 0x3f7f7cf8fc000000

def z450 : W := mkw 0x50180180ae021a15 0x280c00c057010d0a 0xcf780181fe001e1e 0x67bc00c0ff000f0f

def z451 : W := mkw 0x846ffe4717fde589 0xc237ff238bfef2c4 0xbefffe4e07ffe181 0xdf7fff2703fff0c0

def z452 : W := mkw 0x5038abc5be161a15 0x281c55e2df0b0d0a 0xfff9ffcffe1e1e1f 0x7ffcffe7ff0f0f0f

def z453 : W := mkw 0x8867fc51408980aa 0x4433fe28a044c055 0xffffff71c59991ff 0xffffffb8e2ccc8ff

def z454 : W := mkw 0x00000a4510008088 0x0000052288004044 0xfb813ecf38018199 0xfdc09f679c00c0cc

def z455 : W := mkw 0x707da1aaa7741d45 0xb83ed0d553ba0ea2 0xdfffc1fec7f81fe6 0xefffe0ff63fc0ff3

def z456 : W := mkw 0x50100180a8021a14 0x280800c054010d0a 0xeb002181fa061e1f 0x758010c0fd030f0f

def z457 : W := mkw 0x804f540007c94001 0xc027aa0003e4a000 0x9e7f1e0007e1e000 0xcf3f8f0003f0f000

def z458 : W := mkw 0x7038a1aaae361f55 0x381c50d5571b0faa 0xeff8e1fffe1e1fff 0x77fc70ffff0f0fff

def z459 : W := mkw 0x004d000007400001 0x8026800003a00000 0x0879000002600000 0x043c800001300000

def z460 : W := mkw 0x00fda7acb7544001 0x807ed3d65baa2000 0x0879268e3a666000 0x043c93471d333000

def z461 : W := mkw 0x5030a180a8021a14 0x281850c054010d0a 0x6f78e181f8001e1e 0x37bc70c0fc000f0f

def z462 : W := mkw 0x700800020f761f55 0xb804000107bb0faa 0x8100000007fe1fff 0xc080000003ff0fff

def z463 : W := mkw 0x00b2ffd5f0000000 0x00597feaf8000000 0x6e78ff81f8000000 0x373c7fc0fc000000

def z464 : W := mkw 0x2000002a00200540 0x10000015001002a0 0x0080007e000001e0 0x0040003f000000f0

def z465 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x49f901fe02601fe0 0x24fc80ff01300ff0

def z466 : W := mkw 0x401801800e021a11 0x200c00c007010d08 0xef7821813e061e19 0x77bc10c09f030f0c

def z467 : W := mkw 0x204d002a07600541 0x9026801503b002a0 0x9eff007e07e001e0 0xcf7f803f03f000f0

def z468 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0xae79e600067e6001 0x573cf300033f3000

def z469 : W := mkw 0x04900bfff822a798 0x024805fffc1153cc 0x418001fff8000f98 0x20c000fffc0007cc

def z470 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x6e78e181fa060e00 0x373c70c0fd030700

def z471 : W := mkw 0x707da1aaaf761f55 0xb83ed0d557bb0faa 0xdfff21fe3fe61fe0 0xefff90ff1ff30ff0

def z472 : W := mkw 0x0047540000000000 0x0023aa0000000000 0x10071e0000000000 0x08038f0000000000

def z473 : W := mkw 0x00025a5550000000 0x00012d2aa8000000 0x7e87fffff8000000 0x3f43fffffc000000

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x810000000418101f 0x40800000020c080f

def z475 : W := mkw 0x0400020618222710 0x020001030c111388 0xeb01268f3a666e19 0x758093479d33370c

def z476 : W := mkw 0x0000084108028298 0x000004208401414c 0xfb8038c13a078f99 0xfdc01c609d03c7cc

def z477 : W := mkw 0x08000851400080aa 0x04000428a0004055 0x00000001c000001e 0x00000000e000000f

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0xcb00008002000e00 0x6580004001000700

def z479 : W := mkw 0x0c000a575822a7ba 0x0600052bac1153dd 0xfb813ffffa67ffff 0xfdc09ffffd33ffff

def z480 : W := mkw 0x60900bfff0201d40 0x304805fff8100ea0 0x418001fff8001fe0 0x20c000fffc000ff0

def z481 : W := mkw 0x601801aa06201d41 0x300c00d503100ea0 0xcff801fe06001fe0 0x67fc00ff03000ff0

def z482 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff81ffcffe7fff9f 0xffc0ffe7ff3fffcf

def z483 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff873fff3fe7fff9 0xffc39fff9ff3fffc

def z484 : W := mkw 0x8067f40001c94000 0xc033fa0000e4a000 0x3e7ffe0001e1e000 0x9f3fff0000f0f000

def z485 : W := mkw 0x640800020f62bfd9 0xb204000107b15fec 0x8100000007e7fff9 0xc080000003f3fffc

def z486 : W := mkw 0x00900bfdf0000000 0x004805fef8000000 0x7a813ffff8000000 0x3d409ffffc000000

def z487 : W := mkw 0x8822fc51409dc0aa 0x44117e28a04ee055 0x2000fe01c01fe01f 0x10007f00e00ff00f

def z488 : W := mkw 0x5028a0000e161a15 0x28145000070b0d0a 0xaf78e000061e1e1f 0x57bc7000030f0f0f

def z489 : W := mkw 0x84475e4711e9e588 0xc223af2388f4f2c4 0x10871e4e01e1e180 0x88438f2700f0f0c0

def z490 : W := mkw 0x0028a00006140001 0x00145000030a0000 0x0878200002060000 0x043c100001030000

def z491 : W := mkw 0x4018018006001801 0x200c00c003000c00 0xef78c181c6181e1f 0x77bc60c0e30c0f0f

def z492 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x857e013007e01fe0 0xc2bf009803f00ff0

def z493 : W := mkw 0x8c025a55588ba2ba 0x46012d2aac45d15d 0xf786ff71fd9ff1ff 0xfbc37fb8fecff8ff

def z494 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x3086d871c19981ff 0x98436c38e0ccc0ff

def z495 : W := mkw 0x08000851400080aa 0x04000428a0004055 0xd7860171c58011fe 0xebc300b8e2c008ff

def z496 : W := mkw 0x80fffffdf7dd4001 0xc07ffffefbeea000 0x7efffffffd980000 0x3f7ffffffecc0000

def z497 : W := mkw 0x607da1aa07741d41 0xb03ed0d503ba0ea0 0xffffe1fe07fe1fe1 0xfffff0ff03ff0ff0

def z498 : W := mkw 0x605501aa00201d40 0x302a80d500100ea0 0x5fff01fe00001fe0 0x2fff80ff00000ff0

def z499 : W := mkw 0x00c75e7d50000000 0x0063af3ea8000000 0x7a873eff38000000 0x3d439f7f9c000000

def z500 : W := mkw 0x80fff5b8e7dd4001 0xc07ffadc73eea000 0xbe7fff30c7ffe001 0xdf3fff9863fff000

def z501 : W := mkw 0xe808000207e99deb 0xf404000103f4cef5 0x8100000007f99fff 0xc080000003fccfff

def z502 : W := mkw 0x00a2fe55f0000000 0x00517f2af8000000 0x7686ff71f8000000 0x3b437fb8fc000000

def z503 : W := mkw 0x0000000000000000 0x0000000000000000 0x6600c101c0000000 0x33006080e0000000

def z504 : W := mkw 0x807ff5a807dd4001 0xc03ffad403eea000 0xfefffffe07ffe001 0xff7fffff03fff000

def z505 : W := mkw 0xe85f59f947c998eb 0xf42facfca3e4cc75 0xf7fed971c59991ff 0xfbff6cb8e2ccc8ff

def z506 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xeb7820813a060e19 0x75bc10409d03070c

def z507 : W := mkw 0x54080a471e36bf9d 0x2a0405238f1b5fce 0xfb813ecf3e7fff9f 0xfdc09f679f3fffcf

def z508 : W := mkw 0xe0fffffff7fd5d41 0xf07ffffffbfeaea0 0xffffffffffffffe1 0xfffffffffffffff0

def z509 : W := mkw 0x88000851408980aa 0x44000428a044c055 0xc1800171c59991ff 0xe0c000b8e2ccc8ff

def z510 : W := mkw 0xe85f59fb47e99deb 0xf42facfda3f4cef5 0xdfff19fe07e19fe0 0xefff8cff03f0cff0

def z511 : W := mkw 0x0002500000000000 0x0001280000000000 0x3606d80000000000 0x1b036c0000000000

def z512 : W := mkw 0x8c025a5758aba7ba 0x46012d2bac55d3dd 0xfb81fecffa7fef9f 0xfdc0ff67fd3ff7cf

def z513 : W := mkw 0x807ff580a7dd4001 0xc03ffac053eea000 0xfe7fff81ffffe001 0xff3fffc0fffff000

def z514 : W := mkw 0x004d000007400001 0x8026800003a00000 0xdfff017007e011e0 0xefff80b803f008f0

def z515 : W := mkw 0xd83af190ee9f1a37 0x6c1d78c8774f8d1b 0xef7ee1b1ff9e1e7f 0x77bf70d8ffcf0f3f

def z516 : W := mkw 0x705d01aaaf621f55 0xb82e80d557b10faa 0xdfff01ffffe01ffe 0xefff80fffff00fff

def z517 : W := mkw 0x04000a4718222710 0x020005238c111388 0x7a813ecf3a666e00 0x3d409f679d333700

def z518 : W := mkw 0x80fff7acb7dd4001 0xc07ffbd65beea000 0xbe7ffe8e3fffe001 0xdf3fff471ffff000

def z519 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x9e7fc00007f80000 0xcf3fe00003fc0000

def z520 : W := mkw 0x1020a000a8160214 0x08105000540b010a 0xe700e101fc1e101f 0x73807080fe0f080f

def z521 : W := mkw 0x5000000008021a14 0x2800000004010d0a 0x0100000000001e1e 0x0080000000000f0f

def z522 : W := mkw 0x04000a451802a298 0x020005228c01514c 0x0000000138000018 0x000000009c00000c

def z523 : W := mkw 0x607da5aa07745d41 0xb03ed2d503ba2ea0 0xdfff27fe07e67fe0 0xefff93ff03f33ff0

def z524 : W := mkw 0x00000a4510000000 0x0000052288000000 0x10811e4e00000000 0x08408f2700000000

def z525 : W := mkw 0x507ff580ae161a15 0x283ffac0570b0d0a 0xff7fff81fe1e1e1f 0x7fbfffc0ff0f0f0f

def z526 : W := mkw 0xf07ff5aaafff5f55 0xf83ffad557ffafaa 0xffffffffffffffff 0xffffffffffffffff

def z527 : W := mkw 0xe81259fb40a99dea 0x74092cfda054cef5 0xf786d9ffc5999fff 0xfbc36cffe2cccfff

def z528 : W := mkw 0x605d01a807401841 0xb02e80d403a00c20 0x5eff01fe05801060 0x2f7f80ff02c00830

def z529 : W := mkw 0x0008000007544001 0x8004000003aa2000 0x0000000002666000 0x0000000001333000

def z530 : W := mkw 0x04f5afefb822a798 0x027ad7f7dc1153cc 0xfbf93ecf3a67ef99 0xfdfc9f679d33f7cc

def z531 : W := mkw 0xe05f55aa07e95d41 0xf02faad503f4aea0 0xdfff1ffe07e1ffe0 0xefff8fff03f0fff0

def z532 : W := mkw 0x8c025a5750a9a5aa 0x46012d2ba854d2d5 0x10871e7e01e1e1e0 0x88438f3f00f0f0f0

def z533 : W := mkw 0x00000a4510000000 0x0000052288000000 0x20003e0138000000 0x10001f009c000000

def z534 : W := mkw 0x800a500007dd4001 0xc005280003eea000 0xb606d80007ffe001 0xdb036c0003fff000

def z535 : W := mkw 0x8002500000890000 0x4001280000448000 0x1006180001818000 0x88030c0000c0c000

def z536 : W := mkw 0x0000084100008088 0x0000042080004044 0xf780d941c419919f 0xfbc06ca0e20cc8cf

def z537 : W := mkw 0x0400020418022210 0x020001020c011108 0x0000260038066000 0x000013001c033000

def z538 : W := mkw 0xc81a59d1468998ab 0x640d2ce8a344cc55 0xfffed9f1c7999fff 0xffff6cf8e3cccfff

def z539 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xd7861970058191e0 0xebc30cb802c0c8f0

def z540 : W := mkw 0x040002061822a798 0x020001030c1153cc 0x8901268e3a67ef99 0xc48093471d33f7cc

def z541 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x6e79e78ff8000000 0x373cf3c7fc000000

def z542 : W := mkw 0x645d0bef1f62bfd9 0xb22e85f78fb15fec 0xdfff01ff3fe01ff8 0xefff80ff9ff00ffc

def z543 : W := mkw 0x0000000208220710 0x0000000104110388 0xfb8120cf3a660f99 0xfdc090679d3307cc

def z544 : W := mkw 0xd80a58514e9f9abf 0x6c052c28a74fcd5f 0xf786d971c79f9fff 0xfbc36cb8e3cfcfff

def z545 : W := mkw 0x880a585147ddc0ab 0xc4052c28a3eee055 0xf786d971c7fff1ff 0xfbc36cb8e3fff8ff

def z546 : W := mkw 0x8802501040890022 0x4401280820448011 0x0006003001800060 0x0003001800c00030

def z547 : W := mkw 0xd83af9d1ee9f9abf 0x6c1d7ce8f74fcd5f 0xef78f981fe1f9e1f 0x77bc7cc0ff0fcf0f

def z548 : W := mkw 0x0020a000a0000000 0x0010500050000000 0x2000e001f8000000 0x10007000fc000000

def z549 : W := mkw 0x00d75ffd50000000 0x006baffea8000000 0x5eff1ffe00000000 0x2f7f8fff00000000

def z550 : W := mkw 0x04000a471020a588 0x02000523881052c4 0xf3811e4f0061e199 0xf9c08f278030f0cc

def z551 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xa100d801c59991ff 0xd0806c00e2ccc8ff

def z552 : W := mkw 0x4018018206201d01 0x200c00c103100e80 0xdff901ce06601f80 0xeffc80e703300fc0

def z553 : W := mkw 0x605d01aa0f621f51 0xb02e80d507b10fa8 0xffff21ff3fe61ff9 0xffff90ff9ff30ffc

def z554 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xb67ed80005998001 0xdb3f6c0002ccc000

def z555 : W := mkw 0x04000a471020a588 0x02000523881052c4 0x7a813ecf3861e180 0xbd409f679c30f0c0

def z556 : W := mkw 0x0800001040000022 0x0400000820000011 0x00000130c0001066 0x0000009860000833

def z557 : W := mkw 0x54100bc7b822bf9c 0x2a0805e3dc115fce 0xfb813fcffa67ff9f 0xfdc09fe7fd33ffcf

def z558 : W := mkw 0x645d0bef1760bdc9 0xb22e85f78bb05ee4 0xdfff1ffe07e1ffe0 0xefff8fff03f0fff0

def z559 : W := mkw 0xdc3afbd7febfbfbf 0x6e1d7debff5fdfdf 0xffffffffffffffff 0xffffffffffffffff

def z560 : W := mkw 0x00f7f5b8e0000000 0x007bfadc70000000 0x5effc1fec0000000 0x2f7fe0ff60000000

def z561 : W := mkw 0x886ffc5147ddc0ab 0xc437fe28a3eee055 0xbefffe7007ffe1e1 0xdf7fff3803fff0f0

def z562 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xfffee1f1ff9e1fff 0xffff70f8ffcf0fff

def z563 : W := mkw 0x08025851400080aa 0x04012c28a0004055 0x7786d971c00011fe 0x3bc36cb8e00008ff

def z564 : W := mkw 0x0022f40000000000 0x00117a0000000000 0x2000fe0000000000 0x10007f0000000000

def z565 : W := mkw 0x005d01a807400001 0x802e80d403a00000 0xdeff01fe07e00000 0xef7f80ff03f00000

def z566 : W := mkw 0x8002585140890000 0x40012c28a0448000 0xf686d971c5998001 0xfb436cb8e2ccc000

def z567 : W := mkw 0x8802501040890022 0x4401280820448011 0x0000c000c0180006 0x00006000600c0003

def z568 : W := mkw 0xe85f51ba47e91d63 0xf42fa8dd23f48eb1 0xdfffc1fec7f81fe6 0xefffe0ff63fc0ff3

def z569 : W := mkw 0x906ff400afdf4215 0xc837fa0057efa10a 0xbe7ffe01ffffe01f 0xdf3fff00fffff00f

def z570 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x18813ece3a67ef80 0x8c409f671d33f7c0

def z571 : W := mkw 0x006ff40006140001 0x0037fa00030a0000 0xbe7ffe00061e0001 0x5f3fff00030f0000

def z572 : W := mkw 0x8802501040890022 0x4401280820448011 0xe706c131c598107f 0x73836098e2cc083f

def z573 : W := mkw 0x00d50bfdf0000000 0x006a85fef8000000 0x5eff01fff8000000 0x2f7f80fffc000000

def z574 : W := mkw 0xd03af580ae9f5a15 0x681d7ac0574fad0a 0xef78ff81fe1ffe1f 0x77bc7fc0ff0fff0f

def z575 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x3e7ffe0005980000 0x1f3fff0002cc0000

def z576 : W := mkw 0x1420aa45b816a29c 0x0a105522dc0b514e 0x2000fe01f81fe01f 0x10007f00fc0ff00f

def z577 : W := mkw 0x04f7fffff822a798 0x027bfffffc1153cc 0x7ffffffff8000f98 0x3ffffffffc0007cc

def z578 : W := mkw 0xe07ff5aa07fd5d41 0xf03ffad503feaea0 0xdfffc1fe07f81fe0 0xefffe0ff03fc0ff0

def z579 : W := mkw 0xd81259d1e88b9abe 0x6c092ce8f445cd5f 0xf786d9f1fd999fff 0xfbc36cf8fecccfff

def z580 : W := mkw 0x707da1a8a7541845 0xb83ed0d453aa0c22 0x047ec130c5981066 0x023f609862cc0833

def z581 : W := mkw 0x00e7fe7d50000000 0x0073ff3ea8000000 0x3efffe7e00000000 0x1f7fff3f00000000

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000267e001 0xc00000000133f000

def z583 : W := mkw 0x50b8abfdfe161a15 0x285c55feff0b0d0a 0xeff8e1fffe1e1e1f 0x77fc70ffff0f0f0f

def z584 : W := mkw 0x8000000001c94000 0xc000000000e4a000 0x0000000001e1e000 0x8000000000f0f000

def z585 : W := mkw 0xe05d01aa07fd5d41 0xf02e80d503feaea0 0xdfff01fe07ffffe1 0xefff80ff03fffff0

def z586 : W := mkw 0x4018018006001801 0x200c00c003000c00 0x0878008002000e00 0x043c004001000700

def z587 : W := mkw 0xd07ff580a7dd5805 0xe83ffac053eeac02 0x047ec100c5981006 0x023f608062cc0803

def z588 : W := mkw 0x0002585140000000 0x00012c28a0000000 0xf786d971c418101f 0x7bc36cb8e20c080f

def z589 : W := mkw 0x0000000200200500 0x0000000100100280 0x1081004e00600180 0x88408027003000c0

def z590 : W := mkw 0x046dae471f76e799 0x8236d7238fbb73cc 0xfbf93ecf3a67ef99 0xfdfc9f679d33f7cc

def z591 : W := mkw 0x08000000000080aa 0x0400000000004055 0x01000000000011fe 0x00800000000008ff

def z592 : W := mkw 0x707da1a8af561a55 0xb83ed0d457ab0d2a 0xef7ee1b1ff9e1e7f 0x77bf70d8ffcf0f3f

def z593 : W := mkw 0x0045000001400000 0x8022800000a00000 0x1007000001e00000 0x8803800000f00000

def z594 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x847ec00007ffe001 0xc23f600003fff000

def z595 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xb686d870059981e1 0xdb436c3802ccc0f0

def z596 : W := mkw 0x806da40007dd4001 0xc036d20003eea000 0x8879260007ffe001 0xc43c930003fff000

def z597 : W := mkw 0x882af851469d80ab 0x44157c28a34ec055 0xfffef971c79f91ff 0xffff7cb8e3cfc8ff

def z598 : W := mkw 0x004d000007400001 0x8026800003a00000 0x047e000005800000 0x023f000002c00000

def z599 : W := mkw 0x4018018006001801 0x200c00c003000c00 0xdffe01f007801fe0 0xefff00f803c00ff0

def z600 : W := mkw 0x0030a180a0000000 0x001850c050000000 0x0478c100c0000000 0x023c608060000000

def z601 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x4578c181fc181e1e 0x22bc60c0fe0c0f0f

def z602 : W := mkw 0x8c025a5758aba7ba 0x46012d2bac55d3dd 0xf786d9fffd999fff 0xfbc36cfffecccfff

def z603 : W := mkw 0x00fffffdf7400001 0x807ffffefba00000 0xfeffffffffe00000 0xff7ffffffff00000

def z604 : W := mkw 0x607da1aaa7601d41 0xb03ed0d553b00ea0 0xffffe1ffffe01fe0 0xfffff0fffff00ff0

def z605 : W := mkw 0x806ff4000fdf4211 0xc037fa0007efa108 0xff7ffe813fffee19 0xffbfff409ffff70c

def z606 : W := mkw 0x040000000802a298 0x020000000401514c 0x000000000007e019 0x000000000003f00c

def z607 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000c001c018001f 0x10006000e00c000f

def z608 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x91861870059991ff 0xc8c30c3802ccc8ff

def z609 : W := mkw 0x04f7fffff020a588 0x027bfffff81052c4 0x7efffffff861e180 0xbf7ffffffc30f0c0

def z610 : W := mkw 0x0028a0000e160211 0x00145000070b0108 0xef78e0813e1e0e19 0x77bc70409f0f070c

def z611 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x0c7fe60007fe6000 0x063ff30003ff3000

def z612 : W := mkw 0x00b2fffdf0000000 0x00597ffef8000000 0x6080fffff8000000 0x30407ffffc000000

def z613 : W := mkw 0x5838a9d1ee169abf 0x2c1c54e8f70b4d5f 0xeff8e1f1fe1e1fff 0x77fc70f8ff0f0fff

def z614 : W := mkw 0x005501a800000000 0x002a80d400000000 0xdfff01fe058011e0 0xefff80ff02c008f0

def z615 : W := mkw 0xd07ff580afdf5a15 0xe83ffac057efad0a 0xef7ee181ff9e1e1f 0x77bf70c0ffcf0f0f

def z616 : W := mkw 0x1020a000a8160214 0x08105000540b010a 0x0000200038060000 0x000010001c030000

def z617 : W := mkw 0x886ff41047dd4023 0xc437fa0823eea011 0x047ec130c5981066 0x023f609862cc0833

def z618 : W := mkw 0x60fff5b8e7401841 0xb07ffadc73a00c20 0x047ec130c5801060 0x023f609862c00830

def z619 : W := mkw 0x04900bfff822a798 0x024805fffc1153cc 0xfb813ffffa67ef99 0xfdc09ffffd33f7cc

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x10011e000061e000 0x88008f000030f000

def z621 : W := mkw 0x0428aa471e36a799 0x021455238f1b53cc 0xfff9fecf3e7fef99 0xfffcff679f3ff7cc

def z622 : W := mkw 0x5038a180a6141805 0x281c50c0530a0c02 0x6e78e181fc181006 0x373c70c0fe0c0803

def z623 : W := mkw 0x8832f9d1e08980aa 0x44197ce8f044c055 0xfffef9f1fd9991ff 0xffff7cf8feccc8ff

def z624 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xa1003e013a67ef99 0xd0801f009d33f7cc

def z625 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x7686d971c019801f 0x3b436cb8e00cc00f

def z626 : W := mkw 0x04000a451802a298 0x020005228c01514c 0xeb003e813a07ee19 0x75801f409d03f70c

def z627 : W := mkw 0x044d0a471f62a799 0x822685238fb153cc 0xffff3ecf3fe7ef99 0xffff9f679ff3f7cc

def z628 : W := mkw 0xe87ffdfb47fdddeb 0xf43ffefda3feeef5 0xffffffffc7ffffff 0xffffffffe3ffffff

def z629 : W := mkw 0x8802585140890022 0x44012c28a0448011 0x7686d971c5981066 0x3b436cb8e2cc0833

def z630 : W := mkw 0x9822f851e89f82be 0x4c117c28f44fc15f 0xf786f971fd9f91ff 0xfbc37cb8fecfc8ff

def z631 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xcf7821803e061e00 0x67bc10c01f030f00

def z632 : W := mkw 0xd83af190e69d1827 0x6c1d78c8734e8c13 0x047ec130c5981066 0x023f609862cc0833

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x0801260002666000 0x0400930001333000

def z634 : W := mkw 0x0045000000000000 0x0022800000000000 0x1e7f000000000000 0x0f3f800000000000

def z635 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0x0078000000000000 0x003c000000000000

def z636 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xcf79018e06601e00 0x67bc80c703300f00

def z637 : W := mkw 0x0045002800000000 0x0022801400000000 0x1087007e00000000 0x0843803f00000000

def z638 : W := mkw 0x0008000006000001 0x0004000003000000 0x8e78000006000000 0x473c000003000000

def z639 : W := mkw 0x60fffffff7601d41 0xb07ffffffbb00ea0 0x7efffffffa600e00 0x3f7ffffffd300700

def z640 : W := mkw 0x88475c5141c9c0aa 0xc423ae28a0e4e055 0x10871e7001e1e1e0 0x88438f3800f0f0f0

def z641 : W := mkw 0x1020a000a0140004 0x08105000500a0002 0x0000c000c0180006 0x00006000600c0003

def z642 : W := mkw 0x24450a6f1160a5c8 0x9222853788b052e4 0x10871e7e01e1e1e0 0x88438f3f00f0f0f0

def z643 : W := mkw 0x60fff5bae7601d41 0xb07ffadd73b00ea0 0xdfffc1fec7e01fe0 0xefffe0ff63f00ff0

def z644 : W := mkw 0x00000a4710200500 0x0000052388100280 0xfb813ecf3a600f80 0xfdc09f679d3007c0

def z645 : W := mkw 0x607ff5aa07601d41 0xb03ffad503b00ea0 0xfffffffe07e01fe0 0xffffffff03f00ff0

def z646 : W := mkw 0x8047540001c94000 0xc023aa0000e4a000 0xba073e0003e7e001 0xdd039f0001f3f000

def z647 : W := mkw 0x8008000007dd4001 0xc004000003eea000 0xba013e0007ffe001 0xdd009f0003fff000

def z648 : W := mkw 0x0028a00006140001 0x00145000030a0000 0x0478c00004180000 0x023c6000020c0000

def z649 : W := mkw 0x5438abc7be36bf9d 0x2a1c55e3df1b5fce 0xeff8e1cffe1e1f9f 0x77fc70e7ff0f0fcf

def z650 : W := mkw 0x8c025a55588ba2ba 0x46012d2aac45d15d 0x2000fe01f81fe01f 0x10007f00fc0ff00f

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x5a8100ce00000000 0x2d40806700000000

def z652 : W := mkw 0x604d000207601d41 0xb026800103b00ea0 0x9f7f000007e01fe0 0xcfbf800003f00ff0

def z653 : W := mkw 0x50fff5b8ee161a15 0x287ffadc770b0d0a 0xef7ee1b1fe1e1e1f 0x77bf70d8ff0f0f0f

def z654 : W := mkw 0x5038a180a6141805 0x281c50c0530a0c02 0xcf78c180c6181e06 0x67bc60c0630c0f03

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x0406013005801060 0x0203009802c00830

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0x41800170000011e0 0x20c000b8000008f0

def z657 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x44fec1fff8000000 0x227f60fffc000000

def z658 : W := mkw 0xd47fffc7bfffff9d 0xea3fffe3dfffffce 0xffffffcfffffff9f 0xffffffe7ffffffcf

def z659 : W := mkw 0x0000084100008088 0x0000042080004044 0x1080184000018180 0x88400c200000c0c0

def z660 : W := mkw 0xa847587b41e985ea 0xd423ac3da0f4c2f5 0xf787d97fc5f991ff 0xfbc3ecbfe2fcc8ff

def z661 : W := mkw 0x802af000069d0001 0x40157800034e8000 0xbe7ef800079f8001 0xdf3f7c0003cfc000

def z662 : W := mkw 0x886ffc5147ddc0ab 0xc437fe28a3eee055 0xbe7ffe01c7ffe01f 0xdf3fff00e3fff00f

def z663 : W := mkw 0x60dd0bfff7601d41 0xb06e85fffbb00ea0 0xdfff01ffffe01fe0 0xefff80fffff00ff0

def z664 : W := mkw 0x747dabefbf76bfdd 0xba3ed5f7dfbb5fee 0xffffffffffffffff 0xffffffffffffffff

def z665 : W := mkw 0xd87ffdd1efdfdabf 0xec3ffee8f7efed5f 0xfffffff1ffffffff 0xfffffff8ffffffff

def z666 : W := mkw 0x605d0bef17601d41 0xb02e85f78bb00ea0 0xffff3fff3fe01fe0 0xffff9fff9ff00ff0

def z667 : W := mkw 0x10a2fe55f8160214 0x08517f2afc0b010a 0x2000fe01f81e001f 0x10007f00fc0f000f

def z668 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x1486d970c59991e6 0x8a436cb862ccc8f3

def z669 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x9e7f008e07e00e00 0xcf3f804703f00700

def z670 : W := mkw 0x0000000008020210 0x0000000004010108 0x8100000002060e19 0x408000000103070c

def z671 : W := mkw 0x00100180a0000000 0x000800c050000000 0x40000181f8000000 0x200000c0fc000000

def z672 : W := mkw 0x040000020822a798 0x02000001041153cc 0xbb013e000267ef99 0xdd809f000133f7cc

def z673 : W := mkw 0x8047540001c94000 0xc023aa0000e4a000 0x0006000001800000 0x0003000000c00000

def z674 : W := mkw 0x605d01a807401841 0xb02e80d403a00c20 0x9e7f013007e01060 0xcf3f809803f00830

def z675 : W := mkw 0x4038a18006141801 0x201c50c0030a0c00 0xef78e180061e1e01 0x77bc70c0030f0f00

def z676 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0x9e7f260007e66000 0xcf3f930003f33000

def z677 : W := mkw 0x8008000007dd4001 0xc004000003eea000 0x0000000005980000 0x0000000002cc0000

def z678 : W := mkw 0x8002500000890000 0x4001280000448000 0xbe07fe0007ffe001 0xdf03ff0003fff000

def z679 : W := mkw 0x04c75e7f5020a588 0x0263af3fa81052c4 0x10871e7e0061e180 0x88438f3f0030f0c0

def z680 : W := mkw 0x006ff40007544001 0x8037fa0003aa2000 0x3e7ffe0002666000 0x1f3fff0001333000

def z681 : W := mkw 0xc07ff58007dd5801 0xe03ffac003eeac00 0xff7fff8007fffe01 0xffbfffc003ffff00

def z682 : W := mkw 0x88000841008980aa 0x440004208044c055 0xf3801841059991ff 0xf9c00c2082ccc8ff

def z683 : W := mkw 0x500800000e161a15 0x28040000070b0d0a 0x0000000002060e00 0x0000000001030700

def z684 : W := mkw 0x8000000000890000 0x4000000000448000 0x8000000005998001 0xc000000002ccc000

def z685 : W := mkw 0x601001aa00201d40 0x300800d500100ea0 0xdb8101fe02601fe0 0xedc080ff01300ff0

def z686 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xe700d901c419901f 0x73806c80e20cc80f

def z687 : W := mkw 0x5008000006141805 0x28040000030a0c02 0x0000000004181006 0x00000000020c0803

def z688 : W := mkw 0x601801aa07601d41 0xb00c00d503b00ea0 0xc18001fe07e01fe0 0xe0c000ff03f00ff0

def z689 : W := mkw 0x88000000008980aa 0x440000000044c055 0xe700c101c59991ff 0xf3806080e2ccc8ff

def z690 : W := mkw 0x846ff4020fffe799 0xc237fa0107fff3cc 0xbf7ffe0007ffef99 0xdfbfff0003fff7cc

def z691 : W := mkw 0x50180180ae161a15 0x280c00c0570b0d0a 0xc1000181fe1e1e1f 0x608000c0ff0f0f0f

def z692 : W := mkw 0x8c6ffe575fffe7bb 0xc637ff2baffff3dd 0xffffffffffffffff 0xffffffffffffffff

def z693 : W := mkw 0x005501a800000000 0x002a80d400000000 0x047e013000000000 0x023f009800000000

def z694 : W := mkw 0x645d03ae1f623f51 0xb22e81d70fb11fa8 0x0879268e3a666e00 0x043c93471d333700

def z695 : W := mkw 0x00800a55f0000000 0x0040052af8000000 0x00000001f8000000 0x00000000fc000000

def z696 : W := mkw 0x0000085140000000 0x00000428a0000000 0x40800171c0000000 0x204000b8e0000000

def z697 : W := mkw 0x681009fb40209dea 0x340804fda0104ef5 0x418001ffc0001ffe 0x20c000ffe0000fff

def z698 : W := mkw 0x0000084100008088 0x0000042080004044 0x4180004100000198 0x20c00020800000cc

def z699 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x0c78e180fe1e1e06 0x063c70c07f0f0f03

def z700 : W := mkw 0x605501aa01601d40 0xb02a80d500b00ea0 0x518701fe01e01fe0 0xa8c380ff00f00ff0

def z701 : W := mkw 0x8028a00007dd4001 0xc014500003eea000 0xae78e00007ffe001 0xd73c700003fff000

def z702 : W := mkw 0x0002585140000000 0x00012c28a0000000 0x1086187000000000 0x08430c3800000000

def z703 : W := mkw 0x0000000200200500 0x0000000100100280 0x0801008e02600e00 0x0400804701300700

def z704 : W := mkw 0x004d000207600501 0x8026800103b00280 0xdfff00ce07e00f80 0xefff806703f007c0

def z705 : W := mkw 0x4010018000001800 0x200800c000000c00 0x4100018000001e00 0x208000c000000f00

def z706 : W := mkw 0xe85f51b847c91863 0xf42fa8dc23e48c31 0x047ec130c5981066 0x023f609862cc0833

def z707 : W := mkw 0x50cf5e7d5e161a15 0x2867af3eaf0b0d0a 0x91871e7e061e1e1f 0x48c38f3f030f0f0f

def z708 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x7a813ecf3a67ee19 0x3d409f679d33f70c

def z709 : W := mkw 0xac475a7f51e9a5ea 0xd623ad3fa8f4d2f5 0x10871e7e01e1e1e0 0x88438f3f00f0f0f0

def z710 : W := mkw 0x006ff40007400001 0x8037fa0003a00000 0xbe7ffe0007e7e001 0xdf3fff0003f3f000

def z711 : W := mkw 0x08f7fffdf00080aa 0x047bfffef8004055 0xfffffffffc1811ff 0x7ffffffffe0c08ff

def z712 : W := mkw 0x00b0abfdf0000000 0x005855fef8000000 0x48f821fff8000000 0x247c10fffc000000

def z713 : W := mkw 0x8067f40000890000 0x4033fa0000448000 0xbe7ffe0007ffe001 0xdf3fff0003fff000

def z714 : W := mkw 0x00f7f7acb0000000 0x007bfbd658000000 0x0c7fe68e38000000 0x063ff3471c000000

def z715 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbf7ffe0007fff1e1 0xdfbfff0003fff8f0

def z716 : W := mkw 0xd83af9d1ee9f9abf 0x6c1d7ce8f74fcd5f 0x18fe38f03b878fe0 0x8c7f1c781dc3c7f0

def z717 : W := mkw 0x04f7f5bae822a798 0x027bfadd741153cc 0x857ec130c267ef99 0xc2bf60986133f7cc

def z718 : W := mkw 0x0075a1a8a0000000 0x003ad0d450000000 0x0879208e38000000 0x043c90471c000000

def z719 : W := mkw 0xe85f59fb47e99deb 0xf42facfda3f4cef5 0x2879d88fc2798e1f 0x143cec47e13cc70f

def z720 : W := mkw 0x60aafe57f7601d41 0xb0557f2bfbb00ea0 0xa100fe01ffe01fe0 0xd0807f00fff00ff0

def z721 : W := mkw 0x08000851400080aa 0x04000428a0004055 0xf786c171c59811ff 0xfbc360b8e2cc08ff

def z722 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x2e79e68e38000000 0x173cf3471c000000

def z723 : W := mkw 0xa8c75e7f51e985ea 0xd463af3fa8f4c2f5 0x10871e7e01e181e0 0x88438f3f00f0c0f0

def z724 : W := mkw 0x74100befb822bfdc 0x3a0805f7dc115fee 0x418001fff8001ffe 0x20c000fffc000fff

def z725 : W := mkw 0x1030a180a8160214 0x081850c0540b010a 0xef78e181fa1e0e1f 0x77bc70c0fd0f070f

def z726 : W := mkw 0x88f5a7acb08980aa 0x447ad3d65844c055 0x8979268e3d9991ff 0xc4bc93471eccc8ff

def z727 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffff8000180 0xfffffffffc0000c0

def z728 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xba79fe00027fe001 0xdd3cff00013ff000

def z729 : W := mkw 0x601801aa06201d41 0x300c00d503100ea0 0xdffe01fe07801fe0 0xefff00ff03c00ff0

def z730 : W := mkw 0xd0575580a9cb5a14 0xe82baac054e5ad0a 0x51071f81f9e1fe1e 0xa8838fc0fcf0ff0f

def z731 : W := mkw 0x88000000008980aa 0x440000000044c055 0xf786c171c59991ff 0xfbc360b8e2ccc8ff

def z732 : W := mkw 0x0030abc5b0008088 0x001855e2d8004044 0xfff9ffcffc19919f 0xfffcffe7fe0cc8cf

def z733 : W := mkw 0x204d002a07600541 0x9026801503b002a0 0xdfff00fe07e00fe0 0xefff807f03f007f0

def z734 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x5effe7fef8000000 0x2f7ff3ff7c000000

def z735 : W := mkw 0x740800020f76bfdd 0xba04000107bb5fee 0x8100000007ffffff 0xc080000003ffffff

def z736 : W := mkw 0x80f7fffdf09d4000 0x407bfffef84ea000 0x7efffffff8180000 0x3f7ffffffc0c0000

def z737 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xcf78c181fe181e1e 0x67bc60c0ff0c0f0f

def z738 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7af9fecff8000000 0x3d7cff67fc000000

def z739 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xe778c181fc181e1f 0x73bc60c0fe0c0f0f

def z740 : W := mkw 0xa06ff42807dd4041 0xd037fa1403eea020 0xbe7ffe3007ffe061 0xdf3fff1803fff030

def z741 : W := mkw 0x846ffe471fffe799 0xc237ff238ffff3cc 0x45fec0cf3d980f98 0x22ff60679ecc07cc

def z742 : W := mkw 0x00b2fffdf0000000 0x00597ffef8000000 0x6ef8fffff8000000 0x377c7ffffc000000

def z743 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xff79e181fe7e1e1f 0xffbcf0c0ff3f0f0f

def z744 : W := mkw 0xec0a58534febbffb 0xf6052c29a7f5dffd 0xf786d971c7ffffff 0xfbc36cb8e3ffffff

def z745 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x08013e8e3a67ee00 0x04009f471d33f700

def z746 : W := mkw 0x0c000a575822a7ba 0x0600052bac1153dd 0xfb813ecffa67ef9f 0xfdc09f67fd33f7cf

def z747 : W := mkw 0x64100bef1822bfd8 0x320805f78c115fec 0x418000cf38000f98 0x20c000679c0007cc

def z748 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x6f78e181fc181e1e 0x37bc70c0fe0c0f0f

def z749 : W := mkw 0x5038a1a8ae161a15 0x281c50d4570b0d0a 0xeff8e1fffe1e1e1f 0x77fc70ffff0f0f0f

def z750 : W := mkw 0x040002061822a798 0x020001030c1153cc 0xbb013e8e3a67ef99 0xdd809f471d33f7cc

def z751 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff873ecf3fe7ef99 0xffc39f679ff3f7cc

def z752 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xa47efe0007ffe001 0xd23f7f0003fff000

def z753 : W := mkw 0x00575bfd50000000 0x002badfea8000000 0x7efffffff8000000 0x3f7ffffffc000000

def z754 : W := mkw 0x8c02521658ab2732 0x4601290b2c559399 0x0c07e7befffe7e66 0x0603f3df7fff3f33

def z755 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7efffffff99981ff 0xbf7ffffffcccc0ff

def z756 : W := mkw 0x80f7fffdf0894000 0x407bfffef844a000 0x7efffffff801e000 0x3f7ffffffc00f000

def z757 : W := mkw 0xe032f5aa00bd5d40 0x70197ad5005eaea0 0x6180fffe001fffe1 0x30c07fff000ffff0

def z758 : W := mkw 0x6c100bff5822bffa 0x360805ffac115ffd 0x418001fff8001ffe 0x20c000fffc000fff

def z759 : W := mkw 0x88025010408980aa 0x440128082044c055 0xb706d930c59991ff 0xdb836c9862ccc8ff

def z760 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x1cff01fe07e01fe0 0x8e7f80ff03f00ff0

def z761 : W := mkw 0x8802501040890022 0x4401280820448011 0xf786c171c59811ff 0xfbc360b8e2cc08ff

def z762 : W := mkw 0x88b2fbfdf08980aa 0x44597dfef844c055 0xfffef9fffd9991ff 0xffff7cfffeccc8ff

def z763 : W := mkw 0x5438abc7b634bd8d 0x2a1c55e3db1a5ec6 0x14f9df4ec479f186 0x8a7cefa7623cf8c3

def z764 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff87ffffffffffff 0xffc3ffffffffffff

def z765 : W := mkw 0x0030a384b0000000 0x001851c258000000 0x6e79e78ff8000000 0x373cf3c7fc000000

def z766 : W := mkw 0x004d000207600501 0x8026800103b00280 0xdfff01fe07e01fe0 0xefff80ff03f00ff0

def z767 : W := mkw 0x8cc75e7f50a9a5aa 0x4663af3fa854d2d5 0x10871e7e01e1e1e0 0x88438f3f00f0f0f0

def z768 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7ffffffff98191fe 0xbffffffffcc0c8ff

def z769 : W := mkw 0x700800020f761f55 0xb804000107bb0faa 0xf786c171c7fe1fff 0xfbc360b8e3ff0fff

def z770 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0xfffffffffc19919f 0xfffffffffe0cc8cf

def z771 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x0879268e3a666000 0x043c93471d333000

def z772 : W := mkw 0x3065a02aa9760754 0x9832d01554bb03aa 0x3087e07ff9fe01ff 0x9843f03ffcff00ff

def z773 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x347ffe0005ffe001 0x9a3fff0002fff000

def z774 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x6586d971c59991ff 0x32c36cb8e2ccc8ff

def z775 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfff01fe07e7ffe1 0xefff80ff03f3fff0

def z776 : W := mkw 0x00550bed10008088 0x002a85f688004044 0xffff3fff3d8191f9 0xffff9fff9ec0c8fc

def z777 : W := mkw 0x60f7fffdf0001840 0x307bfffef8000c20 0x7efffffff8001060 0x3f7ffffffc000830

def z778 : W := mkw 0x040800020e36a799 0x02040001071b53cc 0x81000000067fef99 0xc0800000033ff7cc

def z779 : W := mkw 0x5030a180a8021a14 0x281850c054010d0a 0xef78e181fc181e1f 0x77bc70c0fe0c0f0f

def z780 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xff7ffe0107ffe019 0xffbfff0083fff00c

def z781 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfff27fe07e67fe0 0xefff93ff03f33ff0

def z782 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x387ffe0003ffe001 0x9c3fff0001fff000

def z783 : W := mkw 0x040800020f76e799 0x8204000107bb73cc 0x810000000267ef99 0xc08000000133f7cc

def z784 : W := mkw 0xdc0800020ebfbfbf 0x6e040001075fdfdf 0x8100000007ffffff 0xc080000003ffffff

def z785 : W := mkw 0x640800020f623f51 0xb204000107b11fa8 0x8100000007e67fe0 0xc080000003f33ff0

def z786 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xf7fed9fffd9991ff 0xfbff6cfffeccc8ff

def z787 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xef78ff81fe1ffe1f 0x77bc7fc0ff0fff0f

def z788 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xd786c171c59811fe 0xebc360b8e2cc08ff

def z789 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfffffffffc19901f 0x7ffffffffe0cc80f

def z790 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7ffffffff800101e 0x3ffffffffc00080f

def z791 : W := mkw 0x88f7fffdf1c9c0aa 0xc47bfffef8e4e055 0xfffffffffdf9f1ff 0xfffffffffefcf8ff

def z792 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0xdfff27fe3d8011e0 0xefff93ff1ec008f0

def z793 : W := mkw 0x00f7f7acb0000000 0x007bfbd658000000 0x187f3e8e38000000 0x0c3f9f471c000000

def z794 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x68f9fffff8000000 0x347cfffffc000000

def z795 : W := mkw 0x0c900bfff822a7ba 0x064805fffc1153dd 0x418001fff8001ffe 0x20c000fffc000fff

def z796 : W := mkw 0x20f7fffdf1400040 0x907bfffef8a00020 0x7efffffff9800060 0x3f7ffffffcc00030

def z797 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x18ff26fe38000000 0x0c7f937f1c000000

def z798 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0xba793e8e3a67e001 0xdd3c9f471d33f000

def z799 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x3a793e8e38000000 0x1d3c9f471c000000

def z800 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0x7efffffffd980000 0x3f7ffffffecc0000

def z801 : W := mkw 0x645d0bed1f42bad9 0xb22e85f68fa15d6c 0x247e3f313d87f079 0x123f1f989ec3f83c

def z802 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfefffffffc180001 0x7f7ffffffe0c0000

def z803 : W := mkw 0x886ff40007dd4023 0xc437fa0003eea011 0xbe7ffe0007fff067 0xdf3fff0003fff833

def z804 : W := mkw 0x0c000a471822a7ba 0x060005238c1153dd 0xfb813ecf3a67ffff 0xfdc09f679d33ffff

def z805 : W := mkw 0x88025010408980aa 0x440128082044c055 0x0506c130c59811fe 0x0283609862cc08ff

def z806 : W := mkw 0x80980bfdf7dd4001 0xc04c05fefbeea000 0xc08001ffffffe001 0xe04000fffffff000

def z807 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x9e7f3e0007e7e000 0xcf3f9f0003f3f000

def z808 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x6e7fe7bff8000000 0x373ff3dffc000000

def z809 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xf786ff71c59ff1ff 0xfbc37fb8e2cff8ff

def z810 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x4879278ff8000000 0x243c93c7fc000000

def z811 : W := mkw 0x8877f9f9e08980aa 0x443bfcfcf044c055 0xfffff9fffd9991ff 0xfffffcfffeccc8ff

def z812 : W := mkw 0x8ca2fe55f88ba2ba 0x46517f2afc45d15d 0x2000fe01f81fe01f 0x10007f00fc0ff00f

def z813 : W := mkw 0x0032fbd5f0000000 0x00197deaf8000000 0x7efffffff8000000 0x3f7ffffffc000000

def z814 : W := mkw 0x0400020618222710 0x020001030c111388 0x28013e8e3a67ee01 0x14009f471d33f700

def z815 : W := mkw 0x88025010408980aa 0x440128082044c055 0xd786c170c59991ff 0xebc360b862ccc8ff

def z816 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x3e7ffe00027fe001 0x1f3fff00013ff000

def z817 : W := mkw 0x605501aa00201d40 0x302a80d500100ea0 0xdfff01fe05801fe0 0xefff80ff02c00ff0

def z818 : W := mkw 0x00f5afedb0000000 0x007ad7f6d8000000 0x48f926cf38000000 0x247c93679c000000

def z819 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x4e79278e38000000 0x273c93c71c000000

def z820 : W := mkw 0x88f7fffdf09dc0aa 0x447bfffef84ee055 0x7efffffff81fe01f 0x3f7ffffffc0ff00f

def z821 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xff7fff0007fff001 0xffbfff8003fff800

def z822 : W := mkw 0x80eff410e7dd4001 0xc077fa0873eea000 0xbe7ffe00c7ffe001 0xdf3fff0063fff000

def z823 : W := mkw 0xc06ff40007dd5801 0xe037fa0003eeac00 0xbf7ffe0007fffe01 0xdfbfff0003ffff00

def z824 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffff8000019 0x7ffffffffc00000c

def z825 : W := mkw 0x700800020f761f55 0xb804000107bb0faa 0x8100000007e61fe0 0xc080000003f30ff0

def z826 : W := mkw 0xd0fff5b8e7dd5805 0xe87ffadc73eeac02 0x047ec130c5981006 0x023f609862cc0803

def z827 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x7a813ecf3a67ef80 0xbd409f679d33f7c0

def z828 : W := mkw 0x00f7fffdf1404000 0x807bfffef8a02000 0x7efffffff8606000 0x3f7ffffffc303000

def z829 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xae78e081fe1e0e1f 0x573c7040ff0f070f

def z830 : W := mkw 0x0020a00000000000 0x0010500000000000 0xbe79fe000267e001 0xdf3cff000133f000

def z831 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xfff9e1cffe1e1e1f 0x7ffcf0e7ff0f0f0f

def z832 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x45fec1fffd9811fe 0x22ff60fffecc08ff

def z833 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0x28793e000267e001 0x143c9f000133f000

def z834 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfefffffffd800000 0xff7ffffffec00000

def z835 : W := mkw 0x00b0a3acb0000000 0x005851d658000000 0x6e78e18ff8000000 0x373c70c7fc000000

def z836 : W := mkw 0x600800020f621f51 0xb004000107b10fa8 0x8100000007e61ff9 0xc080000003f30ffc

def z837 : W := mkw 0x00f7f7acb0000000 0x007bfbd658000000 0x7efffffe38000000 0x3f7fffff1c000000

def z838 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x5eff01fe03e00fe0 0xaf7f80ff01f007f0

def z839 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x9eff00fe07e00fe0 0xcf7f807f03f007f0

def z840 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x0c79e78ef8000000 0x063cf3c77c000000

def z841 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xcffe01fe07801fe0 0x67ff00ff03c00ff0

def z842 : W := mkw 0x88f7fffdf0890022 0x447bfffef8448011 0xfffffffffd98107f 0x7ffffffffecc083f

def z843 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7efffffffd9991e6 0xbf7ffffffeccc8f3

def z844 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xd7fe01fe05801fe0 0xebff00ff02c00ff0

def z845 : W := mkw 0x540800020e363f15 0x2a040001071b1f8a 0x81000000067e7e1f 0x40800000033f3f0f

def z846 : W := mkw 0xf00800020fff5f55 0xf804000107ffafaa 0x8100000007ffffff 0xc080000003ffffff

def z847 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff87ff71c59991ff 0xffc3ffb8e2ccc8ff

def z848 : W := mkw 0x605501aa01601d40 0xb02a80d500b00ea0 0x5fff01fe01e01fe0 0xafff80ff00f00ff0

def z849 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x34ffff7ff8000000 0x1a7fffbffc000000

def z850 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffffc001000 0x7ffffffffe000800

def z851 : W := mkw 0x405d01a806001801 0x202e80d403000c00 0xdfff01fe07801fe0 0xefff80ff03c00ff0

def z852 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfffffffff819819f 0xfffffffffc0cc0cf

def z853 : W := mkw 0x0030abc5b0000000 0x001855e2d8000000 0x7af93ecf38000000 0x3d7c9f679c000000

def z854 : W := mkw 0x88f7fffdf1c9c0aa 0xc47bfffef8e4e055 0x7efffffff9e1e1e0 0xbf7ffffffcf0f0f0

def z855 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffff861e000 0xbf7ffffffc30f000

def z856 : W := mkw 0x5038a580ae165a15 0x281c52c0570b2d0a 0xef78e781fe1e7e1f 0x77bc73c0ff0f3f0f

def z857 : W := mkw 0x806da40007dd4001 0xc036d20003eea000 0xba793e0007ffe001 0xdd3c9f0003fff000

def z858 : W := mkw 0x00550bed10000000 0x002a85f688000000 0x5eff01ff38000000 0x2f7f80ff9c000000

def z859 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0xef79e78ffc18101f 0x77bcf3c7fe0c080f

def z860 : W := mkw 0x00b0abfdf0000000 0x005855fef8000000 0x44f8c1fff8000000 0x227c60fffc000000

def z861 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x5fff01fe05801fe0 0x2fff80ff02c00ff0

def z862 : W := mkw 0x005501aa00200500 0x002a80d500100280 0xdfff01fe07e01fe0 0xefff80ff03f00ff0

def z863 : W := mkw 0x00d75bfdf0000000 0x006badfef8000000 0x7effd9fff8000000 0x3f7fecfffc000000

def z864 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x5eff3ffe38000000 0x2f7f9fff1c000000

def z865 : W := mkw 0x605d01aa07741d41 0xb02e80d503ba0ea0 0xdfff01fe07fe1fe1 0xefff80ff03ff0ff0

def z866 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffffa000e00 0x7ffffffffd000700

def z867 : W := mkw 0x8c475e5751e9e5aa 0xc623af2ba8f4f2d5 0x10871e7e01e1e1e0 0x88438f3f00f0f0f0

def z868 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x047ec1bef8000000 0x023f60df7c000000

def z869 : W := mkw 0x006ff40007544001 0x8037fa0003aa2000 0xbe7ffe000267e001 0xdf3fff000133f000

def z870 : W := mkw 0x0030abc5b0000000 0x001855e2d8000000 0x6ef8e1cff8000000 0x377c70e7fc000000

def z871 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xa578e101fe1e1e1f 0x52bc7080ff0f0f0f

def z872 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffff19fe07e19fe1 0xffff8cff03f0cff0

def z873 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x2879e68ff8000000 0x143cf347fc000000

def z874 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffff3ffe07e01fe0 0xffff9fff03f00ff0

def z875 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff81fecf3e7fef99 0xffc0ff679f3ff7cc

def z876 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x59813ecf3a67ef98 0xacc09f679d33f7cc

def z877 : W := mkw 0x0030a180a8020210 0x001850c054010108 0xef78e181fe1e1e1f 0x77bc70c0ff0f0f0f

def z878 : W := mkw 0x88025a55508980aa 0x44012d2aa844c055 0xf786d9fffd9991ff 0xfbc36cfffeccc8ff

def z879 : W := mkw 0x540800020e363f15 0x2a040001071b1f8a 0x0000000002666e00 0x0000000001333700

def z880 : W := mkw 0x0065a60410000000 0x0032d30208000000 0x0879268e38000000 0x043c93471c000000

def z881 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0xfffffffffd8191f9 0xfffffffffec0c8fc

def z882 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbe7fff3007fff061 0xdf3fff9803fff830

def z883 : W := mkw 0x00f5a7acb1404000 0x807ad3d658a02000 0x0879268e38606000 0x043c93471c303000

def z884 : W := mkw 0x00b2fbfdf0000000 0x00597dfef8000000 0x7efef9fff8000000 0x3f7f7cfffc000000

def z885 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xc586c171c59991ff 0xe2c360b8e2ccc8ff

def z886 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfefffffffd9981e1 0xff7ffffffeccc0f0

def z887 : W := mkw 0x0030a1a8a0000000 0x001850d450000000 0x6ef8e1fff8000000 0x377c70fffc000000

def z888 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x18ff3efe398181e0 0x8c7f9f7f1cc0c0f0

def z889 : W := mkw 0x00f7fffdf0140000 0x007bfffef80a0000 0x7efffffff81e0001 0x3f7ffffffc0f0000

def z890 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xff7ee181ff9e1e1f 0xffbf70c0ffcf0f0f

def z891 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7aff3eff38000000 0x3d7f9f7f9c000000

def z892 : W := mkw 0x006ff40006140001 0x0037fa00030a0000 0xbe7ffe00067fe001 0xdf3fff00033ff000

def z893 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xef7ee1b1ff9e1e7f 0x77bf70d8ffcf0f3f

def z894 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffff818001f 0x3f7ffffffc0c000f

def z895 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfffffffffd8191e0 0xfffffffffec0c8f0

def z896 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0x7efffffff9818000 0xbf7ffffffcc0c000

def z897 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x0879268ff8000000 0x043c9347fc000000

def z898 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x6978e181fa1e1e1f 0x34bc70c0fd0f0f0f

def z899 : W := mkw 0x040800020f766711 0x8204000107bb3388 0x0000000002666e00 0x0000000001333700

def z900 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x0078008e38000000 0x003c00471c000000

def z901 : W := mkw 0x8002500000890000 0x4001280000448000 0xf786d971c59991ff 0xfbc36cb8e2ccc8ff

def z902 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffff98001e0 0xbf7ffffffcc000f0

def z903 : W := mkw 0x08f7fffdf00080aa 0x047bfffef8004055 0xfffffffffd8011fe 0xfffffffffec008ff

def z904 : W := mkw 0x700800020f761f55 0xb804000107bb0faa 0x81000000067e1e1f 0x40800000033f0f0f

def z905 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbf7ffe0007fff01f 0xdfbfff0003fff80f

def z906 : W := mkw 0x00b0abfdf0000000 0x005855fef8000000 0x7ef9fffff8000000 0x3f7cfffffc000000

def z907 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x6efee1fff8000000 0x377f70fffc000000

def z908 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x947fde0007ffe001 0xca3fef0003fff000

def z909 : W := mkw 0x00d503acb0000000 0x006a81d658000000 0x0879008e38000000 0x043c80471c000000

def z910 : W := mkw 0x08f7fffdf00080aa 0x047bfffef8004055 0x7efffffff80001e0 0x3f7ffffffc0000f0

def z911 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0x7efffffff8198001 0x3f7ffffffc0cc000

def z912 : W := mkw 0x64900bfff822bfd8 0x324805fffc115fec 0x418001fff8001ff8 0x20c000fffc000ffc

def z913 : W := mkw 0x8867fe55508980aa 0x4433ff2aa844c055 0xfffffffffd9991ff 0xfffffffffeccc8ff

def z914 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x3e7fffbef8000000 0x1f3fffdf7c000000

def z915 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x38fffefff8000000 0x1c7fff7ffc000000

def z916 : W := mkw 0x88d75bfdf08980aa 0x446badfef844c055 0xffffd9fffd9991ff 0xffffecfffeccc8ff

def z917 : W := mkw 0x7038a180af561a55 0xb81c50c057ab0d2a 0xef78e181ff9e1e7f 0x77bc70c0ffcf0f3f

def z918 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfffc1fec7f81fe6 0xefffe0ff63fc0ff3

def z919 : W := mkw 0x401801800e021a11 0x200c00c007010d08 0xef78e181fe1e1e1f 0x77bc70c0ff0f0f0f

def z920 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7ffffffff80011e0 0x3ffffffffc0008f0

def z921 : W := mkw 0x00f5afedb0000000 0x007ad7f6d8000000 0x18f93ece38000000 0x0c7c9f671c000000

def z922 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffffc181006 0x3f7ffffffe0c0803

def z923 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfefffffffa600000 0xff7ffffffd300000

def z924 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x3efffefe38000000 0x1f7fff7f1c000000

def z925 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xff79ff81fe1e1e1f 0x7fbcffc0ff0f0f0f

def z926 : W := mkw 0xf80a58534fff9fff 0xfc052c29a7ffcfff 0xf786d971c7ff9fff 0xfbc36cb8e3ffcfff

def z927 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x95ff017e07e01fe0 0xcaff80bf03f00ff0

def z928 : W := mkw 0x840a58430fffe799 0xc2052c2187fff3cc 0xf786d84107ffef99 0xfbc36c2083fff7cc

def z929 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x1c7ffe0007ffe000 0x8e3fff0003fff000

def z930 : W := mkw 0x0008000006000001 0x0004000003000000 0xbe793e000667e001 0xdf3c9f000333f000

def z931 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x08793e000267e000 0x043c9f000133f000

def z932 : W := mkw 0x005501a8a0000000 0x002a80d450000000 0x5eff01fff8000000 0x2f7f80fffc000000

def z933 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x3486d971c59991ff 0x9a436cb8e2ccc8ff

def z934 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x38813ecf3a67ef99 0x9c409f679d33f7cc

def z935 : W := mkw 0x0065a40000000000 0x0032d20000000000 0xba793e000267e001 0xdd3c9f000133f000

def z936 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff87d971c7f991ff 0xffc3ecb8e3fcc8ff

def z937 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x4cffe7fff8000000 0x267ff3fffc000000

def z938 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x6e79ff8ff8000000 0x373cffc7fc000000

def z939 : W := mkw 0x040800020f62a799 0x8204000107b153cc 0x8100000007e7ef99 0xc080000003f3f7cc

def z940 : W := mkw 0x00f5afedb0008088 0x007ad7f6d8004044 0xfbf93ecf38018199 0xfdfc9f679c00c0cc

def z941 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff86f971c79f91ff 0xffc37cb8e3cfc8ff

def z942 : W := mkw 0x00d75ffdf0000000 0x006baffef8000000 0x5eff1ffff8000000 0x2f7f8ffffc000000

def z943 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x6ef9e7fff8000000 0x377cf3fffc000000

def z944 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x1e7f268e38000000 0x0f3f93471c000000

def z945 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfff01ffc7e01ffe 0xefff80ffe3f00fff

def z946 : W := mkw 0x886ff41047dd4023 0xc437fa0823eea011 0xbe7ffe3007ffe061 0xdf3fff1803fff030

def z947 : W := mkw 0x80f7fffdf1c94000 0xc07bfffef8e4a000 0xfefffffffdf9e001 0xff7ffffffefcf000

def z948 : W := mkw 0x640800020f62bfd9 0xb204000107b15fec 0x810000000267ef99 0xc08000000133f7cc

def z949 : W := mkw 0x086dac514754c0ab 0x8436d628a3aa6055 0x49f92771c26671fe 0x24fc93b8e13338ff

def z950 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x3e7ffe0003e7e000 0x9f3fff0001f3f000

def z951 : W := mkw 0x5038a180af565a15 0xa81c50c057ab2d0a 0xef78e181fe7e7e1f 0x77bc70c0ff3f3f0f

def z952 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x5effc1fff8000000 0x2f7fe0fffc000000

def z953 : W := mkw 0x700800020f621f55 0xb804000107b10faa 0x8100000007e01ffe 0xc080000003f00fff

def z954 : W := mkw 0x5028a000ae161a15 0x28145000570b0d0a 0xaf78e001fe1e1e1f 0x57bc7000ff0f0f0f

def z955 : W := mkw 0x8067fe4510898088 0x4033ff228844c044 0xfffffecf3d998199 0xffffff679eccc0cc

def z956 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xe786c171c59811ff 0x73c360b8e2cc08ff

def z957 : W := mkw 0x80f7fffdf1c94000 0xc07bfffef8e4a000 0xfefffffffbe7e001 0xff7ffffffdf3f000

def z958 : W := mkw 0x0028a0000e160211 0x00145000070b0108 0xef78e181fe1e1e1f 0x77bc70c0ff0f0f0f

def z959 : W := mkw 0x08f7fffdf00080aa 0x047bfffef8004055 0x7efffffff800001e 0x3f7ffffffc00000f

def z960 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xf787df71c5f9f1ff 0xfbc3efb8e2fcf8ff

def z961 : W := mkw 0x1028a000ae160215 0x08145000570b010a 0xef78e081fe1e0e1f 0x77bc7040ff0f070f

def z962 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfefffffff8018001 0xff7ffffffc00c000

def z963 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x2879fe8ff819801f 0x143cff47fc0cc00f

def z964 : W := mkw 0x005503ac10000000 0x002a81d608000000 0x0879268e38000000 0x043c93471c000000

def z965 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xc5fe01fe07e01fe0 0xe2ff00ff03f00ff0

def z966 : W := mkw 0x80f7fffdf1dd4000 0xc07bfffef8eea000 0x7efffffff9ffe001 0xbf7ffffffcfff000

def z967 : W := mkw 0x04100bc7b822a798 0x020805e3dc1153cc 0x418001cff8000f98 0x20c000e7fc0007cc

def z968 : W := mkw 0x804f540007c94001 0xc027aa0003e4a000 0xbe7f3e0007e7e001 0xdf3f9f0003f3f000

def z969 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xfefffece07ffe001 0xff7fff6703fff000

def z970 : W := mkw 0x605d01aaa7601d41 0xb02e80d553b00ea0 0xdfff01ffffe01fe0 0xefff80fffff00ff0

def z971 : W := mkw 0x605d01aa07745d41 0xb02e80d503ba2ea0 0xdfff01fe07e67fe0 0xefff80ff03f33ff0

def z972 : W := mkw 0x00f7ffedb0000000 0x007bfff6d8000000 0x7efffecf38000000 0x3f7fff679c000000

def z973 : W := mkw 0x0045000000000000 0x0022800000000000 0xbe7f3e000267e001 0xdf3f9f000133f000

def z974 : W := mkw 0x5c100bd7f822bfbe 0x2e0805ebfc115fdf 0x418001fff8001ffe 0x20c000fffc000fff

def z975 : W := mkw 0x0c000a575822a7ba 0x0600052bac1153dd 0xfb813eff3a67eff9 0xfdc09f7f9d33f7fc

def z976 : W := mkw 0xd40800020fffff9d 0xea04000107ffffce 0x8100000007ffff9f 0xc080000003ffffcf

def z977 : W := mkw 0x00d75ffd50000000 0x006baffea8000000 0x7eff3fff38000000 0x3f7f9fff9c000000

def z978 : W := mkw 0xe40800020fffffd9 0xf204000107ffffec 0x8100000007fffff9 0xc080000003fffffc

def z979 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x4dff01fe07e01fe0 0x26ff80ff03f00ff0

def z980 : W := mkw 0x4038a180a6001801 0x201c50c053000c00 0xef78e181fe181e1f 0x77bc70c0ff0c0f0f

def z981 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x55ff01fe05e01fe0 0xaaff80ff02f00ff0

def z982 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffff21ff3fe01fe0 0xffff90ff9ff00ff0

def z983 : W := mkw 0x705d01aa07741d45 0xb82e80d503ba0ea2 0xdfff01fe07f81fe6 0xefff80ff03fc0ff3

def z984 : W := mkw 0x88025c514089c0aa 0x44012e28a044e055 0xf786df71c599f1ff 0xfbc36fb8e2ccf8ff

def z985 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x0c7f27be38000000 0x063f93df1c000000

def z986 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xffffff71c7fff1ff 0xffffffb8e3fff8ff

def z987 : W := mkw 0x98a2fe55f89f82be 0x4c517f2afc4fc15f 0x2000fe01f81f801f 0x10007f00fc0fc00f

def z988 : W := mkw 0x00f5afedb0000000 0x007ad7f6d8000000 0x28793e8f38000000 0x143c9f479c000000

def z989 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff87d9ffc59991ff 0xffc3ecffe2ccc8ff

def z990 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0xbe79fe00067fe001 0xdf3cff00033ff000

def z991 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7efffffff8018000 0x3f7ffffffc00c000

def z992 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb813fcffa67ff9f 0xfdc09fe7fd33ffcf

def z993 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfffffffffffff1ff 0xfffffffffffff8ff

def z994 : W := mkw 0x886ff41047dd4023 0xc437fa0823eea011 0xff7fff31c7fff07f 0xffbfff98e3fff83f

def z995 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xfffffe4007ffe181 0xffffff2003fff0c0

def z996 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0xfffffffffd99901f 0xfffffffffeccc80f

def z997 : W := mkw 0x0075a1a8a0000000 0x003ad0d450000000 0x5eff21fe38000000 0x2f7f90ff1c000000

def z998 : W := mkw 0x604d002a07601d41 0xb026801503b00ea0 0x9fff007e07e01fe0 0xcfff803f03f00ff0

def z999 : W := mkw 0x00000a4710200500 0x0000052388100280 0xfb813ecf3a67ef81 0xfdc09f679d33f7c0

def z1000 : W := mkw 0x88f7f7bcf0890022 0x447bfbde78448011 0x0c7fe7befd981066 0x063ff3df7ecc0833

def z1001 : W := mkw 0xec0800020febbffb 0xf604000107f5dffd 0x8100000007ffffff 0xc080000003ffffff

def z1002 : W := mkw 0x00f7f7acb0000000 0x007bfbd658000000 0x2879fe8e38000000 0x143cff471c000000

def z1003 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x58ff3ffff8000000 0x2c7f9ffffc000000

def z1004 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0xfffffffffa67e199 0xfffffffffd33f0cc

def z1005 : W := mkw 0x08f7fffdf00080aa 0x047bfffef8004055 0xfffffffff80191ff 0xfffffffffc00c8ff

def z1006 : W := mkw 0x802af40007dd4001 0xc0157a0003eea000 0xae78fe0007ffe001 0xd73c7f0003fff000

def z1007 : W := mkw 0x00d50bfdf0000000 0x006a85fef8000000 0x44fe01fff8000000 0x227f00fffc000000

def z1008 : W := mkw 0x8c0a58534fffe7bb 0xc6052c29a7fff3dd 0xf786d971c7ffffff 0xfbc36cb8e3ffffff

def z1009 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x7af93ffff8000000 0x3d7c9ffffc000000

def z1010 : W := mkw 0x8067f40001dd4000 0xc033fa0000eea000 0x3e7ffe0001ffe001 0x9f3fff0000fff000

def z1011 : W := mkw 0x0030a384b0000000 0x001851c258000000 0x0879268e38000000 0x043c93471c000000

def z1012 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0xbe7f3e0007e7e001 0xdf3f9f0003f3f000

def z1013 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffffd801060 0x3f7ffffffec00830

def z1014 : W := mkw 0x04000a575822a798 0x0200052bac1153cc 0xfb813ffffa67ef99 0xfdc09ffffd33f7cc

def z1015 : W := mkw 0x0075abedb0000000 0x003ad5f6d8000000 0x7efffffff8000000 0x3f7ffffffc000000

def z1016 : W := mkw 0x70fda7aebf761f55 0xb87ed3d75fbb0faa 0x0879268e3a660e00 0x043c93471d330700

def z1017 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffff807e001 0x3f7ffffffc03f000

def z1018 : W := mkw 0xf80800020fff9fff 0xfc04000107ffcfff 0x8100000007ff9fff 0xc080000003ffcfff

def z1019 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xdb813ece3a67ef80 0xedc09f671d33f7c0

def z1020 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xef78e181fe7ffe1f 0xf7bc70c0ff3fff0f

def z1021 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x1cfffffef8000000 0x0e7fffff7c000000

def z1022 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xef79e781fe7e7e1f 0x77bcf3c0ff3f3f0f

def z1023 : W := mkw 0x0067f60410000000 0x0033fb0208000000 0x3e7ffe8e38000000 0x1f3fff471c000000

def z1024 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xeb013e8f3a67ee19 0x75809f479d33f70c

def z1025 : W := mkw 0x88f7fffdf0890022 0x447bfffef8448011 0xfefffffffd999067 0xff7ffffffeccc833

def z1026 : W := mkw 0x4018018206201d01 0x200c00c103100e80 0xdfff01fe07e01fe0 0xefff80ff03f00ff0

def z1027 : W := mkw 0x0467f4020822a798 0x0233fa01041153cc 0xbf7ffe000267ef99 0xdfbfff000133f7cc

def z1028 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xf786d971c7fff1ff 0xfbc36cb8e3fff8ff

def z1029 : W := mkw 0x00000a4518020210 0x000005228c010108 0xfb813ecf3a67ee19 0xfdc09f679d33f70c

def z1030 : W := mkw 0x04000a4718222710 0x020005238c111388 0xfa813ecf3a67ee01 0xfd409f679d33f700

def z1031 : W := mkw 0x7038a1a8ae161a55 0x381c50d4570b0d2a 0xef78e1b1fe1e1e7f 0x77bc70d8ff0f0f3f

def z1032 : W := mkw 0x0c000a575822a7ba 0x0600052bac1153dd 0xff873fffffe7ffff 0xffc39ffffff3ffff

def z1033 : W := mkw 0x88f7fffdf0890022 0x447bfffef8448011 0x7efffffff9800060 0x3f7ffffffcc00030

def z1034 : W := mkw 0x006da40007544001 0x8036d20003aa2000 0x18793e000267e000 0x8c3c9f000133f000

def z1035 : W := mkw 0x40f7fffdf0001800 0x207bfffef8000c00 0x7ffffffff8001e00 0x3ffffffffc000f00

def z1036 : W := mkw 0x700800020e361f55 0x38040001071b0faa 0x81000000061e1fff 0x40800000030f0fff

def z1037 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x99ff00fe07e01fe0 0xccff807f03f00ff0

def z1038 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x0879e68ef8000000 0x043cf3477c000000

def z1039 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0x59ff01fe03e01fe0 0xacff80ff01f00ff0

def z1040 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x3e7ffe8ff8000000 0x1f3fff47fc000000

def z1041 : W := mkw 0x88025a55508980aa 0x44012d2aa844c055 0xf787df7fc59991ff 0xfbc3efbfe2ccc8ff

def z1042 : W := mkw 0x00f7f7bcf0000000 0x007bfbde78000000 0x087f26be38000000 0x043f935f1c000000

def z1043 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbefffe7007ffe1e1 0xdf7fff3803fff0f0

def z1044 : W := mkw 0x540808430e36bf9d 0x2a040421871b5fce 0xf780d941c67fff9f 0xfbc06ca0e33fffcf

def z1045 : W := mkw 0x04900befb822a798 0x024805f7dc1153cc 0x418000cf38000f98 0x20c000679c0007cc

def z1046 : W := mkw 0x00f7fffdf0144000 0x007bfffef80a2000 0x7efffffff8066000 0x3f7ffffffc033000

def z1047 : W := mkw 0x00d50bfdf0000000 0x006a85fef8000000 0x7eff3ffff8000000 0x3f7f9ffffc000000

def z1048 : W := mkw 0x08d50bfdf00080aa 0x046a85fef8004055 0xdfff01fffd8011fe 0xefff80fffec008ff

def z1049 : W := mkw 0x00e7fe7d50000000 0x0073ff3ea8000000 0x7efffeff38000000 0x3f7fff7f9c000000

def z1050 : W := mkw 0x54100bc7b822bf9c 0x2a0805e3dc115fce 0x418000cf38000f98 0x20c000679c0007cc

def z1051 : W := mkw 0x707da5aaaf765f55 0xb83ed2d557bb2faa 0x0879268e3a666e00 0x043c93471d333700

def z1052 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xff78f981fe1f9e1f 0xffbc7cc0ff0fcf0f

def z1053 : W := mkw 0x640800020f62bfd9 0xb204000107b15fec 0x8100000007e01ff8 0xc080000003f00ffc

def z1054 : W := mkw 0x00f5abfdf0000000 0x007ad5fef8000000 0x7effe1fff8000000 0x3f7ff0fffc000000

def z1055 : W := mkw 0x0075a1a8a0000000 0x003ad0d450000000 0x6e79e18ff8000000 0x373cf0c7fc000000

def z1056 : W := mkw 0x50180180ae021a15 0x280c00c057010d0a 0xef78c181fe181e1f 0x77bc60c0ff0c0f0f

def z1057 : W := mkw 0x00b0a3acb0000000 0x005851d658000000 0x0878208e38000000 0x043c10471c000000

def z1058 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x08793e8e38000000 0x043c9f471c000000

def z1059 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb813fff3a67fff9 0xfdc09fff9d33fffc

def z1060 : W := mkw 0x205501aa01600540 0x902a80d500b002a0 0xdfff01fe03e00fe0 0xefff80ff01f007f0

def z1061 : W := mkw 0x0002585140000000 0x00012c28a0000000 0xf786d971c59811ff 0xfbc36cb8e2cc08ff

def z1062 : W := mkw 0x88025a55508980aa 0x44012d2aa844c055 0xff87fffffffff1ff 0xffc3fffffffff8ff

def z1063 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xba813ece3a67ef81 0xdd409f671d33f7c0

def z1064 : W := mkw 0x88025010408980aa 0x440128082044c055 0xe706c131c59991ff 0xf3836098e2ccc8ff

def z1065 : W := mkw 0x00100bc510000000 0x000805e288000000 0x7ef93fcf38000000 0x3f7c9fe79c000000

def z1066 : W := mkw 0x0077ffed10000000 0x003bfff688000000 0x7effffff38000000 0x3f7fffff9c000000

def z1067 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x48f927fe38000000 0x247c93ff1c000000

def z1068 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xa978e081fe1e1e1f 0x54bc7040ff0f0f0f

def z1069 : W := mkw 0x0075a1a8a0000000 0x003ad0d450000000 0xffffe1fffd9811ff 0xfffff0fffecc08ff

def z1070 : W := mkw 0x640808430f62bfd9 0xb204042187b15fec 0xf786197107e7fff9 0xfbc30cb883f3fffc

def z1071 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x64fefffff8000000 0x327f7ffffc000000

def z1072 : W := mkw 0x00f7fffdf1400000 0x807bfffef8a00000 0x7efffffff9e00000 0xbf7ffffffcf00000

def z1073 : W := mkw 0x0400020618222710 0x020001030c111388 0xfb813ece3a67ef81 0xfdc09f671d33f7c0

def z1074 : W := mkw 0x802af400069d4001 0x40157a00034ea000 0xbe79fe00067fe001 0xdf3cff00033ff000

def z1075 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x2c7fffbff8000000 0x163fffdffc000000

def z1076 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfff1ffe07e1ffe0 0xefff8fff03f0fff0

def z1077 : W := mkw 0x004d000007400001 0x8026800003a00000 0xba793e000267e001 0xdd3c9f000133f000

def z1078 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x40f801fff8000000 0x207c00fffc000000

def z1079 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfffffffffd9811ff 0xfffffffffecc08ff

def z1080 : W := mkw 0x04100bef1822a798 0x020805f78c1153cc 0x418001ff38000f98 0x20c000ff9c0007cc

def z1081 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffff21fe07e61fe1 0xffff90ff03f30ff0

def z1082 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x2c78e181fe1e1e1f 0x163c70c0ff0f0f0f

def z1083 : W := mkw 0x804f500007c90001 0xc027a80003e48000 0xbe7ffe0007ffe001 0xdf3fff0003fff000

def z1084 : W := mkw 0x0077f9f9e0000000 0x003bfcfcf0000000 0x7efff9fff8000000 0x3f7ffcfffc000000

def z1085 : W := mkw 0x804f540007dd4001 0xc027aa0003eea000 0x9e7f1e0007ffe001 0xcf3f8f0003fff000

def z1086 : W := mkw 0x00f7f7acb0000000 0x007bfbd658000000 0x7e7fff8ff8000000 0x3f3fffc7fc000000

def z1087 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7ffffffff81991ff 0x3ffffffffc0cc8ff

def z1088 : W := mkw 0x80f7fffdf09d4000 0x407bfffef84ea000 0xfefffffffd9fe001 0xff7ffffffecff000

def z1089 : W := mkw 0x005501a800000000 0x002a80d400000000 0x7eff21ff38000000 0x3f7f90ff9c000000

def z1090 : W := mkw 0x006da00007540001 0x8036d00003aa0000 0xbe7ffe0007ffe001 0xdf3fff0003fff000

def z1091 : W := mkw 0x8c0800020fffe7bb 0xc604000107fff3dd 0x8100000007ffffff 0xc080000003ffffff

def z1092 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x9586d970c59991ff 0xcac36cb862ccc8ff

def z1093 : W := mkw 0x08f7fffdf0000022 0x047bfffef8000011 0x7efffffff8001066 0x3f7ffffffc000833

def z1094 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x7effe7fff8000000 0x3f7ff3fffc000000

def z1095 : W := mkw 0x00d50bfdf0000000 0x006a85fef8000000 0x48f901fff8000000 0x247c80fffc000000

def z1096 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdbff00fe03e00fe0 0xedff807f01f007f0

def z1097 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xfe7fff01c7ffe001 0xff3fff80e3fff000

def z1098 : W := mkw 0x440800020e22bf99 0x2204000107115fcc 0x810000000667ff99 0xc08000000333ffcc

def z1099 : W := mkw 0x640800020f623f51 0xb204000107b11fa8 0x0000000002666e00 0x0000000001333700

def z1100 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x99813ece3a67ef99 0xccc09f671d33f7cc

def z1101 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0x7efffffff8018180 0xbf7ffffffc00c0c0

def z1102 : W := mkw 0x88f7fffdf0890022 0x447bfffef8448011 0xfffffffffd9811e6 0xfffffffffecc08f3

def z1103 : W := mkw 0x0400020618222710 0x020001030c111388 0x18013e8e3a67ee00 0x8c009f471d33f700

def z1104 : W := mkw 0x8c22fe55589fe2ba 0x46117f2aac4ff15d 0x2000fe01f81fe01f 0x10007f00fc0ff00f

def z1105 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xdfff01fe07f81fff 0xefff80ff03fc0fff

def z1106 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x54ffdffff8000000 0x2a7feffffc000000

def z1107 : W := mkw 0x0000000208220710 0x0000000104110388 0xfb813ecf3a67ef99 0xfdc09f679d33f7cc

def z1108 : W := mkw 0x8067f40001c94000 0xc033fa0000e4a000 0xbe7ffe0003e7e001 0xdf3fff0001f3f000

def z1109 : W := mkw 0x9c22fa55f89fa2be 0x4e117d2afc4fd15f 0x2000fe01f81fe01f 0x10007f00fc0ff00f

def z1110 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x7efffffffa666000 0x3f7ffffffd333000

def z1111 : W := mkw 0x00e7fe7df0000000 0x0073ff3ef8000000 0x3efffe7ff8000000 0x1f7fff3ffc000000

def z1112 : W := mkw 0x700800020f761f55 0xb804000107bb0faa 0x0000000002660e00 0x0000000001330700

def z1113 : W := mkw 0x88025a55508980aa 0x44012d2aa844c055 0xf786ff71fd9991ff 0xfbc37fb8feccc8ff

def z1114 : W := mkw 0x0028a00006140001 0x00145000030a0000 0xba793e000267e001 0xdd3c9f000133f000

def z1115 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x5eff27fff8000000 0x2f7f93fffc000000

def z1116 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfefffffffd99801f 0xff7ffffffeccc00f

def z1117 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xfeffff7007ffe001 0xff7fffb803fff000

def z1118 : W := mkw 0x0077ffc5b0000000 0x003bffe2d8000000 0x7effffcff8000000 0x3f7fffe7fc000000

def z1119 : W := mkw 0x540800020e36bf9d 0x2a040001071b5fce 0x81000000061e1f9f 0x40800000030f0fcf

def z1120 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0x7ffffffff8000198 0x3ffffffffc0000cc

def z1121 : W := mkw 0x0000084100008088 0x0000042080004044 0xf786d971c59991ff 0xfbc36cb8e2ccc8ff

def z1122 : W := mkw 0x04f7fffdf000a088 0x027bfffef8005044 0x7efffffff801e000 0x3f7ffffffc00f000

def z1123 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff873fff3a67ef99 0xffc39fff9d33f7cc

def z1124 : W := mkw 0x00d503acb0000000 0x006a81d658000000 0x5eff01fe38000000 0x2f7f80ff1c000000

def z1125 : W := mkw 0x0077f5a8a0000000 0x003bfad450000000 0x7efffffff8000000 0x3f7ffffffc000000

def z1126 : W := mkw 0x0c000a575822a7ba 0x0600052bac1153dd 0xff81fffffe7fffff 0xffc0ffffff3fffff

def z1127 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xfff8e1c1fe1e1f9f 0xfffc70e0ff0f0fcf

def z1128 : W := mkw 0x0030a180a0000000 0x001850c050000000 0x7ef9e1cff8000000 0x3f7cf0e7fc000000

def z1129 : W := mkw 0x54900bfff822bf9c 0x2a4805fffc115fce 0x418001fff8001f9e 0x20c000fffc000fcf

def z1130 : W := mkw 0x00f5a7bcf0000000 0x007ad3de78000000 0x087927bef8000000 0x043c93df7c000000

def z1131 : W := mkw 0x0020aa4510000000 0x0010552288000000 0x7ef9fecf38000000 0x3f7cff679c000000

def z1132 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xeff8e1f1fe1e1fff 0x77fc70f8ff0f0fff

def z1133 : W := mkw 0x5038a180af561a15 0xa81c50c057ab0d0a 0xef78e181fffe1e1f 0xf7bc70c0ffff0f0f

def z1134 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xeb78e081fa1e0e1f 0x75bc7040fd0f070f

def z1135 : W := mkw 0x804d000007dd4001 0xc026800003eea000 0xbe7f3e0007ffe001 0xdf3f9f0003fff000

def z1136 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xa879fe0007ffe001 0xd43cff0003fff000

def z1137 : W := mkw 0x08b0abfdf00080aa 0x045855fef8004055 0xeff8e1fffc1811ff 0x77fc70fffe0c08ff

def z1138 : W := mkw 0x906ff400a7dd4005 0xc837fa0053eea002 0xbe7ffe00c7ffe007 0xdf3fff0063fff003

def z1139 : W := mkw 0x886ff41047dd4023 0xc437fa0823eea011 0xffffff70c7fff1e7 0xffffffb863fff8f3

def z1140 : W := mkw 0x00450a4510000000 0x0022852288000000 0x7eff3ecf38000000 0x3f7f9f679c000000

def z1141 : W := mkw 0x747da3aebf763f55 0xba3ed1d75fbb1faa 0x0879268e3a666e00 0x043c93471d333700

def z1142 : W := mkw 0x802af000069d0001 0x40157800034e8000 0xbe7ffe0007ffe001 0xdf3fff0003fff000

def z1143 : W := mkw 0x80f7fffdf09d4000 0x407bfffef84ea000 0xfefffffffa7fe001 0xff7ffffffd3ff000

def z1144 : W := mkw 0x00f5affdf0000000 0x007ad7fef8000000 0x08f926fe38000000 0x047c937f1c000000

def z1145 : W := mkw 0x00b2ffd5f0000000 0x00597feaf8000000 0x7ef9ffcff8000000 0x3f7cffe7fc000000

def z1146 : W := mkw 0x80eff43847dd4001 0xc077fa1c23eea000 0xbe7ffe3007ffe001 0xdf3fff1803fff000

def z1147 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x5586d971c59991fe 0xaac36cb8e2ccc8ff

def z1148 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x6e78e181fa1e0e1f 0x373c70c0fd0f070f

def z1149 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x5af926ce38000000 0x2d7c93671c000000

def z1150 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff813fcf3e67ff99 0xffc09fe79f33ffcc

def z1151 : W := mkw 0x80f7f7acb0890000 0x407bfbd658448000 0xbe7ffe8e3d998001 0xdf3fff471eccc000

def z1152 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xfe7ffe813fffe001 0xff3fff409ffff000

def z1153 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffffc1ffc7e01fe0 0xffffe0ffe3f00ff0

def z1154 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb813ecf3e7fff9f 0xfdc09f679f3fffcf

def z1155 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7ffffffffd9811fe 0x3ffffffffecc08ff

def z1156 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xc578c181fe1e1e1f 0x62bc60c0ff0f0f0f

def z1157 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb873eff3be7eff9 0xfdc39f7f9df3f7fc

def z1158 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff86d9f1c7999fff 0xffc36cf8e3cccfff

def z1159 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x987f3e0007ffe001 0xcc3f9f0003fff000

def z1160 : W := mkw 0x08f5affdf00080aa 0x047ad7fef8004055 0x49f927fff80011fe 0x24fc93fffc0008ff

def z1161 : W := mkw 0x00f7f5b8e0000000 0x007bfadc70000000 0x7effe1fff8000000 0x3f7ff0fffc000000

def z1162 : W := mkw 0x500800020e361f15 0x28040001071b0f8a 0x81000000067e1f9f 0xc0800000033f0fcf

def z1163 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x6578e181fc1e1e1f 0x32bc70c0fe0f0f0f

def z1164 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0x4d78e181fe1e1e1e 0x26bc70c0ff0f0f0f

def z1165 : W := mkw 0x005503ac10000000 0x002a81d608000000 0x5eff27fe38000000 0x2f7f93ff1c000000

def z1166 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xae79fe00067fe001 0x573cff00033ff000

def z1167 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbe7ffe01c7ffe01f 0xdf3fff00e3fff00f

def z1168 : W := mkw 0x00550bed10000000 0x002a85f688000000 0x7af93ecf38000000 0x3d7c9f679c000000

def z1169 : W := mkw 0x00900bfdf0000000 0x004805fef8000000 0x4ef801fff8000000 0x277c00fffc000000

def z1170 : W := mkw 0x5030a180a8161a14 0x281850c0540b0d0a 0x6f78e181f81e1e1f 0x37bc70c0fc0f0f0f

def z1171 : W := mkw 0x705d01aaa7601d45 0xb82e80d553b00ea2 0xdfff01fec7e01fe6 0xefff80ff63f00ff3

def z1172 : W := mkw 0x886ff41047dd4023 0xc437fa0823eea011 0xbe7ffe00c7ffe007 0xdf3fff0063fff003

def z1173 : W := mkw 0x80f7fffdf1c94000 0xc07bfffef8e4a000 0x7efffffff9800000 0x3f7ffffffcc00000

def z1174 : W := mkw 0x00f7fffdf0008088 0x007bfffef8004044 0x7efffffff8018019 0x3f7ffffffc00c00c

def z1175 : W := mkw 0x8067f400009d4000 0x4033fa00004ea000 0xbe7ffe00027fe001 0xdf3fff00013ff000

def z1176 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0xfffffffff98181f9 0xfffffffffcc0c0fc

def z1177 : W := mkw 0xf07ff5a8a7dd5845 0xf83ffad453eeac22 0x047ec130c5981066 0x023f609862cc0833

def z1178 : W := mkw 0x8028a00007dd4001 0xc014500003eea000 0xbe79fe0007ffe001 0xdf3cff0003fff000

def z1179 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xfffee1f1fe1e1e1f 0x7fff70f8ff0f0f0f

def z1180 : W := mkw 0x8c025a555089a0aa 0x46012d2aa844d055 0xf786df71c599f1ff 0xfbc36fb8e2ccf8ff

def z1181 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xba7f3e0003e7e001 0xdd3f9f0001f3f000

def z1182 : W := mkw 0xd06ff40007dd5805 0xe837fa0003eeac02 0xbe7ffe0007fff007 0xdf3fff0003fff803

def z1183 : W := mkw 0xe06ff40007dd5841 0xf037fa0003eeac20 0xbe7ffe0007fff061 0xdf3fff0003fff830

def z1184 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb813ecf3fe7fff9 0xfdc09f679ff3fffc

def z1185 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0xfffffffffd9991e1 0xfffffffffeccc8f0

def z1186 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xff86f9f1fd9991ff 0xffc37cf8feccc8ff

def z1187 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xff81ffcffa67ef99 0xffc0ffe7fd33f7cc

def z1188 : W := mkw 0x806ff42807dd4001 0xc037fa1403eea000 0xbefffe7e07ffe001 0xdf7fff3f03fff000

def z1189 : W := mkw 0x10f7fffdf0140004 0x087bfffef80a0002 0x7efffffff8180006 0x3f7ffffffc0c0003

def z1190 : W := mkw 0x88f7fffdf0890022 0x447bfffef8448011 0x7efffffff8180006 0x3f7ffffffc0c0003

def z1191 : W := mkw 0x80f7fffdf0890000 0x407bfffef8448000 0xfeffffffffffe001 0xff7ffffffffff000

def z1192 : W := mkw 0x88825e55508980aa 0x44412f2aa844c055 0xf786df71c59991ff 0xfbc36fb8e2ccc8ff

def z1193 : W := mkw 0xe0fff5b8e7dd5841 0xf07ffadc73eeac20 0x047ec130c5981060 0x023f609862cc0830

def z1194 : W := mkw 0x00f5afedb0000000 0x007ad7f6d8000000 0x7ef9ffcff8000000 0x3f7cffe7fc000000

def z1195 : W := mkw 0x0067fe5550000000 0x0033ff2aa8000000 0x7efffffff8000000 0x3f7ffffffc000000

def z1196 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xfb81fecffa7fef9f 0xfdc0ff67fd3ff7cf

def z1197 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0xa506d931c59991ff 0xd2836c98e2ccc8ff

def z1198 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xa9013e8f3a67ef99 0xd4809f479d33f7cc

def z1199 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0xfefffffffa060001 0x7f7ffffffd030000

def z1200 : W := mkw 0xdc0a58534ebfbfbf 0x6e052c29a75fdfdf 0xf786d971c7ffffff 0xfbc36cb8e3ffffff

def z1201 : W := mkw 0x00f5afedb0000000 0x007ad7f6d8000000 0x7eff3fff38000000 0x3f7f9fff9c000000

def z1202 : W := mkw 0x806ff400a7dd4001 0xc037fa0053eea000 0xbe7ffe01ffffe001 0xdf3fff00fffff000

def z1203 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xbe7fff00c7fff007 0xdf3fff8063fff803

def z1204 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffffc1fe07f81fe1 0xffffe0ff03fc0ff0

def z1205 : W := mkw 0x5038a180ae161a15 0x281c50c0570b0d0a 0xef78e181ff9e1fff 0xf7bc70c0ffcf0fff

def z1206 : W := mkw 0x00f5a7acb0144000 0x007ad3d6580a2000 0x0879268e38066000 0x043c93471c033000

def z1207 : W := mkw 0x88025851408980aa 0x44012c28a044c055 0x7786d971c59811fe 0x3bc36cb8e2cc08ff

def z1208 : W := mkw 0x50f7fffdf0001804 0x287bfffef8000c02 0x7efffffff8001006 0x3f7ffffffc000803

def z1209 : W := mkw 0x840800020fff6711 0xc204000107ffb388 0x8000000007ffee01 0xc000000003fff700

def z1210 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0xba013e8f3a67ee19 0xdd009f479d33f70c

def z1211 : W := mkw 0x80080a4517dd4001 0xc00405228beea000 0xfa813ecf3fffe001 0xfd409f679ffff000

def z1212 : W := mkw 0x8832fbd5f08980aa 0x44197deaf844c055 0xfffffffffd9991ff 0xfffffffffeccc8ff

def z1213 : W := mkw 0x00f5a7acb0000000 0x007ad3d658000000 0x6a79268f38000000 0x353c93479c000000

def z1214 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0x2c7ffe0007ffe001 0x163fff0003fff000

def z1215 : W := mkw 0x806ff41047dd4001 0xc037fa0823eea000 0xbe7fff30c7ffe001 0xdf3fff9863fff000

def z1216 : W := mkw 0x80f7f7acb1c94000 0xc07bfbd658e4a000 0x187f3e8e39e1e000 0x8c3f9f471cf0f000

def z1217 : W := mkw 0x88f7fffdf08980aa 0x447bfffef844c055 0x7efffffffd99907f 0x3f7ffffffeccc83f

def z1218 : W := mkw 0x00f7fffdf0000000 0x007bfffef8000000 0x76fed9fff8000000 0x3b7f6cfffc000000

def z1219 : W := mkw 0x04000a471822a798 0x020005238c1153cc 0x69813ecf3a67ef99 0x34c09f679d33f7cc

def z1220 : W := mkw 0x80f7fffdf0898088 0x407bfffef844c044 0xfffffffffd998199 0xfffffffffeccc0cc

def z1221 : W := mkw 0x88575bfd508980aa 0x442badfea844c055 0xfffffffffd9991ff 0xfffffffffeccc8ff

def z1222 : W := mkw 0x00e7fe55f0000000 0x0073ff2af8000000 0x7efffecff8000000 0x3f7fff67fc000000

def z1223 : W := mkw 0x605d01aa07601d41 0xb02e80d503b00ea0 0xffff01ff07e01ff9 0xffff80ff83f00ffc

def z1224 : W := mkw 0x0400020618222710 0x020001030c111388 0xfb013e8f3a67ee19 0xfd809f479d33f70c

def z1225 : W := mkw 0x806ff40007dd4001 0xc037fa0003eea000 0xff7ffe8007ffee01 0xffbfff4003fff700

def z1226 : W := mkw 0x540800020e36bf9d 0x2a040001071b5fce 0x810000000267ef99 0xc08000000133f7cc

def z1227 : W := mkw 0x80f7f7acb09d4000 0x407bfbd6584ea000 0x2879fe8e381fe001 0x143cff471c0ff000

def z1228 : W := mkw 0x0065ae4510000000 0x0032d72288000000 0x7af93ecf38000000 0x3d7c9f679c000000

def z1229 : W := mkw 0x88f7fffdf09dc0aa 0x447bfffef84ee055 0xfffffffffd9ff1ff 0xfffffffffecff8ff

def z1230 : W := mkw 0x44100bc71822bf98 0x220805e38c115fcc 0x418001cf38001f98 0x20c000e79c000fcc

def z1231 : W := mkw 0x605d05aa07605d41 0xb02e82d503b02ea0 0xdfff07fe07e07fe0 0xefff83ff03f03ff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z7]),(0,[z8,z0,z1,z2,z3,z5,z6]),(0,[z9,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z10,z6,z11])],[(1,[z0,z1,z2,z3,z5,z12]),(0,[z1,z13,z2,z3,z5,z6,z14]),(0,[z1,z2,z15,z3,z5,z16,z6]),(0,[z17,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z6,z19]),(0,[z20,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z21])],[(0,[z1,z2,z3,z5,z22,z6,z14]),(0,[z0,z1,z2,z3,z5,z23,z6])],[(0,[z1,z2,z15,z3,z5,z6,z14]),(0,[z18,z0,z1,z2,z3,z5,z14]),(0,[z0,z1,z2,z3,z5,z14,z24]),(0,[z18,z1,z25,z2,z3,z5,z6]),(0,[z0,z26,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z27,z5,z6])],[(0,[z28,z0,z1,z2,z3,z5,z6]),(0,[z29,z0,z1,z2,z3,z5,z6])],[(0,[z18,z1,z13,z2,z3,z5,z6]),(0,[z30,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z31,z3,z5,z6]),(0,[z0,z1,z32,z2,z3,z5,z6]),(0,[z0,z1,z2,z33,z3,z5,z6])],[(0,[z18,z1,z2,z34,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z35,z14]),(0,[z0,z1,z36,z2,z3,z5,z6]),(0,[z0,z1,z2,z37,z3,z5,z6])],[(0,[z38,z1,z13,z2,z3,z5,z6]),(0,[z39,z18,z1,z2,z3,z5,z6]),(0,[z40,z0,z1,z2,z15,z5,z6]),(1,[z0,z1,z2,z3,z41,z5])]],
   [[(0,[z38,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z42,z5,z6])],[(0,[z0,z1,z2,z3,z43,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z6])],[(0,[z45,z0,z1,z2,z3,z5,z6]),(0,[z18,z1,z46,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z47,z6]),(0,[z48,z1,z2,z3,z49,z5,z6]),(0,[z0,z1,z2,z3,z10,z5,z6])],[(0,[z0,z1,z50,z2,z3,z5,z6]),(0,[z51,z0,z1,z2,z3,z5,z6]),(0,[z52,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z14,z54]),(0,[z28,z0,z1,z2,z55,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z56]),(0,[z0,z1,z57,z2,z3,z5,z6]),(0,[z0,z1,z2,z58,z3,z5,z6]),(0,[z0,z1,z59,z2,z3,z5,z6]),(0,[z60,z0,z1,z2,z3,z5,z6])],[(0,[z61,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z62,z2,z3,z5,z6]),(0,[z0,z1,z2,z63,z3,z5,z6]),(0,[z64,z0,z1,z2,z3,z5,z6]),(0,[z65,z0,z1,z66,z2,z3,z5])],[(0,[z67,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z68,z5,z6,z14]),(0,[z69,z18,z1,z2,z3,z5,z6]),(0,[z0,z70,z1,z71,z2,z3,z6]),(0,[z0,z1,z72,z3,z5,z22,z6]),(0,[z0,z1,z2,z3,z5,z6,z73])]],
   [[(0,[z74,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z75,z6]),(0,[z76,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z77,z0,z1,z2,z3,z5,z6]),(1,[z78,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z79])],[(0,[z80,z74,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z81,z5,z6]),(0,[z1,z2,z3,z82,z5,z6,z14])],[(0,[z0,z1,z2,z3,z83,z5,z6]),(0,[z18,z1,z66,z2,z3,z5,z6]),(0,[z0,z1,z84,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z85]),(0,[z0,z1,z2,z3,z5,z86,z6])],[(0,[z17,z78,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z87,z6]),(0,[z88,z0,z89,z2,z3,z5,z6])],[(0,[z0,z1,z90,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z91]),(0,[z17,z0,z1,z92,z3,z5,z6]),(0,[z0,z1,z93,z3,z94,z5,z6]),(0,[z95,z0,z1,z2,z3,z6,z96])],[]],
   [[(0,[z0,z97,z1,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z5,z6])],[(0,[z99,z0,z1,z2,z3,z5,z6]),(0,[z0,z100,z1,z2,z3,z5,z6]),(0,[z1,z2,z101,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z102,z5,z6]),(0,[z0,z1,z103,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z104]),(0,[z0,z1,z105,z2,z3,z5,z6]),(0,[z18,z1,z71,z2,z3,z5,z6]),(0,[z0,z1,z25,z72,z3,z5,z6])],[(0,[z0,z1,z106,z2,z3,z5,z6]),(0,[z0,z70,z2,z3,z82,z5,z6]),(0,[z8,z0,z1,z2,z3,z107,z6])],[(0,[z0,z108,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z109,z6]),(0,[z110,z1,z2,z3,z5,z6,z14]),(1,[z0,z1,z72,z3,z5,z22]),(0,[z0,z1,z2,z3,z5,z6,z111]),(0,[z112,z0,z1,z2,z3,z5,z6])],[(0,[z113,z18,z1,z2,z3,z5,z6]),(0,[z114,z0,z1,z2,z3,z5,z6]),(0,[z115,z0,z1,z2,z3,z23,z6]),(0,[z0,z1,z25,z3,z5,z6,z116])],[(0,[z18,z1,z2,z117,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z118,z6]),(0,[z0,z1,z2,z3,z119,z120,z6])],[(0,[z0,z1,z121,z2,z3,z5,z6]),(0,[z18,z1,z2,z15,z3,z5,z6]),(0,[z0,z1,z2,z3,z122,z5,z6]),(0,[z0,z1,z2,z123,z3,z5,z6]),(0,[z124,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z125,z3,z5,z6]),(0,[z0,z126,z1,z2,z3,z5,z6]),(0,[z127,z0,z1,z2,z3,z5,z6]),(0,[z48,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z128,z1,z2,z3,z5,z6]),(0,[z129,z0,z1,z2,z3,z5,z6]),(0,[z130,z0,z1,z2,z3,z5,z6])],[(0,[z131,z0,z1,z13,z2,z3,z6]),(0,[z113,z132,z1,z2,z3,z5,z6]),(1,[z133,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z11,z73])],[(0,[z18,z70,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z134,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z135]),(0,[z0,z1,z2,z3,z5,z6,z136])],[(0,[z0,z1,z2,z3,z5,z16,z6]),(0,[z0,z1,z2,z3,z5,z6,z137]),(1,[z0,z1,z2,z3,z5,z138]),(0,[z0,z1,z2,z3,z5,z6,z139])],[(0,[z0,z1,z2,z3,z140,z5,z6]),(0,[z38,z0,z1,z2,z3,z141,z6]),(0,[z0,z1,z2,z142,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z14]),(0,[z0,z1,z144,z2,z3,z5,z6]),(0,[z145,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z116]),(0,[z69,z0,z1,z2,z3,z6,z73]),(0,[z88,z0,z1,z2,z3,z146,z6])],[(1,[z0,z1,z2,z3,z5,z147]),(0,[z148,z38,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z149,z6]),(0,[z150,z1,z2,z3,z5,z6,z14]),(1,[z18,z1,z2,z3,z5,z14]),(0,[z0,z1,z2,z3,z5,z6,z151]),(0,[z0,z1,z152,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z153,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z154]),(0,[z8,z0,z1,z2,z155,z3,z5])],[(0,[z1,z156,z2,z34,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z157,z6]),(0,[z158,z0,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z5,z138]),(0,[z8,z0,z1,z2,z3,z5,z22])],[(0,[z1,z93,z2,z3,z5,z6,z14]),(0,[z0,z84,z2,z55,z3,z5,z6]),(0,[z0,z1,z2,z94,z5,z6,z19]),(0,[z0,z1,z2,z3,z5,z159,z6])]],
   [[(0,[z18,z1,z156,z2,z3,z5,z6]),(0,[z160,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z161,z5,z6]),(0,[z0,z2,z3,z5,z23,z6,z24]),(0,[z0,z1,z72,z3,z94,z5,z6]),(0,[z0,z1,z2,z162,z3,z5,z6]),(1,[z65,z0,z1,z66,z2,z3])],[(0,[z163,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z164,z6]),(0,[z0,z165,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z2,z166,z5,z6]),(0,[z0,z167,z1,z2,z3,z5,z6])],[(1,[z80,z13,z2,z3,z5,z6]),(0,[z38,z1,z156,z2,z3,z5,z6]),(0,[z168,z0,z1,z2,z15,z5,z6]),(0,[z1,z71,z2,z3,z5,z6,z14]),(0,[z0,z1,z169,z2,z3,z5,z6]),(0,[z0,z110,z2,z170,z3,z5,z6]),(0,[z0,z1,z171,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z172]),(0,[z0,z1,z2,z3,z173,z5,z6])],[(0,[z174,z0,z1,z2,z3,z5,z6]),(0,[z0,z175,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z176]),(0,[z0,z177,z1,z2,z3,z5,z6]),(0,[z0,z1,z178,z2,z3,z5,z6]),(0,[z88,z0,z1,z2,z155,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z179])],[(0,[z180,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z23,z11]),(0,[z0,z1,z93,z2,z155,z5,z6]),(1,[z0,z1,z2,z3,z107,z6]),(1,[z8,z0,z1,z3,z5,z116]),(0,[z0,z1,z2,z3,z181,z5,z6]),(0,[z182,z0,z1,z2,z3,z5,z6])],[(1,[z38,z1,z2,z3,z141,z6]),(0,[z183,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z184,z6]),(1,[z1,z2,z3,z5,z6,z185])],[(0,[z0,z1,z2,z3,z5,z6,z186]),(0,[z0,z1,z2,z3,z5,z6,z24])],[(0,[z187,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z188,z6]),(0,[z0,z1,z2,z189,z3,z5,z6]),(0,[z190,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z191,z5,z6]),(0,[z192,z0,z1,z2,z3,z5,z6]),(0,[z0,z193,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z3,z194,z6]),(0,[z0,z1,z2,z195,z3,z5,z6]),(0,[z0,z1,z196,z2,z3,z5,z6])],[(0,[z0,z1,z25,z93,z2,z5,z6]),(0,[z0,z1,z197,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z198,z6]),(1,[z0,z1,z2,z155,z5,z199])],[(0,[z0,z110,z1,z2,z120,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z200])],[(0,[z0,z1,z201,z2,z3,z5,z6]),(0,[z17,z148,z0,z1,z2,z3,z6]),(0,[z18,z1,z72,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z202,z6]),(0,[z0,z1,z2,z3,z5,z6,z19]),(1,[z1,z203,z2,z3,z5,z6])],[(0,[z1,z2,z3,z94,z5,z6,z14])],[(0,[z204,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z205,z3,z5,z6]),(0,[z206,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z101,z3,z5,z6]),(0,[z18,z1,z2,z3,z49,z5,z6]),(0,[z0,z1,z25,z2,z3,z5,z6]),(0,[z95,z0,z1,z2,z3,z49,z6]),(0,[z0,z1,z2,z3,z10,z5,z11])],[(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z80,z1,z2,z15,z3,z5,z6]),(0,[z208,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z209,z5,z6]),(0,[z1,z2,z3,z5,z6,z210,z14]),(0,[z18,z1,z2,z3,z5,z6,z14]),(0,[z211,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z212,z5,z6])],[(0,[z0,z1,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z213,z5,z6]),(0,[z214,z0,z1,z2,z3,z5,z6]),(0,[z1,z66,z203,z2,z3,z5,z6])]],
   [[(0,[z150,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z34,z3,z5,z6]),(0,[z0,z1,z215,z2,z3,z5,z6]),(0,[z1,z2,z155,z3,z5,z6,z14]),(1,[z1,z2,z216,z3,z5,z6]),(0,[z0,z78,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z217,z5,z6]),(0,[z69,z0,z1,z2,z5,z6,z73])],[(0,[z0,z1,z218,z2,z3,z5,z6]),(0,[z0,z1,z219,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z220,z5,z6])],[(0,[z113,z39,z1,z2,z3,z5,z6]),(0,[z221,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z119,z6]),(0,[z222,z0,z1,z2,z3,z5,z6]),(0,[z223,z0,z2,z3,z5,z6,z24]),(1,[z0,z1,z2,z166,z5,z6])],[(0,[z0,z224,z1,z2,z3,z5,z6]),(0,[z225,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z226,z6]),(1,[z1,z2,z3,z5,z227,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z228,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z229]),(0,[z0,z1,z2,z3,z5,z6,z230]),(0,[z40,z0,z1,z2,z81,z5,z6]),(0,[z231,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z46,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z232]),(0,[z0,z1,z93,z2,z5,z6,z19]),(0,[z233,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z234,z5,z6])],[(0,[z235,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z236]),(0,[z0,z1,z2,z3,z5,z6,z237]),(0,[z0,z1,z2,z3,z5,z238,z6]),(0,[z0,z1,z2,z3,z239,z5,z6]),(0,[z0,z1,z2,z3,z5,z240,z6])],[(0,[z0,z1,z2,z241,z3,z5,z6]),(0,[z1,z156,z2,z15,z3,z5,z6]),(0,[z88,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z71,z2,z3,z6,z96])]],
   [[(0,[z242,z18,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z141,z5,z16,z6]),(0,[z0,z1,z25,z46,z3,z5,z6]),(1,[z0,z1,z25,z93,z5,z6]),(0,[z0,z1,z243,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z244,z5,z6]),(0,[z1,z2,z3,z5,z109,z6,z14]),(1,[z221,z1,z2,z3,z5,z6]),(1,[z245,z0,z1,z2,z3,z5])],[(0,[z246,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z247,z2,z3,z5,z6]),(0,[z0,z248,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z249,z5,z6]),(0,[z0,z1,z2,z3,z5,z250,z6]),(0,[z0,z1,z251,z2,z3,z5,z6])],[(0,[z0,z1,z252,z2,z3,z5,z6]),(0,[z253,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z81,z5,z6]),(0,[z254,z0,z1,z2,z3,z5,z6]),(0,[z0,z70,z1,z2,z3,z82,z6])],[(0,[z168,z18,z1,z2,z3,z5,z6]),(0,[z1,z66,z2,z3,z5,z6,z14]),(0,[z1,z2,z216,z55,z3,z5,z6]),(0,[z0,z1,z2,z170,z5,z6,z73]),(0,[z0,z1,z255,z2,z3,z5,z6]),(0,[z0,z256,z1,z2,z3,z5,z6]),(0,[z0,z1,z66,z2,z3,z5,z6])],[(0,[z38,z0,z70,z1,z2,z3,z6]),(0,[z0,z1,z2,z257,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z258,z6]),(0,[z0,z1,z2,z3,z5,z6,z259]),(0,[z0,z2,z3,z120,z5,z6,z24]),(0,[z133,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z107,z5,z6]),(0,[z0,z1,z3,z5,z22,z6,z116])]],
   [[(0,[z0,z1,z2,z3,z5,z260,z6]),(0,[z1,z2,z3,z5,z6,z14,z73]),(0,[z0,z1,z2,z3,z5,z6,z261]),(1,[z0,z1,z2,z262,z5,z6])],[(0,[z168,z132,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z263,z5,z6]),(0,[z18,z0,z1,z2,z3,z5,z6]),(0,[z1,z25,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z6,z264])],[(0,[z0,z2,z170,z3,z120,z5,z6])],[(0,[z18,z1,z2,z3,z265,z5,z6]),(0,[z17,z0,z1,z2,z262,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z266]),(0,[z0,z1,z2,z3,z102,z5,z6]),(0,[z0,z267,z1,z2,z3,z5,z6])],[(0,[z74,z0,z132,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z268]),(0,[z17,z0,z1,z2,z3,z6,z11]),(0,[z0,z1,z71,z2,z3,z5,z6]),(0,[z0,z1,z269,z2,z3,z5,z6])],[(0,[z270,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z271,z2,z3,z5,z6]),(1,[z0,z1,z46,z94,z5,z6]),(0,[z0,z1,z272,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z273])],[(0,[z274,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z275,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z276,z6]),(0,[z150,z18,z1,z2,z3,z5,z6]),(1,[z277,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z278,z3,z5,z6]),(0,[z129,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z117,z3,z5,z6]),(0,[z0,z67,z1,z2,z3,z5,z23])],[(1,[z113,z1,z34,z3,z5,z6]),(0,[z279,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z15,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z280]),(0,[z0,z1,z2,z3,z281,z5,z6]),(0,[z0,z1,z2,z3,z282,z5,z6])],[(1,[z1,z2,z3,z5,z23,z14]),(0,[z0,z1,z2,z283,z3,z5,z6]),(0,[z0,z1,z284,z2,z3,z5,z6]),(0,[z88,z0,z1,z2,z3,z5,z6])],[(0,[z148,z1,z2,z3,z5,z16,z6]),(0,[z0,z1,z2,z3,z285,z5,z6]),(0,[z95,z1,z2,z3,z5,z6,z14]),(1,[z0,z1,z2,z286,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z287]),(0,[z0,z1,z2,z288,z3,z5,z6]),(0,[z1,z156,z2,z3,z5,z16,z6]),(0,[z0,z289,z1,z2,z3,z5,z6]),(0,[z290,z18,z1,z2,z3,z5,z6]),(0,[z0,z70,z1,z2,z3,z5,z6]),(0,[z0,z1,z291,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z292,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z293])],[(0,[z294,z0,z1,z2,z3,z5,z6]),(0,[z148,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z295,z5,z6])],[(0,[z1,z156,z2,z3,z5,z6,z14]),(0,[z296,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z297,z2,z3,z5,z6]),(0,[z17,z0,z1,z2,z286,z5,z6]),(0,[z0,z1,z2,z3,z298,z5,z6]),(0,[z0,z1,z2,z3,z23,z6,z135])],[(0,[z0,z1,z299,z2,z3,z5,z6]),(0,[z0,z1,z300,z2,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z301,z5,z6])]],
   [[(0,[z302,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z303,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z304,z6]),(0,[z305,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z306,z3,z5,z6]),(0,[z0,z1,z307,z2,z3,z5,z6])],[(0,[z0,z1,z156,z2,z3,z5,z6]),(0,[z308,z0,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z309,z3,z5,z6]),(0,[z8,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z310,z2,z3,z5,z6]),(0,[z1,z2,z3,z102,z5,z198,z6]),(0,[z0,z1,z203,z2,z3,z5,z6])],[(0,[z40,z1,z2,z15,z3,z5,z6]),(0,[z231,z0,z1,z84,z3,z5,z6]),(0,[z0,z1,z55,z3,z5,z6,z96]),(1,[z17,z0,z2,z3,z194,z6]),(1,[z222,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z311])],[(0,[z312,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z313,z6]),(0,[z1,z2,z3,z49,z5,z314,z6])],[(0,[z0,z1,z315,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z116]),(0,[z18,z316,z1,z2,z3,z5,z6]),(0,[z18,z110,z1,z2,z3,z5,z6]),(0,[z296,z0,z1,z2,z170,z5,z6])],[(0,[z80,z148,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z317,z6]),(0,[z0,z1,z318,z2,z3,z5,z6]),(0,[z0,z1,z319,z2,z3,z5,z6]),(0,[z17,z69,z0,z1,z2,z3,z6]),(0,[z0,z1,z71,z2,z3,z49,z6]),(0,[z320,z0,z1,z2,z3,z5,z6]),(0,[z321,z0,z1,z2,z3,z5,z6]),(0,[z0,z322,z1,z2,z3,z5,z6])],[(0,[z80,z1,z13,z2,z3,z5,z6]),(0,[z323,z0,z1,z2,z3,z5,z6]),(0,[z0,z67,z110,z2,z3,z5,z6]),(0,[z0,z1,z2,z286,z3,z5,z6]),(0,[z324,z0,z1,z2,z3,z5,z6]),(0,[z8,z325,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z2,z326,z5,z6]),(0,[z1,z2,z3,z5,z22,z6,z311]),(0,[z327,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z328]),(0,[z0,z1,z66,z2,z3,z10,z5])]],
   [[(0,[z0,z1,z2,z329,z3,z5,z6]),(0,[z18,z18,z1,z2,z3,z5,z6]),(0,[z231,z0,z2,z55,z3,z5,z6]),(1,[z0,z97,z84,z3,z5,z6]),(0,[z0,z1,z2,z3,z119,z5,z6]),(0,[z69,z0,z1,z2,z44,z5,z6]),(0,[z0,z330,z1,z2,z3,z5,z6])],[(0,[z18,z1,z2,z3,z5,z6,z96]),(0,[z95,z0,z70,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z331])],[(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z38,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z333]),(0,[z1,z2,z3,z5,z199,z6,z14]),(0,[z334,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z138,z6]),(1,[z223,z0,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z227,z6])],[(0,[z0,z1,z2,z3,z5,z335,z6]),(0,[z0,z1,z2,z3,z5,z6,z336]),(0,[z148,z0,z70,z1,z2,z3,z6]),(0,[z223,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z6,z35]),(0,[z0,z1,z2,z337,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z338,z6]),(0,[z339,z0,z1,z2,z3,z5,z6]),(0,[z0,z340,z1,z2,z3,z5,z6]),(0,[z245,z0,z1,z2,z3,z94,z5]),(0,[z0,z1,z2,z341,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z342,z6]),(0,[z0,z1,z2,z3,z5,z343,z6]),(0,[z1,z2,z3,z5,z6,z14,z176]),(0,[z18,z1,z93,z2,z3,z5,z6]),(0,[z0,z1,z344,z2,z3,z5,z6]),(1,[z296,z0,z2,z120,z5,z6]),(0,[z345,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z346,z3,z5,z6]),(0,[z347,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z2,z94,z5,z6]),(0,[z0,z1,z2,z155,z94,z5,z6]),(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z348,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z349,z2,z3,z5,z6])],[(0,[z1,z2,z3,z120,z5,z6,z14]),(0,[z0,z1,z2,z3,z350,z5,z6]),(0,[z0,z1,z2,z351,z3,z5,z6]),(0,[z17,z0,z2,z3,z5,z194,z6]),(0,[z352,z0,z1,z2,z3,z5,z6]),(0,[z95,z0,z1,z2,z3,z5,z6]),(0,[z353,z0,z1,z2,z3,z5,z6])],[(0,[z354,z0,z1,z2,z3,z5,z6]),(0,[z355,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z24]),(0,[z0,z1,z2,z3,z49,z5,z6]),(0,[z0,z1,z2,z356,z3,z5,z6]),(1,[z0,z1,z357,z3,z5,z6])]],
   [[(0,[z148,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z11,z14]),(0,[z0,z1,z2,z3,z5,z6,z14]),(0,[z358,z0,z1,z2,z3,z120,z6])],[(1,[z231,z0,z55,z3,z5,z6]),(0,[z296,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z226,z6]),(0,[z0,z1,z2,z3,z5,z6,z359])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z360,z1,z2,z3,z5,z6]),(0,[z0,z361,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z84,z3,z5,z6,z96]),(0,[z0,z1,z2,z44,z120,z5,z6]),(0,[z0,z1,z362,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z363])],[(1,[z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z364,z2,z3,z5,z6]),(0,[z0,z1,z365,z2,z3,z5,z6]),(0,[z277,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z366,z5,z6])],[(0,[z1,z2,z3,z5,z6,z14,z19]),(0,[z0,z1,z2,z3,z41,z5,z6]),(0,[z0,z1,z2,z367,z3,z5,z6])],[(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z369,z6]),(0,[z0,z1,z2,z370,z3,z5,z6]),(0,[z0,z1,z46,z2,z94,z5,z6]),(1,[z95,z0,z1,z3,z6,z96]),(1,[z88,z0,z1,z2,z5,z19])],[(0,[z74,z132,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z371,z5,z6]),(0,[z17,z18,z1,z2,z3,z5,z6]),(0,[z372,z0,z1,z2,z3,z5,z6]),(0,[z0,z373,z1,z2,z3,z5,z6]),(0,[z0,z1,z374,z2,z3,z5,z6]),(0,[z8,z76,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z375,z3,z5,z6]),(1,[z143,z1,z2,z3,z5,z14]),(0,[z0,z1,z2,z3,z5,z6,z376]),(0,[z377,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z80,z0,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z378]),(0,[z0,z1,z2,z3,z5,z6,z379]),(0,[z380,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z381,z6]),(0,[z0,z1,z2,z382,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z56]),(0,[z0,z70,z1,z2,z3,z194,z6]),(0,[z383,z0,z1,z2,z3,z5,z6]),(1,[z325,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z326,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z384]),(0,[z70,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z22,z6]),(0,[z0,z67,z2,z55,z3,z5,z6]),(0,[z0,z1,z2,z3,z385,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z386])],[(0,[z65,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z55,z3,z5,z6]),(0,[z0,z1,z2,z387,z3,z5,z6])],[(0,[z17,z0,z1,z2,z3,z5,z56]),(0,[z0,z1,z2,z388,z3,z5,z6]),(1,[z389,z1,z2,z3,z5,z6])],[(0,[z0,z1,z390,z2,z3,z5,z6]),(0,[z0,z67,z1,z2,z3,z5,z24]),(0,[z391,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z392,z3,z5,z6]),(0,[z393,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z394,z2,z3,z5,z6])],[(0,[z395,z0,z1,z2,z3,z5,z6]),(0,[z0,z67,z2,z3,z120,z5,z6]),(0,[z396,z0,z1,z2,z3,z5,z6]),(0,[z223,z0,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z2,z3,z5,z116]),(0,[z397,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z398,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z399]),(0,[z0,z1,z2,z155,z3,z5,z19])]],
   [[(0,[z400,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z401,z5,z6]),(1,[z40,z1,z2,z15,z5,z6]),(0,[z0,z1,z2,z402,z3,z5,z6]),(0,[z0,z1,z2,z120,z5,z6,z73]),(0,[z0,z67,z2,z3,z82,z5,z6]),(0,[z65,z0,z1,z2,z3,z6,z96]),(0,[z0,z403,z1,z2,z3,z5,z6])],[(0,[z80,z168,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z404]),(0,[z0,z1,z3,z94,z5,z6,z116]),(0,[z0,z1,z2,z3,z5,z6,z405]),(0,[z0,z406,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z6,z73])],[(0,[z407,z0,z1,z2,z3,z5,z6]),(0,[z18,z0,z1,z2,z3,z5,z109]),(0,[z0,z1,z2,z408,z3,z5,z6]),(0,[z0,z1,z2,z3,z409,z5,z6]),(0,[z0,z1,z2,z3,z5,z410,z6]),(0,[z65,z0,z1,z2,z3,z102,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z411,z6]),(0,[z0,z1,z412,z2,z3,z5,z6]),(1,[z0,z70,z2,z3,z82,z6]),(0,[z413,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z414,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z155,z3,z5,z199])],[(0,[z0,z415,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z416,z14]),(0,[z0,z1,z2,z3,z265,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z417]),(0,[z0,z1,z66,z2,z3,z6,z11])],[(0,[z0,z1,z2,z3,z5,z418,z6])],[(0,[z0,z419,z1,z2,z3,z5,z6]),(1,[z76,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z420,z5,z6])]],
   [[(0,[z113,z1,z2,z34,z3,z5,z6]),(0,[z113,z38,z1,z2,z3,z5,z6]),(0,[z296,z18,z1,z2,z3,z5,z6]),(0,[z421,z0,z1,z2,z3,z5,z6]),(0,[z0,z97,z1,z55,z3,z5,z6]),(1,[z358,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z422,z5,z6]),(0,[z65,z0,z70,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z423,z6]),(0,[z0,z424,z1,z2,z3,z5,z6])],[(0,[z143,z18,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z82,z5,z194,z6]),(0,[z425,z0,z1,z2,z3,z5,z6]),(0,[z426,z1,z66,z2,z3,z5,z6])],[(0,[z80,z1,z156,z2,z3,z5,z6]),(0,[z0,z427,z1,z2,z3,z5,z6]),(0,[z428,z0,z1,z2,z3,z5,z6]),(0,[z0,z429,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z311])],[(0,[z0,z430,z1,z2,z3,z5,z6]),(0,[z0,z1,z431,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z432,z6]),(0,[z0,z1,z2,z3,z102,z6,z11])],[(0,[z0,z1,z2,z433,z3,z5,z6]),(0,[z148,z0,z1,z2,z3,z141,z6]),(0,[z434,z0,z1,z2,z3,z5,z6]),(0,[z435,z0,z1,z2,z3,z5,z6])],[(0,[z40,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z436,z3,z5,z6]),(0,[z65,z0,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z141,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z437,z6]),(0,[z0,z1,z2,z3,z438,z5,z6])],[(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z440,z0,z1,z2,z3,z5,z6]),(0,[z0,z441,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z442])]],
   [[(0,[z0,z1,z443,z2,z3,z5,z6]),(0,[z0,z1,z297,z2,z3,z5,z6]),(0,[z0,z2,z55,z3,z5,z6,z24]),(0,[z0,z67,z97,z2,z3,z5,z6]),(1,[z0,z444,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z445])],[(0,[z132,z1,z2,z3,z141,z5,z6]),(0,[z0,z1,z2,z3,z446,z5,z6]),(0,[z1,z2,z3,z5,z23,z6,z14]),(0,[z18,z1,z2,z3,z5,z194,z6]),(0,[z18,z1,z2,z3,z94,z5,z6]),(1,[z28,z0,z1,z2,z3,z6]),(0,[z447,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z448,z6]),(1,[z435,z1,z2,z3,z5,z6]),(0,[z449,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z72,z2,z155,z3,z5]),(0,[z0,z1,z450,z2,z3,z5,z6])],[(0,[z38,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z5,z451,z6])],[(0,[z0,z1,z2,z452,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z453]),(0,[z0,z1,z2,z309,z3,z5,z6]),(0,[z0,z70,z1,z2,z3,z6,z11]),(0,[z0,z67,z2,z3,z5,z23,z6])],[(0,[z1,z84,z2,z3,z5,z6,z14]),(0,[z454,z1,z2,z3,z5,z6,z14]),(0,[z223,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z455,z5,z6]),(0,[z0,z1,z456,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z457,z5,z6]),(0,[z0,z1,z2,z3,z458,z5,z6])],[(0,[z231,z0,z1,z55,z3,z5,z6]),(0,[z459,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z155,z5,z199,z6])],[(0,[z0,z460,z1,z2,z3,z5,z6]),(0,[z0,z1,z461,z2,z3,z5,z6]),(0,[z0,z316,z1,z2,z3,z5,z6])]],
   [[(0,[z80,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z170,z3,z5,z6]),(0,[z0,z97,z1,z84,z3,z5,z6]),(1,[z1,z2,z3,z462,z5,z6]),(0,[z463,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z464,z2,z3,z5,z6]),(1,[z48,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z465,z3,z5,z6])],[(0,[z0,z1,z466,z2,z3,z5,z6]),(0,[z0,z1,z467,z2,z3,z5,z6]),(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z199,z6,z185])],[(1,[z148,z1,z2,z3,z16,z6]),(0,[z88,z8,z0,z1,z2,z3,z5])],[(0,[z80,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z469,z2,z3,z5,z6]),(1,[z39,z1,z156,z3,z5,z6]),(0,[z0,z1,z470,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z6,z135]),(0,[z0,z1,z2,z3,z5,z6,z96]),(0,[z0,z1,z2,z3,z471,z5,z6])],[(0,[z472,z0,z1,z2,z3,z5,z6]),(0,[z473,z0,z1,z2,z3,z5,z6])],[(0,[z474,z0,z1,z2,z3,z5,z6]),(0,[z0,z475,z1,z2,z3,z5,z6])],[(0,[z0,z110,z2,z3,z5,z6,z24]),(0,[z0,z1,z93,z2,z3,z5,z6]),(0,[z476,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z477,z2,z3,z5,z6])],[(0,[z478,z0,z1,z2,z3,z5,z6]),(0,[z65,z0,z1,z2,z3,z49,z6]),(0,[z0,z325,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z185]),(1,[z0,z479,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z480,z5,z6]),(0,[z17,z0,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z481,z3,z5,z6]),(0,[z8,z0,z482,z2,z3,z5,z6]),(1,[z0,z483,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z199,z6,z19])],[(0,[z113,z168,z1,z2,z3,z5,z6]),(0,[z113,z1,z2,z15,z3,z5,z6]),(0,[z0,z1,z2,z3,z484,z5,z6]),(1,[z1,z2,z3,z5,z14,z24]),(0,[z88,z0,z1,z2,z3,z5,z199])],[(0,[z39,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z485,z120,z5,z6]),(0,[z486,z0,z1,z2,z3,z5,z6]),(0,[z0,z389,z1,z2,z3,z5,z6])],[(0,[z18,z1,z2,z3,z141,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z109]),(0,[z0,z1,z2,z3,z5,z6,z487]),(0,[z65,z0,z1,z66,z2,z3,z6])],[(0,[z80,z0,z132,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z109,z24])],[(0,[z0,z1,z488,z2,z3,z5,z6]),(0,[z38,z1,z2,z3,z141,z5,z6]),(0,[z0,z1,z2,z3,z5,z489,z6]),(0,[z490,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z49,z5,z6,z96]),(0,[z0,z1,z491,z2,z3,z5,z6]),(0,[z60,z1,z2,z3,z10,z5,z6])],[(0,[z0,z1,z2,z492,z3,z5,z6]),(0,[z254,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z493]),(0,[z0,z1,z2,z3,z5,z494,z6]),(0,[z0,z1,z495,z2,z3,z5,z6])],[(1,[z168,z1,z2,z81,z5,z6]),(0,[z0,z1,z2,z3,z5,z496,z6]),(0,[z0,z1,z2,z3,z497,z5,z6]),(0,[z0,z1,z2,z3,z49,z6,z11]),(1,[z321,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z10,z11])]],
   [[(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z498,z3,z5,z6]),(0,[z454,z0,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z14,z14]),(0,[z499,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z500,z6]),(0,[z97,z1,z2,z3,z5,z6,z14]),(0,[z69,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z216,z3,z5,z6]),(1,[z1,z2,z3,z485,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z501]),(0,[z502,z0,z1,z2,z3,z5,z6])],[(0,[z80,z0,z1,z2,z3,z5,z6]),(0,[z503,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z504,z6]),(0,[z168,z0,z1,z2,z81,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z505]),(0,[z1,z2,z3,z462,z94,z5,z6]),(0,[z0,z1,z2,z3,z5,z22,z6]),(0,[z0,z1,z2,z102,z5,z6,z73])],[(0,[z0,z1,z506,z2,z3,z5,z6])],[(0,[z0,z1,z2,z507,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z508]),(0,[z0,z1,z2,z3,z5,z509,z6]),(0,[z17,z95,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z11,z96]),(0,[z0,z1,z2,z3,z5,z6,z510]),(0,[z0,z66,z479,z2,z3,z5,z6])],[(0,[z511,z0,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z6,z11]),(0,[z221,z1,z2,z55,z3,z5,z6]),(0,[z17,z0,z67,z2,z3,z5,z6]),(0,[z17,z65,z0,z1,z2,z3,z6])],[(0,[z18,z132,z1,z2,z3,z5,z6]),(0,[z1,z2,z55,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z6,z512])]],
   [[(0,[z0,z1,z2,z3,z5,z513,z6]),(0,[z168,z38,z1,z2,z3,z5,z6]),(0,[z88,z0,z1,z357,z3,z5,z6]),(0,[z514,z0,z1,z2,z3,z5,z6])],[(0,[z39,z0,z1,z34,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z515]),(0,[z0,z1,z2,z3,z516,z5,z6]),(1,[z0,z482,z2,z3,z5,z6])],[(0,[z0,z517,z1,z2,z3,z5,z6]),(0,[z69,z0,z1,z2,z3,z102,z6]),(0,[z88,z0,z1,z2,z3,z226,z6])],[(0,[z1,z2,z170,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z518,z6])],[(0,[z88,z18,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z402,z3,z6]),(0,[z0,z1,z2,z3,z519,z5,z6]),(0,[z0,z1,z520,z2,z3,z5,z6])],[(0,[z39,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z521,z2,z3,z5,z6]),(0,[z0,z522,z1,z2,z3,z5,z6]),(1,[z115,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z523,z5,z6])],[(0,[z113,z1,z2,z3,z5,z16,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z93,z46,z2,z5,z6])],[(0,[z524,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z525,z3,z5,z6]),(0,[z1,z46,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z6,z116]),(0,[z0,z1,z2,z3,z5,z6,z526]),(0,[z0,z1,z2,z3,z5,z6,z527]),(0,[z65,z0,z1,z2,z3,z5,z11])]],
   [[(0,[z0,z1,z2,z528,z3,z5,z6]),(0,[z113,z1,z2,z3,z5,z6,z14]),(0,[z529,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z6,z416]),(0,[z18,z1,z530,z2,z3,z5,z6]),(0,[z69,z0,z70,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z531])],[(0,[z132,z1,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z532]),(1,[z0,z1,z2,z44,z102,z6])],[(0,[z533,z0,z1,z2,z3,z5,z6]),(0,[z302,z18,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z534,z5,z6]),(0,[z0,z1,z2,z3,z535,z5,z6]),(1,[z426,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z81,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z199,z6]),(0,[z536,z0,z1,z2,z3,z5,z6]),(0,[z0,z537,z1,z2,z3,z5,z6]),(1,[z0,z110,z2,z170,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z538]),(0,[z0,z1,z2,z3,z5,z539,z6])],[(0,[z168,z1,z2,z3,z81,z5,z6]),(0,[z0,z540,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z314,z6]),(0,[z541,z0,z1,z2,z3,z5,z6]),(0,[z88,z389,z1,z2,z3,z5,z6])],[(0,[z40,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z542,z5,z6]),(0,[z543,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z166,z5,z6]),(0,[z69,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z544]),(1,[z0,z1,z71,z3,z49,z6])],[(0,[z80,z0,z1,z2,z3,z5,z147]),(0,[z0,z1,z2,z3,z5,z6,z545]),(0,[z0,z1,z2,z3,z5,z546,z6]),(0,[z0,z1,z2,z3,z5,z6,z547]),(0,[z426,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z74,z1,z2,z3,z5,z16,z6]),(0,[z18,z74,z1,z2,z3,z5,z6]),(0,[z548,z0,z1,z2,z3,z5,z6]),(0,[z549,z0,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z16,z6,z14]),(0,[z0,z550,z1,z2,z3,z5,z6])],[(0,[z80,z18,z1,z2,z3,z5,z6]),(0,[z38,z74,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z551,z6]),(0,[z18,z1,z2,z3,z120,z5,z6]),(0,[z231,z0,z97,z2,z3,z5,z6]),(0,[z0,z1,z552,z2,z3,z5,z6]),(0,[z0,z1,z71,z3,z49,z5,z6])],[(0,[z0,z1,z2,z3,z5,z109,z23]),(0,[z0,z1,z2,z3,z553,z5,z6]),(0,[z0,z1,z2,z3,z554,z5,z6]),(0,[z115,z0,z1,z2,z3,z5,z6])],[(1,[z74,z132,z2,z3,z5,z6]),(0,[z0,z555,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z23,z14]),(0,[z332,z18,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z82,z5,z6]),(0,[z0,z1,z2,z3,z5,z194,z6]),(0,[z0,z1,z556,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z94,z5,z6]),(0,[z0,z1,z2,z557,z3,z5,z6])],[(0,[z0,z1,z2,z3,z558,z5,z6]),(0,[z0,z1,z46,z3,z94,z5,z6]),(0,[z95,z0,z1,z3,z5,z6,z96])],[(0,[z0,z1,z2,z3,z5,z6,z559]),(0,[z560,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z561]),(1,[z0,z1,z562,z3,z5,z6])],[(0,[z0,z1,z469,z13,z2,z3,z6]),(0,[z113,z0,z1,z34,z3,z5,z6]),(0,[z0,z1,z482,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z146,z5,z6])]],
   [[(0,[z0,z1,z563,z2,z3,z5,z6]),(0,[z95,z18,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z155,z3,z5,z6]),(0,[z223,z222,z1,z2,z3,z5,z6])],[(0,[z564,z0,z1,z2,z3,z5,z6]),(0,[z565,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z566,z5,z6]),(0,[z0,z97,z84,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z567,z6]),(0,[z17,z0,z1,z2,z3,z82,z6]),(0,[z0,z1,z2,z3,z5,z6,z568]),(0,[z0,z1,z2,z3,z5,z6,z569]),(0,[z8,z0,z570,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z147]),(0,[z571,z0,z1,z2,z3,z5,z6]),(0,[z148,z18,z1,z2,z3,z5,z6]),(0,[z18,z67,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z572,z6]),(0,[z0,z1,z2,z170,z3,z5,z6]),(0,[z573,z1,z2,z3,z102,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z574])],[(0,[z0,z1,z2,z3,z575,z5,z6]),(0,[z113,z0,z1,z2,z3,z5,z6]),(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z576,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z262,z5,z6]),(0,[z0,z1,z577,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z578]),(0,[z0,z1,z2,z3,z5,z6,z579])],[(0,[z0,z1,z2,z402,z55,z3,z6]),(0,[z0,z1,z71,z84,z3,z5,z6]),(0,[z0,z1,z2,z3,z580,z5,z6]),(0,[z581,z0,z1,z2,z3,z5,z6])],[(0,[z582,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z583,z3,z5,z6]),(0,[z435,z1,z2,z3,z5,z194,z6]),(0,[z223,z0,z67,z2,z3,z5,z6]),(0,[z0,z1,z66,z2,z3,z5,z24]),(0,[z0,z1,z357,z2,z3,z5,z6])],[(0,[z148,z132,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z584,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z585]),(0,[z0,z110,z1,z2,z170,z5,z6]),(0,[z0,z1,z586,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z587])],[(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z68,z5,z6]),(0,[z589,z0,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z198,z6])]],
   [[(0,[z0,z1,z590,z2,z3,z5,z6])],[(0,[z0,z1,z591,z2,z3,z5,z6]),(0,[z296,z0,z1,z2,z120,z5,z6]),(0,[z0,z1,z2,z3,z485,z5,z6]),(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z0,z570,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z102,z5,z6])],[(0,[z168,z1,z156,z2,z3,z5,z6]),(0,[z380,z18,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z24]),(0,[z593,z0,z1,z2,z3,z5,z6]),(1,[z60,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z594,z5,z6]),(0,[z132,z1,z2,z15,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z595,z6])],[(0,[z0,z1,z2,z3,z596,z5,z6]),(0,[z1,z2,z3,z5,z6,z14,z96]),(0,[z1,z2,z3,z5,z6,z6,z14]),(0,[z0,z1,z2,z3,z5,z6,z597])],[(0,[z0,z1,z2,z3,z141,z5,z6]),(0,[z1,z2,z3,z5,z194,z6,z14])],[(0,[z113,z0,z1,z156,z3,z5,z6]),(0,[z160,z0,z1,z2,z3,z5,z6]),(0,[z598,z0,z1,z2,z3,z5,z6]),(0,[z133,z1,z2,z3,z5,z23,z6]),(0,[z0,z1,z599,z2,z3,z5,z6]),(0,[z0,z1,z72,z2,z3,z5,z22])],[(0,[z600,z0,z1,z2,z3,z5,z6]),(0,[z39,z1,z156,z2,z3,z5,z6]),(1,[z0,z1,z601,z3,z5,z6]),(0,[z17,z0,z1,z71,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z602]),(0,[z0,z603,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z604,z5,z6]),(0,[z168,z40,z1,z2,z3,z5,z6]),(0,[z231,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z23,z6]),(1,[z0,z1,z92,z3,z5,z6]),(0,[z0,z89,z1,z2,z3,z5,z6]),(0,[z353,z1,z2,z3,z5,z199,z6])],[(0,[z1,z2,z34,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z605,z6]),(0,[z17,z0,z70,z2,z3,z5,z6]),(1,[z224,z1,z2,z3,z5,z6])],[(0,[z0,z606,z1,z2,z3,z5,z6]),(0,[z0,z110,z1,z2,z3,z5,z6]),(0,[z17,z0,z1,z601,z3,z5,z6]),(0,[z223,z0,z1,z2,z3,z5,z23]),(0,[z607,z0,z1,z2,z3,z5,z6]),(1,[z0,z570,z2,z3,z5,z6]),(0,[z88,z0,z1,z72,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z608,z6]),(0,[z0,z1,z609,z2,z3,z5,z6]),(0,[z610,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z611,z5,z6]),(1,[z0,z89,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z54]),(0,[z132,z1,z156,z2,z3,z5,z6]),(0,[z1,z2,z3,z102,z5,z6,z14]),(0,[z296,z0,z110,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z363]),(0,[z612,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z613,z3,z5,z6])],[(0,[z614,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z6,z615]),(0,[z0,z1,z616,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z617])],[(0,[z0,z1,z2,z3,z5,z12,z6]),(0,[z168,z1,z2,z3,z5,z16,z6]),(0,[z0,z1,z2,z3,z618,z5,z6]),(0,[z0,z1,z619,z2,z3,z5,z6]),(0,[z620,z0,z1,z2,z3,z5,z6]),(0,[z347,z1,z2,z3,z120,z5,z6]),(0,[z0,z1,z621,z2,z3,z5,z6])],[(0,[z88,z0,z1,z2,z3,z5,z19])]],
   [[(0,[z0,z1,z622,z2,z3,z5,z6]),(0,[z168,z1,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z44,z3,z5,z6]),(0,[z17,z0,z2,z3,z5,z6,z24]),(0,[z0,z70,z1,z2,z44,z3,z6]),(0,[z0,z1,z2,z3,z5,z6,z11])],[(0,[z0,z132,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z623]),(0,[z0,z624,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z625,z6]),(0,[z18,z1,z2,z3,z10,z5,z6]),(0,[z0,z626,z1,z2,z3,z5,z6]),(0,[z0,z1,z627,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z628]),(0,[z88,z0,z483,z2,z3,z5,z6]),(0,[z0,z444,z66,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z629,z6])],[(0,[z0,z1,z2,z3,z5,z314,z6]),(0,[z0,z1,z72,z2,z3,z5,z116])],[(0,[z211,z0,z1,z2,z3,z5,z6]),(0,[z0,z97,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z5,z6,z630]),(0,[z541,z1,z2,z3,z5,z22,z6]),(0,[z0,z1,z631,z2,z3,z5,z6])],[(0,[z74,z0,z13,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z6,z73]),(0,[z0,z1,z2,z3,z5,z518,z6]),(0,[z0,z1,z2,z3,z5,z6,z632]),(1,[z353,z1,z2,z3,z5,z6])],[(0,[z38,z1,z2,z15,z3,z5,z6]),(0,[z633,z0,z1,z2,z3,z5,z6])],[(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z15,z3,z81,z5,z6]),(0,[z40,z18,z1,z2,z3,z5,z6]),(0,[z65,z18,z1,z2,z3,z5,z6]),(1,[z18,z1,z2,z3,z5,z109]),(0,[z635,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z636,z3,z5,z6])]],
   [[(0,[z637,z0,z1,z2,z3,z5,z6]),(0,[z638,z0,z1,z2,z3,z5,z6]),(0,[z88,z321,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z639,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z640])],[(0,[z18,z1,z84,z2,z3,z5,z6]),(0,[z0,z1,z641,z2,z3,z5,z6]),(0,[z0,z1,z642,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z643,z5,z6]),(0,[z132,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z530,z2,z3,z5,z6]),(0,[z0,z1,z25,z93,z3,z5,z6]),(0,[z0,z1,z2,z326,z3,z5,z6])],[(0,[z644,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z645,z5,z6]),(0,[z231,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z41,z94,z5]),(0,[z8,z0,z1,z2,z3,z432,z6]),(1,[z0,z1,z2,z3,z146,z6])],[(0,[z0,z1,z2,z3,z534,z5,z6]),(0,[z0,z1,z2,z3,z646,z5,z6]),(0,[z0,z1,z66,z2,z3,z5,z23])],[(0,[z0,z1,z2,z3,z647,z5,z6]),(0,[z100,z1,z2,z3,z5,z6,z14]),(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z649,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z650]),(0,[z8,z0,z1,z72,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z199,z6])],[(0,[z651,z0,z1,z2,z3,z5,z6]),(0,[z242,z0,z1,z2,z3,z5,z6]),(0,[z18,z97,z1,z2,z3,z5,z6])],[(0,[z80,z113,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z652,z3,z5,z6]),(0,[z0,z1,z2,z55,z3,z5,z6]),(1,[z347,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z653,z3,z5,z6]),(0,[z1,z169,z2,z3,z5,z6,z14]),(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z654,z2,z3,z5,z6]),(0,[z655,z0,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z3,z5,z6,z116]),(0,[z656,z0,z1,z2,z3,z5,z6]),(1,[z573,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z49,z5,z6,z14]),(0,[z657,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z562,z3,z5,z6]),(0,[z65,z0,z1,z2,z3,z10,z6])],[(0,[z18,z1,z2,z3,z5,z109,z6]),(0,[z0,z1,z2,z3,z5,z6,z658]),(0,[z1,z2,z3,z10,z5,z227,z6])],[(0,[z168,z0,z1,z2,z3,z5,z6]),(0,[z148,z0,z1,z2,z3,z16,z6]),(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z296,z0,z2,z3,z120,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z660]),(0,[z0,z1,z2,z3,z661,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z662])],[(0,[z1,z2,z3,z5,z6,z14,z378]),(0,[z0,z1,z2,z3,z120,z5,z6]),(0,[z245,z0,z1,z2,z3,z5,z6])],[(1,[z131,z0,z1,z2,z3,z6]),(1,[z0,z1,z469,z2,z3,z6]),(0,[z0,z1,z2,z3,z663,z5,z6]),(0,[z8,z1,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z5,z6,z14,z384]),(0,[z0,z1,z2,z3,z5,z6,z210]),(0,[z0,z1,z2,z3,z664,z5,z6]),(0,[z358,z0,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z87,z6]),(0,[z0,z1,z2,z3,z5,z6,z665])],[(0,[z0,z1,z2,z3,z666,z5,z6]),(0,[z0,z1,z667,z2,z3,z5,z6]),(0,[z1,z72,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z668,z6]),(0,[z0,z1,z2,z3,z82,z5,z6]),(0,[z0,z1,z2,z669,z3,z5,z6])],[(0,[z670,z0,z1,z2,z3,z5,z6]),(0,[z671,z0,z1,z2,z3,z5,z6]),(0,[z0,z672,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z673,z5,z6]),(0,[z0,z1,z2,z674,z3,z5,z6]),(0,[z277,z1,z2,z3,z94,z5,z6]),(0,[z0,z1,z675,z2,z3,z5,z6]),(0,[z676,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z677,z5,z6]),(0,[z1,z2,z3,z10,z5,z6,z14]),(0,[z0,z1,z2,z3,z678,z5,z6]),(0,[z0,z1,z479,z2,z3,z5,z6])],[(0,[z0,z1,z679,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z16,z6]),(1,[z69,z0,z1,z2,z6,z73]),(0,[z0,z1,z483,z2,z3,z5,z6])],[(0,[z17,z38,z0,z1,z2,z3,z6]),(0,[z573,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z155,z3,z5,z6])],[(0,[z680,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z82,z5,z6,z24]),(0,[z223,z224,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z681])],[(0,[z0,z1,z2,z3,z5,z682,z6]),(0,[z0,z1,z683,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z684,z5,z6]),(0,[z0,z1,z2,z685,z3,z5,z6]),(0,[z0,z67,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z432,z6]),(0,[z65,z0,z1,z2,z3,z6,z73])],[(0,[z80,z1,z2,z3,z141,z5,z6]),(0,[z131,z0,z1,z2,z3,z5,z6]),(0,[z38,z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z5,z686,z6])],[(0,[z0,z1,z687,z2,z3,z5,z6]),(0,[z0,z1,z2,z688,z3,z5,z6]),(0,[z223,z0,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z5,z23,z6,z363])],[(0,[z0,z1,z2,z3,z5,z689,z6]),(0,[z1,z683,z2,z3,z5,z6,z14]),(0,[z0,z1,z71,z55,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z690,z6])],[(0,[z0,z1,z691,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z87,z194,z6]),(0,[z0,z1,z2,z3,z5,z6,z692]),(0,[z95,z0,z1,z71,z3,z5,z6]),(0,[z88,z0,z1,z2,z5,z6,z19])],[(0,[z693,z0,z1,z2,z3,z5,z6]),(0,[z290,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z462,z5,z6])],[(0,[z39,z0,z1,z156,z3,z5,z6]),(0,[z0,z1,z2,z3,z694,z5,z6]),(1,[z657,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z92,z3,z5,z6]),(0,[z0,z1,z601,z2,z3,z5,z6])],[(0,[z695,z0,z1,z2,z3,z5,z6]),(0,[z696,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z44,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z3,z697,z5,z6])],[(0,[z74,z1,z2,z3,z5,z6,z14]),(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z699,z2,z3,z5,z6]),(1,[z541,z1,z2,z3,z5,z6])],[(1,[z1,z2,z3,z5,z6,z14]),(0,[z0,z1,z2,z44,z170,z5,z6]),(0,[z17,z657,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z700,z3,z5,z6]),(0,[z0,z444,z1,z2,z3,z5,z6])],[(0,[z1,z13,z2,z3,z5,z16,z6]),(0,[z0,z1,z2,z3,z701,z5,z6]),(0,[z702,z0,z1,z2,z3,z5,z6]),(0,[z703,z0,z1,z2,z3,z5,z6]),(0,[z704,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z705,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z102,z6]),(0,[z88,z0,z1,z562,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z3,z5,z6]),(0,[z0,z708,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z709])],[(0,[z710,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z448,z14]),(0,[z1,z711,z2,z3,z5,z6]),(0,[z0,z1,z2,z166,z432,z6]),(0,[z712,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z713,z6]),(1,[z1,z707,z3,z5,z6]),(0,[z223,z2,z3,z5,z14,z24]),(0,[z714,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z14,z186]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z1,z169,z2,z3,z141,z6]),(0,[z67,z2,z3,z5,z23,z14]),(0,[z0,z1,z2,z44,z262,z6]),(0,[z0,z1,z72,z166,z5,z6]),(0,[z0,z1,z3,z5,z6,z716])],[(1,[z717,z2,z3,z5,z6]),(0,[z718,z1,z2,z3,z41,z5]),(0,[z0,z1,z2,z3,z5,z719])],[(0,[z133,z1,z2,z3,z5,z6]),(0,[z1,z707,z34,z3,z5,z6]),(0,[z168,z1,z2,z720,z5,z6]),(0,[z1,z2,z15,z720,z5,z6]),(0,[z0,z1,z721,z2,z3,z5]),(0,[z722,z1,z2,z3,z5,z6]),(0,[z76,z1,z2,z326,z5,z6])],[(0,[z0,z1,z3,z5,z6,z723]),(0,[z460,z1,z2,z3,z5,z14]),(0,[z1,z2,z3,z5,z280,z14]),(0,[z0,z1,z2,z3,z724,z6])],[(0,[z148,z1,z2,z3,z5,z147]),(0,[z0,z1,z725,z3,z5,z6]),(0,[z1,z2,z3,z43,z16,z6]),(0,[z1,z2,z3,z68,z16,z6]),(0,[z1,z2,z3,z5,z109,z726]),(0,[z727,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z728,z6]),(0,[z78,z1,z2,z3,z5,z138]),(0,[z0,z1,z2,z729,z5,z6])]],
   [[(0,[z1,z13,z2,z3,z5,z147]),(0,[z0,z1,z601,z3,z5,z138])],[(0,[z18,z1,z2,z3,z5,z14]),(0,[z0,z1,z92,z3,z5,z138]),(1,[z0,z1,z3,z6,z730])],[(0,[z0,z1,z2,z3,z5,z731]),(0,[z732,z1,z2,z3,z5,z6]),(0,[z0,z1,z733,z2,z5,z6]),(0,[z734,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z730])],[(0,[z231,z55,z3,z5,z6,z14]),(0,[z358,z1,z2,z3,z6,z14]),(0,[z1,z2,z3,z735,z5,z6]),(0,[z1,z2,z3,z5,z736,z6]),(0,[z0,z1,z737,z3,z5,z6]),(0,[z738,z1,z2,z3,z5,z6]),(0,[z0,z1,z739,z3,z5,z6]),(0,[z0,z444,z2,z3,z5,z23])],[(0,[z1,z2,z15,z446,z5,z6]),(0,[z0,z1,z2,z3,z6,z740]),(0,[z0,z2,z3,z741,z194,z6]),(0,[z742,z1,z2,z3,z5,z6])],[(0,[z18,z1,z601,z3,z5,z6]),(0,[z0,z1,z743,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z744]),(0,[z245,z0,z745,z2,z3,z5]),(0,[z0,z89,z357,z3,z5,z6]),(0,[z426,z444,z2,z3,z5,z6])],[(0,[z347,z1,z2,z3,z5,z6]),(0,[z192,z13,z2,z3,z5,z6]),(0,[z718,z1,z2,z3,z5,z6]),(0,[z17,z0,z310,z2,z3,z6]),(0,[z0,z746,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z747,z6])],[(0,[z0,z1,z748,z3,z5,z6]),(0,[z168,z1,z2,z604,z5,z6]),(0,[z0,z1,z749,z3,z5,z6]),(0,[z0,z750,z2,z3,z5,z6]),(0,[z129,z1,z3,z5,z6,z378]),(0,[z0,z751,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z752,z6]),(0,[z1,z2,z101,z5,z6,z210]),(0,[z18,z570,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z107,z6])],[(0,[z454,z13,z2,z3,z5,z6]),(0,[z38,z1,z2,z3,z141,z6]),(0,[z18,z89,z2,z3,z5,z6]),(0,[z65,z0,z1,z2,z262,z6])],[(0,[z17,z0,z621,z2,z3,z6]),(0,[z0,z1,z520,z93,z5,z6])],[(0,[z354,z1,z2,z3,z5,z14]),(0,[z88,z0,z1,z2,z166,z5])],[(0,[z0,z1,z469,z2,z3,z6]),(0,[z40,z1,z2,z720,z5,z6]),(0,[z753,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z754]),(0,[z1,z2,z3,z5,z6,z755]),(0,[z1,z2,z3,z5,z756,z6]),(0,[z0,z1,z2,z3,z6,z757])],[(0,[z28,z1,z2,z3,z6,z14]),(0,[z0,z1,z2,z3,z758,z6]),(0,[z325,z570,z2,z3,z5,z6]),(0,[z0,z1,z2,z155,z166,z5]),(0,[z0,z483,z357,z3,z5,z6])],[(0,[z0,z1,z2,z102,z6,z757])],[(0,[z0,z1,z2,z3,z5,z759]),(0,[z717,z13,z2,z3,z5,z6]),(0,[z1,z203,z2,z3,z5,z6]),(0,[z0,z1,z2,z760,z5,z6]),(0,[z0,z1,z2,z3,z5,z761]),(0,[z0,z1,z2,z44,z542,z6]),(0,[z1,z2,z3,z5,z6,z762]),(0,[z0,z483,z2,z3,z226,z6])]],
   [[(0,[z0,z1,z763,z3,z5,z6]),(0,[z245,z0,z764,z2,z3,z5])],[(0,[z18,z483,z2,z3,z5,z6]),(0,[z765,z1,z2,z3,z5,z6]),(0,[z48,z1,z71,z3,z49,z6]),(0,[z389,z89,z2,z3,z5,z6])],[(0,[z80,z247,z2,z3,z5,z6]),(0,[z38,z1,z2,z3,z534,z6]),(0,[z2,z55,z3,z5,z14,z24]),(0,[z1,z46,z94,z5,z6,z14]),(0,[z766,z0,z1,z2,z5,z6]),(0,[z88,z0,z1,z562,z5,z19])],[(0,[z1,z3,z5,z6,z14,z767]),(0,[z1,z2,z3,z5,z6,z768])],[(0,[z1,z2,z216,z3,z5,z6]),(0,[z100,z2,z3,z5,z6,z416]),(0,[z1,z2,z3,z769,z5,z6]),(0,[z770,z1,z2,z3,z5,z6]),(0,[z771,z1,z2,z3,z5,z6]),(0,[z0,z1,z772,z3,z5,z6])],[(0,[z0,z1,z2,z3,z773,z6]),(0,[z0,z1,z2,z3,z5,z774]),(0,[z0,z1,z357,z3,z146,z6])],[(0,[z0,z1,z2,z775,z5,z6]),(0,[z1,z156,z707,z3,z5,z6]),(0,[z776,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z777,z5,z6]),(0,[z1,z778,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z281,z11]),(0,[z321,z1,z2,z3,z226,z6])],[(0,[z38,z1,z2,z3,z140,z6]),(0,[z40,z1,z2,z309,z5,z6]),(0,[z1,z2,z3,z5,z227,z6]),(0,[z1,z779,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z780,z6]),(0,[z0,z1,z2,z781,z5,z6]),(0,[z0,z1,z2,z3,z782,z6]),(1,[z0,z1,z2,z6,z757]),(0,[z1,z783,z2,z3,z5,z6])]],
   [[(0,[z80,z131,z13,z2,z3,z6]),(0,[z18,z1,z2,z3,z10,z11]),(0,[z1,z2,z3,z5,z6,z784]),(0,[z1,z2,z3,z785,z5,z6])],[(0,[z454,z0,z2,z3,z5,z24]),(0,[z18,z1,z2,z3,z146,z6]),(0,[z1,z2,z3,z5,z6,z786]),(0,[z245,z0,z1,z46,z94,z5]),(0,[z0,z1,z599,z94,z5,z6]),(0,[z245,z0,z1,z2,z166,z5]),(0,[z389,z483,z2,z3,z5,z6])],[(0,[z657,z1,z2,z3,z5,z6]),(0,[z168,z1,z2,z3,z5,z147]),(0,[z1,z2,z15,z3,z5,z147]),(0,[z0,z1,z787,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z788]),(0,[z1,z2,z3,z5,z6,z789]),(0,[z790,z1,z2,z3,z5,z6]),(0,[z0,z570,z2,z166,z5,z6])],[(0,[z0,z1,z2,z3,z5,z726]),(0,[z1,z2,z3,z5,z6,z791]),(0,[z792,z1,z2,z3,z5,z6]),(0,[z793,z1,z2,z3,z5,z6]),(0,[z794,z1,z2,z3,z5,z6])],[(0,[z0,z1,z795,z2,z3,z6])],[(0,[z1,z2,z3,z5,z6,z14]),(0,[z1,z796,z2,z3,z5,z6]),(0,[z797,z1,z2,z3,z5,z6]),(0,[z8,z76,z1,z3,z5,z116])],[(0,[z221,z1,z2,z3,z5,z6]),(0,[z798,z1,z2,z3,z5,z6]),(0,[z799,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z800,z6]),(0,[z0,z1,z2,z5,z6,z719])],[(0,[z1,z92,z3,z5,z6,z14]),(0,[z0,z2,z170,z801,z5,z6]),(0,[z802,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z6,z803]),(0,[z0,z804,z2,z3,z5,z6]),(0,[z110,z2,z3,z5,z14,z24]),(0,[z0,z1,z71,z92,z3,z6]),(0,[z0,z1,z772,z2,z5,z6]),(0,[z0,z1,z2,z5,z6,z757])],[(0,[z0,z1,z2,z3,z5,z805]),(0,[z1,z2,z3,z141,z806,z6]),(1,[z1,z2,z3,z5,z726]),(0,[z277,z1,z2,z3,z41,z5]),(0,[z0,z1,z2,z3,z807,z6]),(0,[z389,z1,z2,z3,z146,z6])],[(0,[z231,z0,z402,z55,z3,z6]),(0,[z0,z1,z72,z155,z94,z5])],[(0,[z1,z156,z2,z3,z5,z147]),(0,[z18,z1,z469,z2,z3,z6]),(0,[z18,z1,z2,z3,z5,z259]),(0,[z808,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z809]),(0,[z810,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z3,z107,z116])],[(0,[z1,z2,z15,z5,z6,z210]),(0,[z1,z2,z3,z5,z56,z14]),(0,[z0,z1,z2,z262,z5,z6]),(0,[z78,z1,z2,z262,z5,z6]),(0,[z1,z2,z3,z5,z6,z811])],[(0,[z1,z2,z5,z6,z14,z812]),(0,[z0,z2,z763,z3,z5,z6]),(0,[z813,z1,z2,z3,z5,z6]),(0,[z0,z814,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z815]),(0,[z0,z1,z2,z3,z816,z6]),(0,[z1,z2,z817,z5,z6,z14]),(0,[z473,z1,z2,z3,z5,z14]),(0,[z0,z1,z92,z262,z5,z6]),(0,[z818,z1,z2,z3,z5,z6]),(0,[z0,z70,z2,z3,z295,z6]),(0,[z819,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z820])],[(0,[z1,z156,z288,z3,z5,z6]),(0,[z0,z1,z2,z720,z5,z6]),(0,[z69,z1,z2,z6,z14,z73]),(0,[z17,z0,z2,z3,z741,z6]),(0,[z0,z1,z2,z3,z821,z6]),(0,[z0,z482,z2,z326,z5,z6])]],
   [[(0,[z1,z717,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z822,z6]),(0,[z0,z1,z2,z3,z6,z823]),(0,[z148,z1,z2,z3,z518,z6]),(0,[z1,z2,z3,z5,z14,z493]),(0,[z824,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z825,z5,z6]),(0,[z65,z0,z1,z495,z2,z3])],[(0,[z0,z2,z3,z5,z6,z826]),(0,[z0,z827,z2,z3,z5,z6]),(0,[z0,z1,z46,z94,z5,z6]),(0,[z828,z1,z2,z3,z5,z6]),(0,[z0,z1,z829,z3,z5,z6])],[(0,[z830,z0,z1,z2,z3,z6]),(0,[z482,z2,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z432,z6]),(1,[z0,z2,z801,z5,z6])],[(0,[z0,z1,z831,z3,z5,z6]),(0,[z277,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z832]),(0,[z833,z0,z1,z2,z3,z6])],[(0,[z657,z1,z2,z3,z5,z138]),(0,[z834,z1,z2,z3,z5,z6]),(0,[z835,z1,z2,z3,z5,z6])],[(0,[z425,z0,z55,z3,z5,z6]),(0,[z28,z0,z1,z71,z3,z6]),(0,[z0,z1,z3,z49,z6,z730])],[(0,[z65,z1,z66,z2,z3,z14]),(0,[z1,z2,z836,z3,z5,z6]),(0,[z837,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z838,z5,z6]),(0,[z1,z563,z2,z3,z5,z14]),(0,[z347,z1,z2,z3,z119,z6]),(0,[z78,z1,z2,z286,z5,z6]),(0,[z0,z2,z3,z5,z741,z6]),(0,[z0,z1,z2,z839,z5,z6]),(0,[z325,z1,z2,z3,z432,z6]),(0,[z88,z0,z89,z2,z5,z19])]],
   [[(0,[z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z566,z5,z14]),(0,[z115,z1,z2,z3,z6,z14]),(0,[z1,z2,z326,z5,z6,z14]),(0,[z840,z1,z2,z3,z5,z6]),(0,[z0,z1,z601,z286,z5,z6]),(0,[z799,z1,z2,z3,z5,z138]),(0,[z17,z435,z1,z2,z3,z6])],[(0,[z1,z2,z720,z81,z5,z6]),(0,[z1,z2,z3,z5,z572,z14]),(0,[z0,z1,z2,z841,z5,z6]),(0,[z1,z2,z3,z5,z6,z842]),(0,[z0,z1,z92,z286,z5,z6]),(0,[z0,z1,z2,z166,z107,z6])],[(0,[z1,z2,z3,z5,z6,z843]),(0,[z0,z110,z2,z801,z5,z6]),(0,[z0,z1,z2,z844,z5,z6]),(0,[z1,z2,z845,z3,z5,z6])],[(0,[z17,z2,z3,z194,z6,z14]),(0,[z1,z2,z3,z5,z6,z846]),(0,[z0,z1,z3,z5,z22,z716])],[(0,[z0,z1,z2,z3,z5,z847]),(0,[z148,z108,z1,z2,z3,z6]),(0,[z0,z1,z2,z848,z5,z6]),(0,[z849,z1,z2,z3,z5,z6]),(0,[z17,z0,z627,z2,z3,z6]),(0,[z850,z1,z2,z3,z5,z6])],[(0,[z0,z1,z851,z2,z5,z6]),(0,[z1,z2,z3,z5,z6,z852]),(0,[z853,z1,z2,z3,z5,z6]),(0,[z0,z1,z562,z3,z226,z6]),(0,[z1,z2,z3,z5,z6,z854])],[(0,[z1,z156,z3,z5,z6,z35]),(0,[z855,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z262,z5,z138]),(0,[z0,z1,z72,z562,z3,z5]),(0,[z0,z1,z856,z3,z5,z6])],[(0,[z0,z1,z2,z3,z857,z6]),(0,[z1,z2,z3,z5,z6,z311]),(0,[z18,z1,z562,z3,z5,z6]),(0,[z17,z0,z2,z3,z194,z6]),(0,[z858,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z720,z5,z6]),(0,[z859,z1,z2,z3,z5,z6]),(0,[z860,z1,z2,z3,z5,z6])],[(0,[z80,z13,z2,z3,z5,z12]),(0,[z0,z717,z2,z3,z5,z6]),(0,[z0,z1,z2,z861,z5,z6]),(0,[z862,z1,z2,z5,z6,z14]),(0,[z17,z0,z92,z3,z194,z6]),(0,[z863,z1,z2,z3,z5,z6])],[(0,[z0,z2,z3,z82,z741,z6]),(0,[z864,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z865,z5,z6]),(0,[z88,z1,z2,z5,z14,z19]),(0,[z866,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z867]),(0,[z1,z2,z3,z6,z135,z363]),(0,[z0,z1,z72,z3,z5,z22]),(0,[z868,z1,z2,z3,z5,z6])],[(0,[z869,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z146,z6,z14]),(0,[z0,z97,z84,z3,z5,z6]),(0,[z870,z1,z2,z3,z5,z6]),(0,[z245,z0,z1,z3,z5,z116])],[(0,[z0,z1,z871,z3,z5,z6]),(0,[z131,z78,z1,z2,z3,z6]),(0,[z0,z1,z779,z3,z5,z6]),(0,[z18,z1,z2,z3,z41,z5]),(0,[z0,z1,z2,z872,z5,z6]),(0,[z873,z1,z2,z3,z5,z6]),(0,[z321,z89,z2,z3,z5,z6])],[(0,[z0,z1,z2,z874,z5,z6]),(0,[z332,z530,z2,z3,z5,z6]),(0,[z1,z46,z462,z94,z5,z6]),(0,[z0,z875,z2,z3,z5,z6]),(0,[z0,z876,z2,z3,z5,z6]),(0,[z76,z1,z2,z3,z432,z6])],[(0,[z877,z0,z1,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z336]),(0,[z389,z1,z562,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z878]),(0,[z1,z2,z3,z5,z14,z544]),(0,[z1,z2,z879,z3,z5,z6]),(0,[z17,z18,z2,z3,z194,z6]),(0,[z880,z1,z2,z3,z5,z6]),(0,[z881,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z882,z6]),(0,[z883,z1,z2,z3,z5,z6]),(0,[z884,z1,z2,z3,z5,z6]),(0,[z203,z479,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z885]),(0,[z1,z2,z3,z5,z6,z886])],[(0,[z95,z1,z3,z6,z14,z96]),(0,[z160,z1,z2,z265,z5,z6]),(0,[z0,z1,z2,z3,z5,z138]),(0,[z887,z1,z2,z3,z5,z6])],[(0,[z1,z156,z3,z5,z381,z6]),(0,[z1,z2,z3,z5,z6,z888]),(0,[z0,z1,z357,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z147]),(0,[z0,z1,z772,z94,z5,z6]),(0,[z0,z1,z72,z3,z5,z539])],[(0,[z1,z2,z3,z5,z12,z14]),(0,[z231,z0,z55,z3,z5,z6]),(0,[z0,z1,z71,z3,z646,z6]),(0,[z17,z0,z2,z3,z11,z24]),(0,[z889,z1,z2,z3,z5,z6]),(0,[z321,z483,z2,z3,z5,z6])],[(0,[z1,z2,z44,z102,z6,z14]),(0,[z0,z1,z166,z5,z6,z116]),(0,[z0,z1,z890,z3,z5,z6])],[(0,[z18,z1,z2,z3,z5,z6]),(0,[z38,z1,z2,z3,z371,z6]),(0,[z891,z1,z2,z3,z5,z6]),(0,[z65,z0,z1,z66,z2,z3])]],
   [[(0,[z892,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z625,z14]),(0,[z0,z1,z893,z3,z5,z6]),(0,[z0,z745,z2,z3,z5,z6]),(0,[z894,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z895]),(0,[z1,z2,z3,z5,z896,z6])],[(0,[z80,z13,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z629,z14]),(0,[z18,z1,z92,z3,z5,z6]),(0,[z17,z0,z2,z3,z194,z138]),(0,[z897,z1,z2,z3,z5,z6])],[(0,[z0,z110,z2,z125,z5,z6]),(0,[z112,z0,z2,z3,z5,z24]),(0,[z0,z1,z898,z3,z5,z6]),(0,[z0,z89,z2,z3,z226,z6]),(1,[z0,z1,z2,z5,z719])],[(0,[z143,z1,z2,z3,z5,z14]),(0,[z1,z899,z2,z3,z5,z6]),(0,[z1,z2,z166,z5,z6,z14]),(0,[z1,z2,z3,z432,z6,z14]),(0,[z900,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z901,z5]),(0,[z902,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z3,z5,z116])],[(0,[z325,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z379]),(0,[z1,z2,z3,z5,z6,z185]),(0,[z0,z763,z55,z3,z5,z6]),(0,[z78,z1,z2,z3,z5,z56]),(0,[z224,z1,z2,z3,z5,z23]),(0,[z1,z903,z2,z3,z5,z6]),(0,[z1,z2,z3,z904,z5,z6]),(0,[z65,z0,z444,z66,z2,z3])],[(0,[z1,z2,z3,z68,z6,z384]),(0,[z0,z1,z601,z3,z5,z56]),(0,[z223,z224,z2,z3,z5,z24]),(0,[z321,z1,z2,z3,z146,z6])],[(0,[z0,z1,z2,z3,z905,z6]),(0,[z1,z2,z3,z5,z6,z726]),(0,[z231,z18,z55,z3,z5,z6]),(0,[z906,z1,z2,z3,z5,z6]),(0,[z907,z1,z2,z3,z5,z6]),(0,[z0,z1,z92,z3,z5,z56])],[(0,[z0,z1,z2,z3,z908,z6]),(0,[z389,z1,z2,z3,z5,z6])]],
   [[(0,[z909,z1,z2,z3,z5,z6]),(0,[z65,z18,z1,z66,z2,z3]),(0,[z0,z67,z2,z3,z5,z448]),(0,[z0,z2,z3,z5,z6,z754]),(0,[z0,z1,z46,z41,z94,z5]),(0,[z1,z910,z2,z3,z5,z6]),(0,[z0,z570,z2,z326,z5,z6]),(0,[z1,z2,z3,z5,z911,z6]),(0,[z0,z1,z2,z155,z5,z199])],[(0,[z0,z1,z2,z3,z912,z6]),(0,[z1,z530,z2,z3,z5,z14]),(0,[z0,z2,z801,z120,z5,z6]),(0,[z358,z0,z1,z2,z44,z6]),(0,[z657,z1,z2,z262,z5,z6]),(0,[z1,z2,z3,z5,z6,z913]),(0,[z914,z1,z2,z3,z5,z6]),(0,[z115,z0,z1,z66,z2,z3]),(0,[z915,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z916])],[(0,[z0,z1,z3,z917,z5,z6]),(0,[z18,z1,z72,z3,z5,z22]),(0,[z231,z221,z55,z3,z5,z6]),(0,[z0,z1,z2,z918,z5,z6]),(0,[z348,z0,z1,z3,z6,z96])],[(0,[z18,z1,z2,z3,z5,z608]),(0,[z0,z1,z919,z3,z5,z6]),(0,[z920,z1,z2,z3,z5,z6])],[(0,[z40,z1,z2,z15,z5,z6]),(0,[z8,z18,z1,z3,z5,z116]),(0,[z921,z1,z2,z3,z5,z6]),(0,[z922,z1,z2,z3,z5,z6]),(0,[z923,z1,z2,z3,z5,z6]),(0,[z0,z1,z71,z649,z3,z6]),(0,[z924,z1,z2,z3,z5,z6])],[(0,[z0,z1,z925,z3,z5,z6]),(0,[z70,z2,z3,z82,z6,z14]),(0,[z1,z2,z3,z5,z6,z926]),(0,[z0,z1,z2,z5,z199,z719])],[(0,[z80,z252,z2,z3,z5,z6]),(0,[z8,z1,z3,z5,z14,z116])],[(0,[z0,z1,z2,z927,z5,z6]),(0,[z17,z2,z3,z5,z14,z24]),(0,[z483,z2,z3,z5,z6,z14]),(0,[z1,z2,z3,z5,z928,z6]),(0,[z0,z1,z2,z3,z929,z6]),(0,[z0,z70,z2,z3,z82,z6]),(0,[z930,z0,z1,z2,z3,z6]),(0,[z245,z0,z1,z2,z5,z19]),(0,[z245,z0,z1,z2,z3,z931]),(0,[z932,z1,z2,z3,z5,z6]),(0,[z426,z479,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z933]),(0,[z0,z934,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z14,z602]),(0,[z18,z1,z2,z3,z5,z138]),(0,[z935,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z936]),(0,[z0,z1,z2,z3,z119,z6]),(0,[z937,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z166,z5,z6]),(0,[z0,z1,z2,z155,z5,z686])],[(0,[z132,z2,z3,z209,z5,z6]),(0,[z938,z1,z2,z3,z5,z6])],[(0,[z18,z1,z2,z3,z5,z147]),(0,[z1,z939,z2,z3,z5,z6])],[(0,[z940,z1,z2,z3,z5,z23]),(0,[z0,z1,z2,z3,z5,z941]),(0,[z358,z0,z1,z2,z3,z6]),(0,[z657,z1,z2,z286,z5,z6]),(0,[z0,z1,z2,z262,z6,z11]),(1,[z0,z2,z3,z741,z6]),(0,[z942,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z6,z730,z96]),(0,[z943,z1,z2,z3,z5,z6]),(0,[z944,z1,z2,z3,z5,z6])],[(0,[z80,z13,z2,z3,z5,z147]),(0,[z1,z2,z3,z5,z668,z14]),(0,[z28,z1,z2,z216,z3,z6]),(0,[z0,z1,z2,z945,z5,z6])],[(0,[z231,z28,z0,z55,z3,z6]),(0,[z0,z1,z2,z3,z6,z946]),(0,[z88,z0,z1,z2,z146,z19])],[(0,[z97,z84,z3,z5,z6,z14]),(0,[z17,z2,z3,z87,z194,z6]),(0,[z76,z570,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z947,z6])]],
   [[(0,[z1,z2,z3,z5,z726,z14]),(0,[z0,z1,z25,z93,z5,z6]),(0,[z1,z2,z3,z948,z5,z6]),(0,[z0,z1,z66,z949,z2,z3])],[(0,[z0,z1,z2,z3,z950,z6]),(0,[z1,z951,z3,z5,z6,z14]),(0,[z952,z1,z2,z3,z5,z6]),(0,[z435,z70,z1,z2,z3,z6]),(0,[z245,z0,z1,z2,z3,z5]),(0,[z1,z2,z3,z953,z5,z6])],[(0,[z0,z1,z954,z3,z5,z6]),(0,[z1,z2,z3,z955,z5,z6]),(0,[z935,z18,z1,z2,z3,z6]),(0,[z18,z1,z2,z3,z107,z6]),(0,[z0,z1,z2,z3,z5,z956]),(0,[z1,z2,z3,z5,z957,z6]),(0,[z958,z0,z1,z3,z5,z6]),(0,[z1,z959,z2,z3,z5,z6])],[(0,[z1,z2,z3,z226,z6,z14]),(0,[z0,z1,z2,z3,z5,z960]),(0,[z0,z1,z961,z3,z5,z6]),(0,[z962,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z963]),(0,[z0,z424,z2,z170,z5,z6]),(0,[z0,z444,z2,z3,z5,z6]),(0,[z573,z1,z2,z44,z102,z6]),(0,[z0,z483,z562,z3,z5,z6])],[(0,[z131,z132,z1,z2,z3,z6]),(0,[z358,z18,z1,z2,z3,z6]),(0,[z245,z277,z1,z2,z3,z5])],[(0,[z435,z1,z2,z3,z5,z6]),(0,[z97,z2,z3,z5,z14,z24]),(0,[z964,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z730])],[(0,[z168,z1,z2,z663,z5,z6]),(0,[z18,z1,z2,z155,z5,z199]),(0,[z277,z1,z46,z94,z5,z6]),(0,[z1,z71,z3,z49,z314,z6]),(0,[z325,z1,z2,z3,z107,z6]),(0,[z0,z1,z2,z326,z107,z6])]],
   [[(0,[z168,z1,z2,z666,z5,z6]),(0,[z18,z1,z2,z3,z5,z453]),(0,[z296,z358,z0,z2,z120,z6]),(0,[z358,z347,z1,z2,z3,z6]),(0,[z17,z657,z2,z3,z194,z6]),(0,[z0,z482,z2,z3,z432,z6])],[(0,[z0,z1,z2,z965,z5,z6]),(0,[z211,z1,z2,z3,z5,z14]),(0,[z358,z0,z2,z3,z6,z24]),(0,[z0,z1,z949,z2,z3,z6])],[(0,[z245,z18,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z966,z6])],[(0,[z0,z1,z967,z2,z3,z6]),(0,[z1,z562,z3,z5,z6,z14]),(0,[z0,z1,z2,z3,z968,z6]),(0,[z321,z1,z562,z3,z5,z6])],[(0,[z0,z1,z2,z3,z969,z6]),(0,[z0,z1,z2,z970,z5,z6])],[(0,[z80,z131,z1,z2,z3,z6]),(0,[z0,z1,z2,z971,z5,z6]),(0,[z1,z2,z971,z5,z6,z14]),(0,[z972,z1,z2,z3,z5,z6]),(0,[z0,z764,z2,z3,z5,z6])],[(0,[z131,z1,z2,z3,z16,z6]),(0,[z148,z1,z2,z3,z16,z6]),(0,[z18,z1,z2,z3,z5,z509]),(0,[z17,z0,z2,z262,z194,z6]),(0,[z88,z321,z1,z2,z5,z19])],[(0,[z973,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z974,z3,z6]),(0,[z0,z1,z2,z3,z6,z135]),(0,[z0,z975,z2,z3,z5,z6])]],
   [[(0,[z131,z1,z2,z3,z6,z14]),(0,[z0,z1,z2,z5,z6,z812]),(0,[z113,z1,z34,z3,z5,z6]),(0,[z18,z1,z2,z3,z119,z6]),(0,[z18,z1,z2,z166,z5,z6]),(0,[z1,z2,z3,z5,z6,z976]),(0,[z977,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z978]),(0,[z0,z1,z2,z979,z5,z6]),(0,[z0,z171,z2,z3,z5,z24]),(0,[z224,z1,z2,z3,z5,z24])],[(0,[z1,z2,z3,z5,z23,z14]),(0,[z1,z980,z3,z5,z6,z14]),(0,[z133,z1,z2,z3,z5,z109]),(0,[z0,z1,z2,z981,z5,z6]),(0,[z8,z0,z1,z3,z5,z716]),(1,[z0,z1,z949,z2,z3])],[(0,[z0,z1,z2,z982,z5,z6]),(0,[z0,z1,z2,z983,z5,z6]),(0,[z877,z1,z3,z5,z6,z14]),(0,[z0,z1,z2,z286,z5,z6]),(0,[z0,z1,z2,z3,z5,z984]),(0,[z0,z1,z2,z326,z432,z6])],[(0,[z1,z25,z93,z5,z6,z14]),(0,[z28,z0,z2,z3,z6,z24]),(0,[z0,z70,z2,z3,z741,z6])],[(0,[z28,z0,z1,z3,z6,z96]),(0,[z985,z1,z2,z3,z5,z6]),(0,[z17,z0,z2,z3,z6,z692]),(0,[z0,z1,z2,z3,z986,z6]),(0,[z8,z0,z1,z166,z5,z116])],[(0,[z1,z2,z5,z6,z14,z987]),(0,[z18,z1,z2,z3,z5,z726]),(0,[z988,z1,z2,z3,z5,z6]),(0,[z325,z1,z2,z166,z5,z6])],[(0,[z0,z1,z2,z3,z5,z989]),(0,[z0,z444,z2,z3,z5,z138]),(0,[z76,z1,z2,z3,z107,z6]),(0,[z88,z389,z1,z2,z5,z19])],[(0,[z940,z1,z2,z3,z5,z14]),(0,[z18,z1,z25,z93,z5,z6]),(0,[z990,z0,z1,z2,z3,z6]),(0,[z296,z0,z2,z801,z5,z6]),(0,[z115,z133,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z6,z991]),(0,[z0,z992,z2,z3,z5,z6]),(0,[z60,z1,z2,z3,z10,z11])]],
   [[(0,[z1,z2,z3,z5,z6,z993]),(0,[z0,z1,z2,z3,z6,z994]),(0,[z0,z1,z2,z3,z995,z6]),(0,[z1,z2,z3,z5,z996,z6]),(0,[z997,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z998,z5,z6]),(0,[z999,z0,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1000]),(0,[z1,z2,z3,z5,z6,z1001]),(0,[z657,z1,z2,z3,z5,z56]),(0,[z1002,z1,z2,z3,z5,z6])],[(0,[z222,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z12]),(0,[z1,z2,z3,z5,z47,z14]),(0,[z1003,z1,z2,z3,z5,z6]),(0,[z1004,z1,z2,z3,z5,z6])],[(0,[z113,z1,z707,z3,z5,z6]),(0,[z168,z1,z2,z81,z5,z6]),(0,[z321,z1,z2,z3,z5,z6]),(0,[z1,z1005,z2,z3,z5,z6]),(0,[z0,z1,z2,z6,z757,z73])],[(0,[z570,z2,z3,z5,z6,z14]),(0,[z529,z1,z169,z2,z3,z6])],[(0,[z74,z316,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1006,z6]),(0,[z2,z3,z82,z5,z14,z24]),(0,[z1007,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1008]),(0,[z1009,z1,z2,z3,z5,z6]),(0,[z69,z0,z1,z2,z6,z757])],[(0,[z1,z2,z3,z485,z5,z6]),(0,[z1,z72,z3,z5,z22,z14]),(0,[z18,z1,z2,z262,z5,z6])],[(0,[z0,z1,z2,z3,z1010,z6]),(0,[z1011,z1,z2,z3,z5,z6]),(0,[z1012,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z56,z993]),(0,[z133,z1,z2,z3,z6,z135]),(0,[z0,z1,z586,z94,z5,z6])]],
   [[(0,[z148,z78,z1,z2,z3,z6]),(0,[z1013,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z107,z6,z14]),(0,[z0,z67,z92,z3,z5,z6]),(0,[z223,z0,z2,z3,z5,z24]),(0,[z0,z89,z2,z3,z146,z6])],[(0,[z1,z2,z3,z83,z5,z14]),(0,[z38,z78,z1,z2,z3,z6])],[(0,[z0,z1014,z2,z3,z5,z6]),(0,[z89,z2,z3,z5,z6,z14]),(0,[z18,z1,z46,z94,z5,z6]),(0,[z1015,z1,z2,z3,z5,z6]),(0,[z296,z0,z2,z120,z5,z6]),(0,[z0,z1,z2,z262,z5,z56])],[(0,[z0,z1,z2,z3,z1016,z5]),(0,[z0,z1,z951,z3,z5,z6]),(0,[z242,z1,z297,z3,z5,z6]),(0,[z0,z1,z2,z801,z5,z6]),(0,[z0,z1,z2,z286,z5,z138]),(0,[z0,z1,z562,z5,z6,z19]),(0,[z65,z0,z444,z2,z3,z6])],[(0,[z80,z717,z2,z3,z5,z6]),(0,[z0,z482,z2,z3,z5,z6]),(0,[z0,z1,z2,z155,z471,z5])],[(0,[z1017,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1018]),(0,[z0,z1019,z2,z3,z5,z6])],[(0,[z0,z1,z1020,z3,z5,z6]),(0,[z245,z1,z2,z3,z5,z14]),(0,[z1021,z1,z2,z3,z5,z6]),(0,[z0,z1,z1022,z3,z5,z6]),(0,[z1023,z1,z2,z3,z5,z6]),(0,[z0,z1024,z2,z3,z5,z6])]],
   [[(0,[z113,z1,z2,z3,z5,z147]),(0,[z132,z2,z3,z5,z343,z6]),(0,[z113,z1,z117,z3,z5,z6]),(0,[z0,z1,z2,z402,z3,z6]),(0,[z1,z2,z3,z5,z6,z1025]),(0,[z0,z1,z2,z3,z226,z6])],[(0,[z1,z2,z3,z5,z6,z363]),(0,[z115,z0,z1,z2,z3,z6]),(0,[z0,z483,z2,z3,z146,z6])],[(0,[z223,z18,z2,z3,z5,z24]),(0,[z0,z1,z1026,z2,z5,z6])],[(0,[z1,z1027,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1028])],[(0,[z129,z1,z34,z3,z5,z6]),(0,[z38,z1,z2,z3,z806,z6]),(0,[z296,z18,z2,z120,z5,z6]),(0,[z95,z0,z1,z3,z6,z96]),(0,[z88,z0,z1,z2,z5,z19])],[(0,[z1029,z0,z2,z3,z5,z6]),(0,[z0,z1030,z2,z3,z5,z6]),(0,[z1,z2,z3,z23,z135,z14]),(0,[z1,z683,z3,z5,z6,z35]),(0,[z211,z316,z2,z3,z5,z6]),(0,[z0,z1,z3,z1031,z5,z6]),(0,[z0,z1032,z2,z3,z5,z6])],[(0,[z80,z469,z13,z2,z3,z6]),(0,[z536,z0,z2,z3,z5,z24]),(0,[z1,z2,z3,z5,z6,z1033]),(0,[z0,z1,z3,z5,z716,z116])],[(0,[z1,z2,z15,z5,z304,z6]),(0,[z1034,z0,z1,z2,z3,z6]),(0,[z296,z347,z2,z120,z5,z6]),(0,[z0,z1,z2,z3,z5,z56]),(0,[z1,z203,z2,z3,z5,z24]),(0,[z1,z1035,z2,z3,z5,z6]),(0,[z0,z1,z2,z326,z5,z6]),(0,[z1,z2,z3,z1036,z5,z6])]],
   [[(0,[z0,z1,z3,z5,z6,z767]),(0,[z0,z1,z2,z1037,z5,z6]),(0,[z1,z2,z3,z5,z314,z6]),(0,[z1038,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z772,z5,z6]),(0,[z0,z1,z2,z1039,z5,z6]),(0,[z0,z1,z72,z3,z212,z5]),(0,[z514,z0,z1,z2,z6,z73]),(0,[z1040,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1041]),(0,[z1042,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z570,z2,z3,z432,z6])],[(1,[z1,z2,z3,z806,z6]),(0,[z1,z2,z1044,z3,z5,z6]),(0,[z0,z1,z1045,z2,z3,z6]),(0,[z0,z1,z71,z3,z49,z6]),(0,[z1046,z1,z2,z3,z5,z6])],[(0,[z1047,z1,z2,z3,z5,z6]),(0,[z0,z1,z949,z2,z3,z11])],[(0,[z0,z1,z2,z817,z5,z6])],[(0,[z1,z2,z3,z5,z147,z14]),(0,[z163,z1,z2,z3,z5,z14]),(0,[z1,z2,z3,z5,z157,z14]),(0,[z1,z1048,z2,z3,z5,z6]),(0,[z95,z18,z1,z3,z6,z96]),(0,[z88,z18,z1,z2,z5,z19]),(0,[z339,z0,z55,z3,z5,z6]),(0,[z0,z1,z71,z3,z6,z730])],[(0,[z1,z2,z3,z141,z5,z147]),(0,[z18,z97,z84,z3,z5,z6]),(0,[z1049,z1,z2,z3,z5,z6]),(0,[z17,z0,z2,z3,z194,z56]),(0,[z115,z0,z2,z3,z6,z24]),(0,[z0,z1,z2,z1050,z3,z6])],[(0,[z132,z717,z2,z3,z5,z6]),(0,[z245,z0,z1,z72,z3,z5]),(0,[z0,z1,z2,z3,z1051,z5])]],
   [[(0,[z0,z1,z1052,z3,z5,z6]),(0,[z1,z2,z3,z1053,z5,z6]),(0,[z245,z0,z1,z2,z155,z5]),(0,[z1054,z1,z2,z3,z5,z6]),(0,[z1,z72,z3,z5,z22,z311]),(0,[z1055,z1,z2,z3,z5,z6])],[(0,[z131,z38,z1,z2,z3,z6]),(0,[z38,z1,z577,z2,z3,z6]),(0,[z0,z1,z2,z44,z42,z6]),(0,[z0,z1,z1056,z3,z5,z6])],[(0,[z80,z443,z2,z3,z5,z6]),(0,[z479,z2,z3,z5,z6,z14]),(0,[z1057,z1,z2,z3,z5,z6]),(0,[z0,z1,z491,z94,z5,z6])],[(0,[z0,z1,z94,z5,z6,z538]),(0,[z245,z1058,z1,z2,z3,z5])],[(0,[z223,z222,z2,z3,z5,z24]),(0,[z0,z444,z2,z3,z6,z11])],[(0,[z18,z1,z357,z3,z5,z6]),(0,[z0,z1059,z2,z3,z5,z6])],[(0,[z0,z1,z1060,z2,z5,z6]),(0,[z76,z1,z2,z3,z5,z6]),(0,[z245,z0,z1,z2,z3,z986])],[(0,[z1061,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1062]),(0,[z0,z89,z562,z3,z5,z6])]],
   [[(0,[z0,z1063,z2,z3,z5,z6]),(0,[z65,z0,z1,z255,z2,z3]),(0,[z0,z482,z2,z3,z107,z6])],[(0,[z0,z1,z2,z3,z5,z1064]),(0,[z231,z216,z55,z3,z5,z6]),(0,[z358,z0,z67,z2,z3,z6]),(0,[z1065,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z220,z11])],[(0,[z18,z1,z2,z3,z5,z551])],[(0,[z1,z2,z3,z5,z198,z6]),(0,[z18,z1,z2,z3,z5,z75]),(0,[z358,z0,z1,z2,z262,z6]),(0,[z1066,z1,z2,z3,z5,z6]),(0,[z444,z203,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z14,z104]),(0,[z1,z2,z205,z3,z5,z14]),(0,[z1067,z1,z2,z3,z5,z6])],[(0,[z862,z0,z1,z2,z5,z6]),(0,[z0,z1,z1068,z3,z5,z6]),(0,[z1069,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1,z2,z3,z462,z41,z5]),(0,[z389,z1,z357,z3,z5,z6])],[(0,[z60,z1,z2,z3,z5,z6]),(0,[z454,z2,z3,z5,z6,z54]),(0,[z1,z357,z3,z5,z6,z14]),(0,[z18,z1,z2,z3,z5,z56]),(0,[z1071,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z801,z5,z6]),(0,[z1072,z1,z2,z3,z5,z6]),(0,[z0,z1073,z2,z3,z5,z6])],[(0,[z113,z1,z375,z3,z5,z6]),(0,[z0,z1,z2,z3,z1074,z6]),(0,[z1,z2,z3,z485,z119,z6])]],
   [[(0,[z74,z717,z2,z3,z5,z6]),(0,[z1075,z1,z2,z3,z5,z6]),(0,[z320,z0,z2,z120,z5,z6]),(0,[z0,z2,z3,z5,z138,z24])],[(0,[z28,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1076,z5,z6]),(0,[z1077,z0,z1,z2,z3,z6])],[(0,[z74,z672,z2,z3,z5,z6]),(0,[z588,z1,z2,z3,z5,z14]),(0,[z900,z1,z2,z3,z5,z56]),(0,[z1078,z1,z2,z3,z5,z6]),(0,[z1079,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z326,z5,z116])],[(0,[z0,z1,z1080,z2,z3,z6]),(0,[z1,z2,z3,z806,z16,z6]),(0,[z0,z1,z2,z1081,z5,z6]),(0,[z28,z0,z67,z2,z3,z6]),(0,[z0,z1,z1082,z3,z5,z6]),(0,[z78,z1,z601,z3,z5,z6]),(0,[z17,z78,z2,z3,z194,z6]),(0,[z325,z1,z2,z326,z5,z6])],[(0,[z0,z1,z2,z3,z1083,z6]),(0,[z78,z1,z92,z3,z5,z6]),(0,[z1084,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z10,z227,z11])],[(0,[z0,z1,z2,z3,z1085,z6]),(0,[z355,z1,z2,z3,z5,z14]),(0,[z1086,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1087]),(0,[z1,z2,z3,z5,z1088,z6])],[(0,[z39,z1,z707,z3,z5,z6]),(0,[z1089,z1,z2,z3,z5,z6]),(0,[z1090,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z6,z1091]),(0,[z1,z203,z2,z3,z5,z23]),(0,[z95,z0,z1,z3,z6,z730]),(0,[z0,z482,z2,z166,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1092]),(0,[z148,z1,z2,z3,z342,z6]),(0,[z48,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z462,z5,z6]),(0,[z18,z1,z2,z3,z5,z689]),(0,[z1,z2,z216,z402,z3,z6]),(0,[z0,z89,z2,z3,z5,z6]),(0,[z1,z1093,z2,z3,z5,z6]),(0,[z1094,z1,z2,z3,z5,z6]),(0,[z0,z1,z562,z3,z146,z6]),(0,[z1095,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z1096,z5,z6])],[(0,[z444,z2,z3,z5,z6,z14]),(0,[z18,z70,z2,z3,z82,z6]),(0,[z8,z325,z1,z3,z5,z116]),(0,[z0,z1,z72,z3,z5,z716]),(0,[z0,z1,z2,z37,z102,z6])],[(0,[z39,z1,z156,z3,z5,z6]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z28,z18,z1,z2,z3,z6]),(0,[z0,z1,z949,z2,z3,z10])],[(0,[z74,z1,z2,z3,z5,z147]),(0,[z254,z1,z2,z3,z534,z6]),(0,[z1,z1098,z2,z3,z5,z6])],[(0,[z168,z1,z2,z265,z5,z6]),(0,[z1,z2,z3,z1099,z5,z6])],[(0,[z0,z1100,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z623]),(0,[z1101,z1,z2,z3,z5,z6]),(0,[z296,z0,z2,z119,z120,z6]),(0,[z1,z2,z3,z5,z6,z1102]),(0,[z0,z1103,z2,z3,z5,z6])],[(0,[z192,z148,z1,z2,z3,z6]),(1,[z0,z763,z3,z5,z6]),(0,[z28,z221,z1,z2,z3,z6]),(0,[z0,z67,z2,z262,z5,z6]),(0,[z0,z1,z2,z3,z741,z6]),(0,[z0,z1,z2,z5,z6,z1104]),(0,[z0,z479,z2,z3,z5,z6]),(0,[z0,z1,z562,z155,z5,z6])],[(0,[z0,z1,z2,z1105,z5,z6]),(0,[z133,z1,z2,z3,z5,z14]),(0,[z0,z483,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z6,z757])]],
   [[(0,[z1,z2,z3,z5,z14,z24])],[(0,[z353,z1,z2,z3,z5,z6]),(0,[z0,z1,z980,z3,z5,z6]),(0,[z1106,z1,z2,z3,z5,z6]),(0,[z221,z1,z2,z402,z3,z6]),(0,[z0,z84,z763,z3,z5,z6]),(0,[z1107,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1108,z6]),(0,[z113,z1,z583,z3,z5,z6]),(0,[z1,z2,z155,z5,z199,z14]),(0,[z0,z1,z2,z5,z6,z1109]),(0,[z1110,z1,z2,z3,z5,z6]),(0,[z1111,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1112,z41,z5])],[(0,[z0,z1,z2,z3,z5,z1113]),(0,[z18,z1,z2,z3,z5,z109]),(0,[z110,z2,z170,z5,z6,z14]),(0,[z158,z0,z2,z3,z5,z24]),(0,[z1114,z0,z1,z2,z3,z6]),(0,[z1115,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z719,z19])],[(0,[z17,z0,z2,z286,z194,z6]),(0,[z1,z2,z3,z5,z6,z1116]),(0,[z65,z1,z66,z203,z2,z3])],[(0,[z0,z1,z2,z3,z1117,z6]),(0,[z940,z1,z2,z3,z5,z6]),(0,[z1,z795,z2,z3,z6,z14]),(0,[z1,z851,z2,z5,z6,z14]),(0,[z231,z0,z763,z3,z5,z6]),(0,[z1118,z1,z2,z3,z5,z6]),(0,[z312,z0,z2,z120,z5,z6]),(0,[z1,z2,z1119,z3,z5,z6]),(0,[z1120,z1,z2,z3,z5,z6])],[(0,[z18,z444,z2,z3,z5,z6]),(0,[z0,z1,z25,z59,z5,z6]),(0,[z0,z1,z2,z3,z10,z11])],[(0,[z143,z1,z2,z3,z5,z726]),(0,[z1121,z0,z1,z2,z3,z5]),(0,[z1,z1122,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z146,z6])]],
   [[(0,[z0,z1,z2,z5,z6,z987]),(0,[z0,z97,z284,z3,z5,z6]),(0,[z0,z26,z84,z3,z5,z6]),(0,[z245,z1079,z1,z2,z3,z5]),(0,[z0,z1,z269,z3,z49,z6])],[(0,[z69,z0,z1,z2,z262,z6]),(0,[z17,z0,z590,z2,z3,z6])],[(0,[z0,z1123,z2,z3,z5,z6]),(0,[z1124,z1,z2,z3,z5,z6])],[(0,[z211,z1,z2,z3,z5,z147]),(0,[z1,z2,z3,z713,z6,z14]),(0,[z1125,z1,z2,z3,z5,z6])],[(0,[z113,z1,z452,z3,z5,z6]),(0,[z573,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1112,z5,z6]),(0,[z614,z1,z2,z5,z6,z176]),(0,[z1,z3,z5,z6,z14,z723]),(0,[z0,z1126,z2,z3,z5,z6])],[(0,[z0,z1,z1127,z3,z5,z6]),(0,[z0,z1,z2,z3,z47,z11]),(0,[z0,z1,z2,z3,z678,z11])],[(0,[z1128,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1129,z3,z6]),(0,[z115,z1,z2,z3,z23,z14]),(0,[z1130,z1,z2,z3,z5,z6]),(0,[z1131,z1,z2,z3,z5,z6]),(0,[z76,z1,z2,z166,z5,z6]),(0,[z8,z0,z570,z3,z5,z116]),(0,[z0,z1,z1132,z3,z5,z6])]],
   [[(0,[z0,z1,z1133,z3,z5,z6]),(0,[z0,z1,z1134,z3,z5,z6]),(0,[z0,z2,z262,z5,z6,z24]),(0,[z0,z2,z3,z5,z754,z24]),(0,[z1058,z1,z2,z3,z5,z6])],[(0,[z131,z0,z1,z2,z3,z6]),(0,[z1,z2,z3,z5,z87,z6]),(0,[z0,z1,z2,z3,z1135,z6]),(0,[z132,z2,z507,z3,z5,z6]),(0,[z0,z1,z2,z3,z1136,z6]),(0,[z1,z1137,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z6,z135]),(0,[z0,z1,z2,z3,z6,z1138]),(0,[z0,z1,z2,z3,z6,z1139]),(0,[z0,z570,z2,z3,z107,z6]),(0,[z1140,z1,z2,z3,z5,z6]),(0,[z88,z0,z483,z2,z5,z19])],[(0,[z0,z70,z619,z2,z3,z6]),(0,[z2,z3,z5,z416,z14,z24]),(0,[z0,z1,z2,z3,z1141,z5]),(0,[z0,z1,z2,z3,z1142,z6]),(0,[z1,z2,z3,z5,z1143,z6]),(0,[z1144,z1,z2,z3,z5,z6])],[(0,[z18,z1,z2,z3,z5,z682]),(0,[z1145,z1,z2,z3,z5,z6]),(0,[z17,z435,z2,z3,z194,z6]),(1,[z0,z1,z3,z5,z716]),(0,[z65,z426,z1,z66,z2,z3])],[(0,[z0,z1,z2,z3,z1146,z6]),(0,[z18,z1,z2,z286,z5,z6]),(0,[z0,z1,z2,z3,z5,z716]),(0,[z1,z2,z44,z102,z198,z6])],[(0,[z1,z469,z2,z3,z6,z14]),(0,[z148,z1,z2,z3,z806,z6]),(0,[z18,z479,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1147]),(0,[z69,z0,z1,z2,z6,z73])],[(0,[z0,z1,z1148,z3,z5,z6]),(0,[z115,z0,z67,z2,z3,z6])],[(0,[z0,z1,z2,z3,z806,z6]),(0,[z1,z2,z3,z6,z135,z14]),(0,[z1149,z1,z2,z3,z5,z6]),(0,[z0,z1150,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z432,z6]),(0,[z0,z1,z2,z44,z102,z6])],[(0,[z1,z2,z3,z484,z16,z6]),(0,[z426,z1,z2,z3,z5,z6]),(0,[z2,z3,z120,z5,z14,z24]),(0,[z1,z2,z3,z5,z138,z14]),(0,[z1,z2,z3,z5,z1151,z6]),(0,[z0,z1,z2,z286,z5,z56]),(0,[z321,z1,z357,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1152,z6]),(0,[z131,z18,z1,z2,z3,z6]),(0,[z0,z1,z2,z1153,z5,z6]),(0,[z0,z1154,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z14,z261]),(0,[z0,z110,z2,z170,z5,z6]),(0,[z1,z2,z3,z5,z138,z1155])],[(0,[z88,z0,z1,z2,z5,z719]),(0,[z65,z0,z66,z479,z2,z3])],[(0,[z0,z1,z1156,z3,z5,z6]),(0,[z132,z2,z3,z5,z6,z416]),(0,[z65,z0,z1,z2,z3,z138])],[(0,[z454,z2,z3,z5,z14,z24]),(0,[z115,z18,z1,z2,z3,z6]),(0,[z0,z1157,z2,z3,z5,z6]),(0,[z0,z1,z2,z155,z5,z719])],[(0,[z18,z1,z2,z3,z5,z229]),(0,[z69,z18,z1,z2,z6,z73]),(0,[z0,z1,z2,z3,z5,z1158])],[(0,[z0,z1,z2,z3,z1159,z6]),(0,[z18,z1,z2,z3,z5,z149]),(0,[z1,z1160,z2,z3,z5,z6]),(0,[z17,z0,z2,z3,z313,z6])]],
   [[(0,[z38,z1,z2,z3,z647,z6]),(0,[z1161,z1,z2,z3,z5,z6]),(0,[z1,z1162,z2,z3,z5,z6]),(0,[z0,z1,z1163,z3,z5,z6]),(0,[z657,z1,z601,z3,z5,z6]),(0,[z0,z1,z1164,z3,z5,z6]),(0,[z1165,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1166,z6])],[(0,[z541,z1,z2,z3,z5,z6]),(0,[z657,z1,z92,z3,z5,z6]),(0,[z0,z1,z2,z3,z138,z11]),(0,[z0,z1,z2,z3,z1167,z6]),(0,[z1168,z1,z2,z3,z5,z6]),(0,[z353,z1,z2,z155,z5,z199])],[(0,[z1,z2,z3,z141,z690,z6])],[(0,[z74,z132,z2,z3,z5,z6]),(0,[z39,z1,z297,z3,z5,z6]),(0,[z1,z2,z3,z41,z5,z14]),(0,[z296,z2,z485,z120,z5,z6]),(0,[z1,z2,z3,z5,z6,z1155]),(0,[z1169,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1170,z3,z5,z6]),(0,[z1,z2,z3,z5,z237,z14]),(0,[z1,z601,z3,z5,z6,z14]),(0,[z0,z1,z2,z1171,z5,z6]),(0,[z0,z1,z2,z3,z6,z1172]),(0,[z0,z1,z949,z2,z3,z5]),(0,[z65,z0,z1,z949,z2,z3])],[(0,[z614,z1,z2,z81,z5,z6]),(0,[z1,z2,z3,z119,z6,z14]),(0,[z0,z362,z2,z3,z82,z6]),(0,[z223,z0,z2,z3,z5,z754]),(0,[z0,z1,z562,z3,z5,z6])],[(0,[z1,z2,z3,z5,z545,z14]),(0,[z28,z0,z1,z92,z3,z6]),(0,[z1,z2,z3,z5,z1173,z6]),(0,[z1174,z1,z2,z3,z5,z6]),(0,[z115,z0,z1,z2,z3,z138]),(0,[z0,z1,z357,z3,z226,z6])],[(0,[z0,z1,z2,z3,z1175,z6]),(0,[z18,z482,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1176]),(0,[z0,z70,z2,z3,z6,z617]),(0,[z115,z1,z2,z3,z6,z363]),(0,[z0,z2,z3,z5,z6,z1177])]],
   [[(0,[z0,z1,z2,z3,z1178,z6]),(0,[z0,z1,z1179,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1180]),(0,[z0,z1,z93,z772,z5,z6])],[(0,[z1,z2,z3,z10,z11,z14]),(0,[z290,z1,z2,z3,z518,z6]),(0,[z0,z1,z2,z3,z1181,z6])],[(0,[z0,z1,z2,z3,z6,z1182]),(0,[z0,z1,z2,z3,z6,z1183]),(0,[z0,z1184,z2,z3,z5,z6]),(0,[z18,z1,z2,z402,z3,z6]),(0,[z18,z1,z2,z3,z226,z6]),(0,[z0,z1,z601,z262,z5,z6]),(0,[z8,z0,z482,z3,z5,z116]),(0,[z1,z2,z3,z5,z1185,z6])],[(0,[z0,z1,z2,z3,z5,z1186]),(0,[z1,z390,z2,z3,z5,z14]),(0,[z0,z1187,z2,z3,z5,z6]),(0,[z380,z1,z2,z309,z5,z6]),(0,[z0,z1,z2,z3,z41,z5])],[(0,[z0,z1,z2,z3,z1188,z6]),(0,[z1,z1189,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1190]),(0,[z0,z1,z92,z3,z6,z11]),(0,[z0,z444,z2,z3,z5,z24]),(0,[z325,z482,z2,z3,z5,z6]),(0,[z541,z1,z72,z3,z5,z22]),(0,[z88,z0,z1,z2,z226,z19])],[(0,[z1,z2,z3,z5,z1191,z6])],[(0,[z0,z1,z2,z3,z5,z1192]),(0,[z0,z2,z3,z5,z6,z1193]),(0,[z1194,z1,z2,z3,z5,z6]),(0,[z1195,z1,z2,z3,z5,z6]),(0,[z0,z1196,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1197]),(0,[z0,z1198,z2,z3,z5,z6]),(0,[z18,z1,z2,z44,z102,z6]),(0,[z1199,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1200]),(0,[z0,z97,z763,z3,z5,z6]),(0,[z1201,z1,z2,z3,z5,z6]),(0,[z245,z0,z1,z562,z3,z5])]],
   [[],[(0,[z0,z1,z2,z3,z1202,z6]),(0,[z18,z110,z2,z170,z5,z6]),(0,[z18,z1,z2,z326,z5,z6]),(0,[z0,z1,z2,z3,z1203,z6]),(0,[z0,z1,z2,z1204,z5,z6]),(0,[z1,z2,z155,z5,z199,z185])],[(1,[z1,z2,z720,z5,z6]),(0,[z0,z1,z1205,z3,z5,z6]),(0,[z296,z2,z120,z5,z6,z14]),(0,[z389,z1,z2,z3,z226,z6])],[(0,[z17,z0,z443,z2,z3,z6]),(0,[z1,z414,z2,z3,z5,z14]),(0,[z8,z0,z1,z3,z432,z116]),(0,[z88,z0,z1,z357,z5,z19])],[(0,[z18,z1,z1045,z2,z3,z6]),(0,[z18,z1,z71,z3,z49,z6]),(0,[z245,z1,z2,z3,z462,z5]),(0,[z1206,z1,z2,z3,z5,z6])],[(0,[z133,z1,z2,z3,z5,z12]),(0,[z78,z1,z2,z3,z5,z6]),(0,[z18,z1,z2,z3,z5,z287]),(0,[z1,z2,z3,z5,z418,z14])],[(0,[z0,z1,z2,z3,z5,z1207]),(0,[z0,z1,z601,z3,z5,z6]),(0,[z1,z2,z1208,z3,z5,z6]),(0,[z1,z2,z3,z5,z1209,z6]),(0,[z0,z1210,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1211,z5,z6]),(0,[z1,z2,z3,z5,z6,z1212]),(0,[z0,z1,z92,z3,z5,z6]),(1,[z0,z1,z772,z5,z6])]],
   [[(0,[z224,z1,z2,z3,z5,z6]),(0,[z1,z2,z286,z5,z6,z14]),(0,[z1213,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1214,z6]),(0,[z0,z1,z772,z46,z5,z6])],[(0,[z0,z1,z2,z3,z1215,z6]),(0,[z1,z2,z262,z5,z6,z14]),(0,[z1,z2,z3,z5,z1216,z6]),(0,[z0,z570,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1217]),(0,[z358,z1,z2,z3,z485,z6]),(0,[z1218,z1,z2,z3,z5,z6]),(0,[z0,z1219,z2,z3,z5,z6])],[(0,[z1,z2,z15,z401,z5,z6]),(0,[z1,z156,z3,z122,z5,z6]),(0,[z358,z0,z1,z2,z6,z73]),(0,[z1,z2,z3,z5,z1220,z6])],[(0,[z1,z2,z3,z5,z6,z1221]),(0,[z1222,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z931,z6]),(0,[z76,z482,z2,z3,z5,z6])],[(0,[z80,z530,z2,z3,z5,z6]),(0,[z0,z1,z707,z3,z5,z6]),(0,[z1,z2,z3,z5,z806,z6]),(0,[z1,z71,z3,z49,z6,z14]),(0,[z0,z1,z2,z1223,z5,z6]),(0,[z0,z1224,z2,z3,z5,z6])],[(0,[z1,z2,z402,z3,z6,z14]),(0,[z2,z3,z5,z23,z14,z24]),(0,[z0,z1,z2,z3,z1225,z6]),(0,[z17,z0,z601,z3,z194,z6]),(0,[z1,z2,z1226,z3,z5,z6])],[(0,[z302,z1,z117,z3,z5,z6]),(0,[z1,z2,z3,z5,z1227,z6]),(0,[z0,z92,z3,z5,z6,z24]),(0,[z95,z0,z1,z92,z3,z6]),(0,[z115,z0,z1,z2,z3,z11]),(0,[z8,z0,z1,z562,z3,z5]),(0,[z1228,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1229]),(0,[z65,z0,z1,z92,z3,z6]),(0,[z0,z70,z2,z557,z3,z6]),(0,[z0,z1,z1230,z2,z3,z6]),(0,[z0,z1,z2,z1231,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 534) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1057).take 172) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1229)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 534, 172] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 106).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 225).take 31).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [106, 119, 31] = true :=
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

end PEqualNP.Outside.L_meta_38901

theorem PEqualNP.Outside.L_meta_38901 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4008373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38901.solve