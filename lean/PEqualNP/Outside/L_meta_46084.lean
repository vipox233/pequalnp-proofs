import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46084

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
  Nat.testBit (4277074632 * 2 ^ 32 + 4243126464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4090d0e39036c780#64 ++ 0x220486871c81b63c#64 ++ 0xc1b1d3e7907ecf8f#64 ++ 0xde0d8e9f3c83f67c#64 : BitVec 256),
   (0x0206220d068b0aaa#64 ++ 0x4010311068345855#64 ++ 0x664e223f1f8f0fff#64 ++ 0xbb327111f8fc787f#64 : BitVec 256),
   (0x0870143021505150#64 ++ 0x804380a1810a828a#64 ++ 0xd8703c38e1f1f1fd#64 ++ 0x7ec381e1c70f8f8f#64 : BitVec 256),
   (0x17802b40da01ac03#64 ++ 0x00bc015a06d00d60#64 ++ 0xdf803fc0fe01fe1c#64 ++ 0xf6fc01fe07f00ff0#64 : BitVec 256),
   (0x3deb4000fdec001c#64 ++ 0x01ef5a0007ef6000#64 ++ 0x3fffc000fffe001b#64 ++ 0xf9fffe0007fff000#64 : BitVec 256),
   (0x9f7dbfbe00000000#64 ++ 0x04fbedfdf0000000#64 ++ 0xbfffffff00000007#64 ++ 0xf5fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [13, 2]⟩, ⟨.and, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0204220d02030aa2 0x4010211068101855 0x4000223f00010fe4 0x02000111f800087f

def z1 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e223f1f8f0fff 0xbb327111f8fc787f

def z2 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703c38e1f1f1fd 0x7ec381e1c70f8f8f

def z3 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fc0fe01fe1c 0xf6fc01fe07f00ff0

def z4 : W := mkw 0x401090e30012c780 0x220084871800963c 0xc00013e70000cf84 0x0600009f3800067c

def z5 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e7907ecf8f 0xde0d8e9f3c83f67c

def z6 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff00000007 0xf5fffffff8000000

def z7 : W := mkw 0x0080400090240000 0x0004020004812000 0x01b1c000907e000b 0xd80d8e000483f000

def z8 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000fffe001b 0xf9fffe0007fff000

def z9 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffffe1f1f1ff 0xffffffffff0f8f8f

def z10 : W := mkw 0x4090d0e390268680 0x220486871c813434 0x81b1d3e7100e0e07 0xd40d8e9f38807070

def z11 : W := mkw 0x0206220c0689082a 0x4010311060344841 0x664e22181f810e7c 0xb3327110c0fc0873

def z12 : W := mkw 0x3deb0000fdc8001c 0x01ef580007ee4000 0x3fce0000ff800018 0xf1fe700007fc0000

def z13 : W := mkw 0x1ff03f70fb51fd53 0x80ff81fb87da8fea 0xdff03ff8fff1fffd 0xfeff81ffc7ff8fff

def z14 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x278fc3c700000002 0x813c7e1e38000000

def z15 : W := mkw 0x48f0d4f3b176d7d0 0xa24786a79d8bb6be 0xd9f1fffff1ffffff 0xfecf8fffff8fffff

def z16 : W := mkw 0x3de94940f964a415 0x01ef4a4a07cb2520 0x99b1ddc0e070f000 0x44cd8eee07038780

def z17 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x260e02071e0e0e02 0x8130701038f07070

def z18 : W := mkw 0x0204220c00000000 0x0010211060000000 0x260e020700000002 0x8130701038000000

def z19 : W := mkw 0x4290f2e39237cf82 0x221487971c91be7c 0xc7b1f3e79e7fcf9f 0xfe3d8f9f3cf3fe7c

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8003c00e001f01c 0x76c001e007000f80

def z21 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x0070003801f001e1 0x08038001c00f800f

def z22 : W := mkw 0x3dfb5430fdfc515c 0x81efdaa187efe28a 0x3fffc038fffe01fb 0xf9fffe01c7fff00f

def z23 : W := mkw 0x00800040da01ac03 0x0004000206d00d60 0x40000000fe01fe18 0x0200000007f00ff0

def z24 : W := mkw 0x17802b00da012803 0x00bc015806d00940 0x1f802c00fe013018 0xf0fc016007f00980

def z25 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x81b1d3c7907ece02 0xc40d8e9e3c83f670

def z26 : W := mkw 0x0200220002010802 0x0010011000100840 0x460022001e010e1c 0xb230011000f00870

def z27 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x27bfc0009e7e000b 0xd93dfe0004f3f000

def z28 : W := mkw 0x1d69000000000000 0x00eb480000000000 0x3fffc00000000003 0xf1fffe0000000000

def z29 : W := mkw 0xbfffffbefdec001c 0x05fffffdf7ef6000 0xbffffffffffe001f 0xfdfffffffffff000

def z30 : W := mkw 0x408040419036c780 0x220402020c81b63c 0x41b1c000907ecf8b 0xda0d8e000483f67c

def z31 : W := mkw 0x0204220c00000000 0x0010211060000000 0x264e201800000000 0x21327100c0000000

def z32 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0xfe4e3e3fff8fffff 0xfff271f1fffc7fff

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x18002c0060013010 0x20c0016003000980

def z34 : W := mkw 0x0860041021401050 0x80430020810a0082 0x18402c1861813070 0x20c20160c30c0983

def z35 : W := mkw 0x0006000d048a02a8 0x4000300068245015 0x264e003f1f8e01fb 0xb9327001f8fc700f

def z36 : W := mkw 0x0a76363d068b0aaa 0x4053b1b1e8345855 0xfe7e3e3f1f8f0fff 0xfff3f1f1f8fc787f

def z37 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x27cfc0001f8e001b 0xb93e7e0000fc7000

def z38 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x078003c01e000e00 0x803c001e00f00070

def z39 : W := mkw 0x17862b4dde8baeab 0x40bc315a6ef45d75 0xffce3fffff8fffff 0xfffe71fffffc7fff

def z40 : W := mkw 0x4010d0a300364380 0x220086851801b21c 0xc031d027807ec18f 0x5e018e813c03f60c

def z41 : W := mkw 0xdffdffff9036c780 0x26ffeffffc81b63c 0xffffffff907ecf8f 0xfffffffffc83f67c

def z42 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdfc03ff8ff81fffd 0xfefe01ffc7fc0fff

def z43 : W := mkw 0x0000400000240000 0x0000020000012000 0x0031c000007e0003 0x08018e000003f000

def z44 : W := mkw 0x15800940d800a401 0x00ac004a06c00520 0x99801dc0e000f000 0x44cc00ee07000780

def z45 : W := mkw 0x3dfb5430fdfc515c 0x81efdaa187efe28a 0xfffffc38fffff1ff 0xffffffe1c7ffff8f

def z46 : W := mkw 0x3fef620dffef0abe 0x41ff7b106fff7855 0x7fffe23fffff0fff 0xfbffff11fffff87f

def z47 : W := mkw 0x9f7dbfbe00105140 0x84fbedfdf000828a 0xffffffff0001f1e7 0xf7fffffff8000f8f

def z48 : W := mkw 0x5790fbe3da37ef83 0x22bc87df1ed1bf7c 0xdfb1ffe7fe7fff9f 0xfefd8fff3ff3fffc

def z49 : W := mkw 0x4010d0a300364380 0x220086851801b21c 0x0031c027007e0183 0x08018e013803f00c

def z50 : W := mkw 0x9f6d2f1c21401050 0x84fb6978e10a0082 0x3e4e2c1861813070 0x21f27160c30c0983

def z51 : W := mkw 0x02002b400201ac03 0x0010015a00100d60 0xc0003fc00001fe04 0x060001fe00000ff0

def z52 : W := mkw 0x286b400025ec001c 0x01435a00012f6000 0x207fc00001fe0003 0x0903fe00000ff000

def z53 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x18702c3861f131f1 0x28c38161c30f898f

def z54 : W := mkw 0x0860041021401050 0x80430020810a0082 0xd8403c18e181f07c 0x76c201e0c70c0f83

def z55 : W := mkw 0x0206220c04880008 0x0010311060244000 0x264e223f1f8e001f 0xb9327111f8fc7000

def z56 : W := mkw 0x9f7fbfbe0689082a 0x44fbfdfdf0344841 0xbfffffff0f810077 0xf5fffffff87c0803

def z57 : W := mkw 0x8214bfbf02030aa2 0x4410a5fdf8101855 0xc0003fff00010fe4 0x060001fff800087f

def z58 : W := mkw 0x17002b0000000000 0x00b8015800000000 0x9f803fc000000004 0xf4fc01fe00000000

def z59 : W := mkw 0x35824000fdec001c 0x01ac120007ef6000 0x1f800000fffe0018 0xf8fc000007fff000

def z60 : W := mkw 0x00820041de8baeab 0x400410020ef45d75 0x40000000ff8ffff8 0x0a00000007fc7fff

def z61 : W := mkw 0x9f7dbfbf00020280 0x04fbedfdf8001014 0xffffffff100e0f8f 0xfffffffff880707c

def z62 : W := mkw 0x17862b4cde89ac2b 0x40bc315a66f44d61 0xffce3fd8ff81fe7c 0xf7fe71fec7fc0ff3

def z63 : W := mkw 0x1d7990a200000000 0x00ebcc8510000000 0xbfffd3e700000007 0xf5fffe9f38000000

def z64 : W := mkw 0x7dfbd0e3fdfec79c 0x23efde871feff63c 0xffffd3e7fffecf9f 0xfffffe9f3ffff67c

def z65 : W := mkw 0x087094b221505150 0x804384a5910a828a 0xd9f1ffffe1f1f1ff 0xfecf8fffff0f8f8f

def z66 : W := mkw 0x0006000d048a02a8 0x4000300068245015 0x204e003f018e01e3 0x09027001f80c700f

def z67 : W := mkw 0x15800940d800a401 0x00ac004a06c00520 0xd9801fc0f000fe0c 0xd6cc00fe078007f0

def z68 : W := mkw 0x887d94be00000000 0x0443eca5f0000000 0x207fc03f00000003 0x0103fe01f8000000

def z69 : W := mkw 0x9d799db200000000 0x04ebcced90000000 0x99b1ddc000000000 0x44cd8eee00000000

def z70 : W := mkw 0x00800040da01ac03 0x0004000206d00d60 0x000000001e000e00 0x0000000000f00070

def z71 : W := mkw 0x0000000021401050 0x80000000010a0082 0x0000000061813070 0x00000000030c0983

def z72 : W := mkw 0x0000000021505150 0x80000000010a828a 0x40000000e1f1f1f8 0x0a000000070f8f8f

def z73 : W := mkw 0x0000000100020280 0x0000000008001014 0x00000207100e0e02 0x8000001038807070

def z74 : W := mkw 0x0080400090240000 0x0004020004812000 0x0181c000100e0002 0x800c0e0000807000

def z75 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbe4e3fff00000004 0x25f271fff8000000

def z76 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x7fffe038ffff01ff 0xfbffff01c7fff80f

def z77 : W := mkw 0x1de00000f9400010 0x00ef000007ca0000 0x1ff00000fff00019 0xf8ff800007ff8000

def z78 : W := mkw 0x1500090000000000 0x00a8004800000000 0x99801dc000000000 0x44cc00ee00000000

def z79 : W := mkw 0x4092d0e396bfcfaa 0x620496871cb5fe7d 0xc1b1d3e79fffcfff 0xde0d8e9f3cfffe7f

def z80 : W := mkw 0x0010102000104100 0x0000808100008208 0xc03010208070c18d 0x5e0180810403860c

def z81 : W := mkw 0x1ff63f7dffdbfffb 0xc0ffb1fbeffedfff 0xfffe3fffffffffff 0xfffff1ffffffffff

def z82 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98301c00e070f000 0x44c180e007038780

def z83 : W := mkw 0x17802b40d800a401 0x00bc015a06c00520 0x9f803fc0e000f004 0xf4fc01fe07000780

def z84 : W := mkw 0x4080c0c390268680 0x220406061c813434 0x0181c3c7100e0e02 0x800c0e1e38807070

def z85 : W := mkw 0x17002b400201ac03 0x00b8015a00100d60 0xdf803fc00001fe04 0xf6fc01fe00000ff0

def z86 : W := mkw 0x001090a200000000 0x0000848510000000 0x81b1d3e700000007 0xd40d8e9f38000000

def z87 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffffe070f007 0xf5ffffffff038780

def z88 : W := mkw 0x887d94be00000000 0x0443eca5f0000000 0xb87ffc3f00000007 0x75c3ffe1f8000000

def z89 : W := mkw 0x00020001068b0aaa 0x4000100008345855 0x400000001f8f0ff8 0x0a00000000fc787f

def z90 : W := mkw 0x9f7fbfbf068b0aaa 0x44fbfdfdf8345855 0xffffffff1f8f0fff 0xfffffffff8fc787f

def z91 : W := mkw 0x0000000100020280 0x0000000008001014 0x40000227100e0f8f 0x9a0000113880707c

def z92 : W := mkw 0x0206220c0689082a 0x4010311060344841 0x264e20180f810070 0x21327100c07c0803

def z93 : W := mkw 0x9f7dbfbe21401050 0x84fbedfdf10a0082 0xbfffffff61813077 0xf5fffffffb0c0983

def z94 : W := mkw 0x0860041021401050 0x80430020810a0082 0x18702c18e1f13079 0x78c38160c70f8983

def z95 : W := mkw 0x17822b40de89ac0b 0x00bc115a06f44d60 0xffce3fc0ff8ffe1f 0xfffe71fe07fc7ff0

def z96 : W := mkw 0x0002000004880008 0x0000100000244000 0x264e00001f8e001b 0xb932700000fc7000

def z97 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8301c00e1f1f1f8 0x4ec180e0070f8f8f

def z98 : W := mkw 0x0860041021401050 0x80430020810a0082 0x18000c0060003000 0x00c0006003000180

def z99 : W := mkw 0x3ffb7f70fffdfd5f 0x81ffdbfb87ffefea 0xfffffff8ffffffff 0xffffffffc7ffffff

def z100 : W := mkw 0x0870143000000000 0x004380a180000000 0x0070003800000001 0x00038001c0000000

def z101 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffff01f001e7 0xfdfffffff80f800f

def z102 : W := mkw 0x409050619036c780 0x220482830c81b63c 0xc0301020907ecf8d 0x5e0180810483f67c

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x98001c00e000f000 0x44c000e007000780

def z104 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e78070cf84 0x460d8e9f3c03867c

def z105 : W := mkw 0x7dfbd4f3fdfed7dc 0xa3efdea79feff6be 0xffffffffffffffff 0xffffffffffffffff

def z106 : W := mkw 0x0010143000105140 0x800080a18000828a 0xc0003c380001f1e4 0x060001e1c0000f8f

def z107 : W := mkw 0x9ffdbffeda01ac03 0x04ffedfff6d00d60 0xfffffffffe01fe1f 0xf7fffffffff00ff0

def z108 : W := mkw 0xdffdfffe9034c500 0x26ffeffff481a628 0xbfffffff8070c007 0xf5fffffffc038600

def z109 : W := mkw 0x20824000dcac000c 0x0104120006e56000 0x000000001e0e0000 0x0000000000f07000

def z110 : W := mkw 0x4092d0e394bec788 0x220496871ca5f63c 0xe7ffd3e79ffecf9f 0xff3ffe9f3cfff67c

def z111 : W := mkw 0x9f7dbfbf02030aa2 0x44fbedfdf8101855 0xffffffff00010fe7 0xf7fffffff800087f

def z112 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x660e22071e0f0e1e 0xb330711038f07870

def z113 : W := mkw 0x48f0d0e3b176c790 0x224786871d8bb63c 0xd9f1d3e7f1fecf9f 0xfecf8e9f3f8ff67c

def z114 : W := mkw 0x4090d0e3b176d7d0 0xa20486871d8bb6be 0xc1b1d3e7f1ffffff 0xde0d8e9f3f8fffff

def z115 : W := mkw 0x0080004090008400 0x0004000204800420 0xc18013c09000ce0c 0xd60c009e04800670

def z116 : W := mkw 0x887d94be00000000 0x0443eca5f0000000 0xa1ffd3ff00000007 0xd50ffe9ff8000000

def z117 : W := mkw 0x3deb4001fdee029c 0x01ef5a000fef7014 0x7fffc227fffe0f9f 0xfbfffe113ffff07c

def z118 : W := mkw 0xbfef6f1cfdec001c 0x05ff7b78e7ef6000 0x3fffec18fffe001b 0xf9ffff60c7fff000

def z119 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e221f1f8f0e72 0xa1327110f8fc7873

def z120 : W := mkw 0x8214bfbe00000000 0x0410a5fdf0000000 0x80003fff00000004 0x040001fff8000000

def z121 : W := mkw 0x1df01d70f950f551 0x80ef80eb87ca87aa 0x99b01dc0e070f000 0x44cd80ee07038780

def z122 : W := mkw 0x3feb6b40ffedac1f 0x01ff5b5a07ff6d60 0x3fffc3c0fffe0e1b 0xf9fffe1e07fff070

def z123 : W := mkw 0x0206220d27db5bfa 0xc0103110693edadf 0x664e223fffffffff 0xbb327111ffffffff

def z124 : W := mkw 0x5796fbefdebfefab 0x62bcb7df7ef5ff7d 0xffffffffffffffff 0xffffffffffffffff

def z125 : W := mkw 0x9ff9bff2da01ac03 0x04ffcdff96d00d60 0xdfb1ffc0fe01fe1c 0xf6fd8ffe07f00ff0

def z126 : W := mkw 0x0200220002010802 0x0010011000100840 0x464022381f810ffd 0xba320111c0fc087f

def z127 : W := mkw 0xddf9ddf29034c500 0x26efceef9481a628 0x99b1ddc08070c000 0x44cd8eee04038600

def z128 : W := mkw 0x9d7d9dbe00000000 0x04ebecedf0000000 0xb9ffddff00000003 0x45cffeeff8000000

def z129 : W := mkw 0x0002000004880008 0x0000100000244000 0x204e0000018e0003 0x09027000000c7000

def z130 : W := mkw 0x3deb4940fdeca41d 0x01ef5a4a07ef6520 0xbfffddc0fffef01b 0xfdfffeee07fff780

def z131 : W := mkw 0x9ffdbffefb51fd53 0x84ffedfff7da8fea 0xfffffffffff1ffff 0xffffffffffff8fff

def z132 : W := mkw 0x971dbfbe00000000 0x04b8edfdf0000000 0xa78fffff00000006 0x853c7ffff8000000

def z133 : W := mkw 0x15800000d8000000 0x00ac000006c00000 0x1f800000fe000018 0xf0fc000007f00000

def z134 : W := mkw 0x1f703f306b517953 0x80fb81f9835a8bca 0xde703c38eff1f1fd 0x7ef381e1c77f8f8f

def z135 : W := mkw 0x408040419036c780 0x220402020c81b63c 0x40000000907ecf88 0x0a0000000483f67c

def z136 : W := mkw 0x9f6d2f1c00000000 0x04fb6978e0000000 0x3e4e2c1800000000 0x21f27160c0000000

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x40402038018101fd 0x3a020101c00c080f

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000001e000018 0xb030000000f00000

def z139 : W := mkw 0x15820000dc880008 0x00ac100006e44000 0x3fce0000ff8e001b 0xf9fe700007fc7000

def z140 : W := mkw 0x4010d0a200344100 0x220086851001a208 0x0031c00000700000 0x00018e0000038000

def z141 : W := mkw 0x00800040d800a401 0x0004000206c00520 0x00000000e000f000 0x0000000007000780

def z142 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x27ffc0001ffe0003 0x893ffe0000fff000

def z143 : W := mkw 0x3feb6b40ffedac1f 0x01ff5b5a07ff6d60 0xffffffc0fffffe1f 0xfffffffe07fffff0

def z144 : W := mkw 0x0200220000000000 0x0010011000000000 0x0600220000000004 0xb030011000000000

def z145 : W := mkw 0x3deb4410fdec105c 0x81ef5a2087ef6082 0x3fffec18ffff307b 0xf9ffff60c7fff983

def z146 : W := mkw 0x5780ebc3da27ae83 0x22bc075e1ed13d74 0x0781c3c71e0e0e02 0x803c0e1e38f07070

def z147 : W := mkw 0x3d6b00006dc8001c 0x01eb5800036e4000 0x3e4e00006f800010 0x21f27000037c0000

def z148 : W := mkw 0x3de94000f9640014 0x01ef4a0007cb2000 0x19f1c000e1f00019 0x78cf8e00070f8000

def z149 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98701c38e1f0f1e1 0x4cc380e1c70f878f

def z150 : W := mkw 0xbfffffbfffef0abe 0x45fffffdffff7855 0xffffffffffff0fff 0xfffffffffffff87f

def z151 : W := mkw 0x0a74363c21505150 0x8053a1b1e10a828a 0xfe7e3e3fe1f1f1ff 0xfff3f1f1ff0f8f8f

def z152 : W := mkw 0x0010102000104100 0x0000808100008208 0xd8303c20e071f19d 0x7ec181e107038f8c

def z153 : W := mkw 0x1d69000000000000 0x00eb480000000000 0x3e4e000000000000 0x21f2700000000000

def z154 : W := mkw 0x9ffdbffed800a401 0x04ffedfff6c00520 0xbfffffffe000f007 0xf5ffffffff000780

def z155 : W := mkw 0x0870143000000000 0x004380a180000000 0x98703c3800000005 0x74c381e1c0000000

def z156 : W := mkw 0x4090d0e29034c500 0x220486871481a628 0x81b1d1c08070c000 0x440d8e8e04038600

def z157 : W := mkw 0x17002b0002010802 0x00b8015800100840 0xdf803fc01e010e1c 0xf6fc01fe00f00870

def z158 : W := mkw 0x17802b00d8000000 0x00bc015806c00000 0x9f803fc0fe00001c 0xf4fc01fe07f00000

def z159 : W := mkw 0x0204220d02030aa2 0x4010211068101855 0x664e223f00010fe7 0xb3327111f800087f

def z160 : W := mkw 0x0204220c00000000 0x0010211060000000 0x264e223f00000007 0xb1327111f8000000

def z161 : W := mkw 0x3deb4000fdfc515c 0x81ef5a0007efe28a 0x7fffc000fffff1fb 0xfbfffe0007ffff8f

def z162 : W := mkw 0x9df99df2d800a401 0x04efccef96c00520 0x99b1ddc0e000f000 0x44cd8eee07000780

def z163 : W := mkw 0x0860041021505150 0x80430020810a828a 0x58402c18e1f1f1f8 0x2ac20160c70f8f8f

def z164 : W := mkw 0x0a76363d27db5bfa 0xc053b1b1e93edadf 0xfe7e3e3fffffffff 0xfff3f1f1ffffffff

def z165 : W := mkw 0x1f6d220c00000000 0x00fb691060000000 0x3fffe23f00000007 0xf1ffff11f8000000

def z166 : W := mkw 0x20824000fdec001c 0x0104120007ef6000 0x264e0000fffe001b 0xb932700007fff000

def z167 : W := mkw 0xdffdffffb176d7d0 0xa6ffeffffd8bb6be 0xfffffffff1ffffff 0xffffffffff8fffff

def z168 : W := mkw 0x20824000fdec001c 0x0104120007ef6000 0x00000000fffe0018 0x0800000007fff000

def z169 : W := mkw 0x0204220d00020280 0x0010211068001014 0x664e223f100e0f8f 0xbb327111f880707c

def z170 : W := mkw 0x001090a200104100 0x0000848510008208 0xc1b1d3e78070c18f 0xde0d8e9f3c03860c

def z171 : W := mkw 0x0010143000105140 0x800080a18000828a 0xd8003c38e001f1fc 0x76c001e1c7000f8f

def z172 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x278fc0001e0e0002 0x813c7e0000f07000

def z173 : W := mkw 0x9f6d2f1c4a012803 0x04fb6978e2500940 0x3e4e2c186e013010 0x21f27160c3700980

def z174 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x9f801fc0fe00fe00 0xc4fc00fe07f007f0

def z175 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfbfdfc700000002 0xc5fdfefe38000000

def z176 : W := mkw 0x17002b404a01ac03 0x00b8015a02500d60 0xde003fc06e01fe14 0x26f001fe03700ff0

def z177 : W := mkw 0x1de9400090240000 0x00ef4a0004812000 0x3fffc000907e000b 0xf9fffe000483f000

def z178 : W := mkw 0x3de94000f9640014 0x01ef4a0007cb2000 0x19b1c000e0700000 0x40cd8e0007038000

def z179 : W := mkw 0x17002b0000000000 0x00b8015800000000 0xdf803fc0e001f01c 0xf6fc01fe07000f80

def z180 : W := mkw 0x5790fbe39036c780 0x22bc87df1c81b63c 0xdfb1ffe7907ecf8f 0xfefd8fff3c83f67c

def z181 : W := mkw 0x887d94be21505150 0x8443eca5f10a828a 0xf87ffc3fe1f1f1ff 0x7fc3ffe1ff0f8f8f

def z182 : W := mkw 0x3d7b14306dd8515c 0x81ebd8a1836ec28a 0xfe7e3c38eff1f1fd 0x7ff3f1e1c77f8f8f

def z183 : W := mkw 0x4294f2ef9237cfa2 0x6214a7977c91be7d 0xc1b1f3ff907fcfef 0xde0d8f9ffc83fe7f

def z184 : W := mkw 0x3fe96b40fb65ac17 0x01ff4b5a07db2d60 0xdfb1ffc0fe71fe1c 0xf6fd8ffe07f38ff0

def z185 : W := mkw 0x0214b2ae00000000 0x0010a59570000000 0xa7fff3ff00000007 0xf53fff9ff8000000

def z186 : W := mkw 0x1d6b000004880008 0x00eb580000244000 0x3fffc0001f8e001b 0xf9fffe0000fc7000

def z187 : W := mkw 0x0010102000104100 0x0000808100008208 0x0030002000700181 0x080180010003800c

def z188 : W := mkw 0x28e24000fdec001c 0x0147120007ef6000 0x18700000fffe0019 0x78c3800007fff000

def z189 : W := mkw 0x0870143000000000 0x004380a180000000 0xd8703c38e001f01d 0x76c381e1c7000f80

def z190 : W := mkw 0xfffffffffdfec79c 0x27ffffffffeff63c 0xfffffffffffecf9f 0xfffffffffffff67c

def z191 : W := mkw 0x15800940da01ac03 0x00ac004a06d00d60 0xd9801dc0fe01fe18 0x46cc00ee07f00ff0

def z192 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffffe001f01f 0xf7ffffffff000f80

def z193 : W := mkw 0x0204220c00000000 0x0010211060000000 0x664e223f018101ff 0xbb327111f80c080f

def z194 : W := mkw 0x17802b4090008400 0x00bc015a04800420 0xdf803fc09000ce0c 0xf6fc01fe04800670

def z195 : W := mkw 0x3dfb5430fdfc515c 0x81efdaa187efe28a 0xbfffdc00fffef01b 0xfdfffee007fff780

def z196 : W := mkw 0x4296f2ef96bfcfaa 0x6214b7977cb5fe7d 0xe7fff3ff9fffcfff 0xff3fff9ffcfffe7f

def z197 : W := mkw 0x0082400094ac0008 0x0004120004a56000 0x27ffc0009ffe001b 0xf93ffe0004fff000

def z198 : W := mkw 0x4290fbe39237ef83 0x221487df1c91bf7c 0xc1b1ffe7907fff8f 0xde0d8fff3c83fffc

def z199 : W := mkw 0x8214bfbe00105140 0x8410a5fdf000828a 0xc0003fff0001f1e4 0x060001fff8000f8f

def z200 : W := mkw 0x970fab8f068b0aaa 0x44b87d5c78345855 0x67cfe3ff1f8f0fff 0xbb3e7f1ff8fc787f

def z201 : W := mkw 0x9f6dab8e00000000 0x04fb6d5c70000000 0x3fffc3c700000003 0xf1fffe1e38000000

def z202 : W := mkw 0x8a74bfbe00000000 0x0453a5fdf0000000 0x98703fff00000005 0x74c381fff8000000

def z203 : W := mkw 0x0006000c04880028 0x4000300060244001 0x204e001801800060 0x01027000c00c0003

def z204 : W := mkw 0x80109db200000000 0x040084ed90000000 0x80001dc000000000 0x040000ee00000000

def z205 : W := mkw 0x0860000021400010 0x00430000010a0000 0x18700000e1f00019 0x78c38000070f8000

def z206 : W := mkw 0x17903f70da11fd43 0x80bc81fb86d08fea 0xdf803ff8fe01fffc 0xf6fc01ffc7f00fff

def z207 : W := mkw 0x0000808200000000 0x0000040410000000 0x0181c3c700000002 0x800c0e1e38000000

def z208 : W := mkw 0x5590d0e3d836c780 0x22ac86871ec1b63c 0xdfb1d3e7fe7ecf9f 0xfefd8e9f3ff3f67c

def z209 : W := mkw 0x0216363d069b5bea 0xc010b1b1e834dadf 0xe64e3e3f1f8fffff 0xbf3271f1f8fc7fff

def z210 : W := mkw 0x0a703f702351fd53 0x805381fb811a8fea 0xd8703ff8e1f1fffd 0x7ec381ffc70f8fff

def z211 : W := mkw 0x409090e39012c780 0x220484871c80963c 0xc18013e79000cf8c 0xd60c009f3c80067c

def z212 : W := mkw 0x0010143021505150 0x800080a1810a828a 0xc0003c38e1f1f1fc 0x0e0001e1c70f8f8f

def z213 : W := mkw 0x4af6f6ffb7ffdffa 0xe257b7b7fdbffeff 0xffffffffffffffff 0xffffffffffffffff

def z214 : W := mkw 0x4294f2ef9036c780 0x2214a7977c81b63c 0xe7fff3ff907ecf8f 0xff3fff9ffc83f67c

def z215 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d1c0907ecf88 0x4e0d8e8e0483f67c

def z216 : W := mkw 0x887994b200000000 0x0443cca590000000 0x0031c00000000000 0x00018e0000000000

def z217 : W := mkw 0xbdfbddb2fdec001c 0x05efdeed97ef6000 0xbfffddc0fffe001b 0xfdfffeee07fff000

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z219 : W := mkw 0x60824041fdfec79c 0x230412020feff63c 0x40000000fffecf98 0x0a00000007fff67c

def z220 : W := mkw 0x0000000021505150 0x80000000010a828a 0x00000000e070f000 0x0000000007038780

def z221 : W := mkw 0x3def400dfdee02bc 0x41ef7a006fef7015 0x3fffc03ffffe01fb 0xf9fffe01fffff00f

def z222 : W := mkw 0x8a7dbfbe00000000 0x0453edfdf0000000 0xa07fffff00000007 0x0503fffff8000000

def z223 : W := mkw 0x5df9d0e39036c780 0x22efce871c81b63c 0xffffd3e7907ecf8f 0xfffffe9f3c83f67c

def z224 : W := mkw 0x286b400025ec001c 0x01435a00012f6000 0x267fc0001ffe001b 0xb933fe0000fff000

def z225 : W := mkw 0x4090d0e3da37ef83 0x220486871ed1bf7c 0xc1b1d3e7fe7fff9f 0xde0d8e9f3ff3fffc

def z226 : W := mkw 0x37826b40ffedac1f 0x01bc135a07ff6d60 0xdf803fc0fffffe1c 0xfefc01fe07fffff0

def z227 : W := mkw 0x4080c0c390268680 0x220406061c813434 0x01b1c3c7907e0e0b 0xd80d8e1e3c83f070

def z228 : W := mkw 0x0204220d02030aa2 0x4010211068101855 0x0000020700000e00 0x0000001038000070

def z229 : W := mkw 0x4016d0af04be43a8 0x6200b6857825f21d 0x207fc03f01fe01e3 0x0903fe01f80ff00f

def z230 : W := mkw 0x408040419036c780 0x220402020c81b63c 0x40000227907ecf8f 0x9a0000113c83f67c

def z231 : W := mkw 0x4090d4f39036d7c0 0xa20486a79c81b6be 0xc1b1ffff907fffef 0xde0d8ffffc83ffff

def z232 : W := mkw 0x0010102000000000 0x0000808100000000 0x8030102000000005 0x5401808100000000

def z233 : W := mkw 0x1500000000000000 0x00a8000000000000 0x1f80000000000000 0xf0fc000000000000

def z234 : W := mkw 0x0286224dde8baeab 0x401431126ef45d75 0x664e223fff8fffff 0xbb327111fffc7fff

def z235 : W := mkw 0x1fe02b40fb41ac13 0x00ff015a07da0d60 0xdff03fc0fff1fe1d 0xfeff81fe07ff8ff0

def z236 : W := mkw 0x087094b200000000 0x004384a590000000 0x99f1ffff00000007 0xf4cf8ffff8000000

def z237 : W := mkw 0x15800940d800a401 0x00ac004a06c00520 0xd9803dc0e001f01c 0x76cc01ee07000f80

def z238 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xc0703c3801f1f1e5 0x0e0381e1c00f8f8f

def z239 : W := mkw 0x17002b004a012803 0x00b8015802500940 0x1e002c006e013010 0x20f0016003700980

def z240 : W := mkw 0x00020001048a02a8 0x4000100008245015 0x00000000018e01e0 0x08000000000c700f

def z241 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e02071f8e0e1b 0xb932701038fc7070

def z242 : W := mkw 0x0869000000000000 0x0043480000000000 0x207fc00000000003 0x0103fe0000000000

def z243 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e223f0f810ff4 0x23327111f87c087f

def z244 : W := mkw 0x3fef620cfdec001c 0x01ff7b1067ef6000 0x3fffe23ffffe001f 0xf9ffff11fffff000

def z245 : W := mkw 0x1ff03f70da01ac03 0x00ff81fb86d00d60 0xdff03ff8fe01fe1d 0xf6ff81ffc7f00ff0

def z246 : W := mkw 0x1d69000021400010 0x00eb4800010a0000 0x3fffc000e1f0001b 0xf9fffe00070f8000

def z247 : W := mkw 0x4090d0a390364380 0x220486851c81b21c 0x01b1c027907e018b 0xd80d8e013c83f00c

def z248 : W := mkw 0x9ffdbffe90008400 0x04ffedfff4800420 0xffffffff9000ce0f 0xf7fffffffc800670

def z249 : W := mkw 0x3deb4040fdec841c 0x01ef5a0207ef6420 0xffffd3c0fffece1f 0xfffffe9e07fff670

def z250 : W := mkw 0x1de90000d8000000 0x00ef480006c00000 0x3fffc000fe00001b 0xf1fffe0007f00000

def z251 : W := mkw 0x687bd0a325fe439c 0x2343de85192ff21c 0x207fc02701fe0183 0x0903fe01380ff00c

def z252 : W := mkw 0xc214bfff0012c780 0x2610a5fff800963c 0xc0003fff0000cf84 0x060001fff800067c

def z253 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8403c38e181f1fd 0x7ec201e1c70c0f8f

def z254 : W := mkw 0x82042f1c00000000 0x04102178e0000000 0x00002c1800000000 0x00000160c0000000

def z255 : W := mkw 0x8214bfbe00000000 0x0410a5fdf0000000 0x81b1ffff00000007 0xd40d8ffff8000000

def z256 : W := mkw 0x0002000004880008 0x0000100000244000 0x260e00001e0e0002 0x8130700000f07000

def z257 : W := mkw 0x20824040ffedac1f 0x0104120207ff6d60 0x40000000fffffe18 0x0a00000007fffff0

def z258 : W := mkw 0x287b543025fc515c 0x8143daa1812fe28a 0xf87ffc38e1fff1ff 0x7fc3ffe1c70fff8f

def z259 : W := mkw 0x9d690d1000000000 0x04eb486880000000 0x18000c0000000000 0x00c0006000000000

def z260 : W := mkw 0x9d799db200000000 0x04ebcced90000000 0x99b1dfe700000007 0xd4cd8eff38000000

def z261 : W := mkw 0x408040419036c780 0x220402020c81b63c 0xc18013c0907ecf8c 0xde0c009e0483f67c

def z262 : W := mkw 0x15800040d8008400 0x00ac000206c00420 0xdf8013c0fe00ce1c 0xf6fc009e07f00670

def z263 : W := mkw 0x400000410012c780 0x220000020800963c 0x400000000000cf80 0x020000000000067c

def z264 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1f1f3ff91ffcfff 0xfe0f8f9ffc8ffe7f

def z265 : W := mkw 0x9509898200000000 0x04a84c4c10000000 0x0181c1c000000000 0x000c0e0e00000000

def z266 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xbf8fffc700000006 0xf5fc7ffe38000000

def z267 : W := mkw 0xbffffffeffedac1f 0x05fffffff7ff6d60 0xfffffffffffffe1f 0xfffffffffffffff0

def z268 : W := mkw 0x00800040da01ac03 0x0004000206d00d60 0xc18013c0fe01fe1c 0xd60c009e07f00ff0

def z269 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000e0000018 0x70c0000007000000

def z270 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x0030000000700000 0x0001800000038000

def z271 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x27cfe3ff00000007 0xb13e7f1ff8000000

def z272 : W := mkw 0x3fef6b4dffefaebf 0x41ff7b5a6fff7d75 0xffffffffffffffff 0xffffffffffffffff

def z273 : W := mkw 0x0080004090008400 0x0004000204800420 0x818011c08000c000 0x440c008e04000600

def z274 : W := mkw 0x0206220c0689082a 0x4010311060344841 0x264e223f0f810077 0xb1327111f87c0803

def z275 : W := mkw 0x15800940d800a401 0x00ac004a06c00520 0x9f801dc0fe00f018 0xf4fc00ee07f00780

def z276 : W := mkw 0x3dfb5020fdfc411c 0x01efda8107efe208 0xffffd020fffec19f 0xfffffe8107fff60c

def z277 : W := mkw 0x378b6b40deadac0f 0x01bc5b5a06f56d60 0x278fc3c01e0e0e02 0x813c7e1e00f07070

def z278 : W := mkw 0xdffdffffda37ef83 0x26ffeffffed1bf7c 0xfffffffffe7fff9f 0xfffffffffff3fffc

def z279 : W := mkw 0x8a74bfbe21505150 0x8453a5fdf10a828a 0xd8703fffe1f1f1fd 0x7ec381ffff0f8f8f

def z280 : W := mkw 0x0872143025d85158 0x804390a1812ec28a 0xfe7e3c38fffff1ff 0xfff3f1e1c7ffff8f

def z281 : W := mkw 0x9f6daf9e00000000 0x04fb6d7cf0000000 0x3fcfefdf00000002 0xa1fe7f7ef8000000

def z282 : W := mkw 0x0860041000000000 0x0043002080000000 0x18402c1800000000 0x20c20160c0000000

def z283 : W := mkw 0x4000400100364380 0x220002000801b21c 0x00000000007e0180 0x080000000003f00c

def z284 : W := mkw 0x9d799db200000000 0x04ebcced90000000 0xbfffddc000000003 0xf5fffeee00000000

def z285 : W := mkw 0x886d041c00000000 0x04436820e0000000 0x204e001800000000 0x01027000c0000000

def z286 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x01b1c3e7107e0f83 0x880d8e1f3883f07c

def z287 : W := mkw 0x7debc0c3fdee869c 0x23ef5e061fef7434 0x3fffc3c7fffe0e1b 0xf9fffe1e3ffff070

def z288 : W := mkw 0x08701431215253d0 0x804380a1890a929e 0xd8703e3ff1ffffff 0xfec381f1ff8fffff

def z289 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xc7803fc01e01fe04 0x863c01fe00f00ff0

def z290 : W := mkw 0x0a74363c00000000 0x0053a1b1e0000000 0xbe7e3e3f00000007 0xf5f3f1f1f8000000

def z291 : W := mkw 0x9ffdbfbed8000000 0x04ffedfdf6c00000 0xbffffffffe00001f 0xf5fffffffff00000

def z292 : W := mkw 0x001090a200000000 0x0000848510000000 0x0031c02700000003 0x00018e0138000000

def z293 : W := mkw 0x0200220002010802 0x0010011000100840 0x060020000e010010 0x2030010000700800

def z294 : W := mkw 0x0080400090240000 0x0004020004812000 0x01b1c00080700000 0x400d8e0004038000

def z295 : W := mkw 0x0000000021400010 0x00000000010a0000 0x00000000e1f00018 0x08000000070f8000

def z296 : W := mkw 0x9d799db221505150 0x84ebcced910a828a 0x99b1ddc0e070f000 0x44cd8eee07038780

def z297 : W := mkw 0x1500000048000000 0x00a8000002400000 0x1e0000006e000010 0x20f0000003700000

def z298 : W := mkw 0x0006000d048a02a8 0x4000300068245015 0x604e023f118e0fef 0x9b027011f88c707f

def z299 : W := mkw 0x1f703f3000000000 0x00fb81f980000000 0x9ff03ff800000005 0xf4ff81ffc0000000

def z300 : W := mkw 0xbfefeb8efdec001c 0x05ff7f5c77ef6000 0x3fffc3c7fffe001b 0xf9fffe1e3ffff000

def z301 : W := mkw 0x4080c0c390268680 0x220406061c813434 0x4181c3e7100e0f8f 0x9a0c0e1f3880707c

def z302 : W := mkw 0x48f05471b176d7d0 0xa24782a38d8bb6be 0xd8703c38f1fffffd 0x7ec381e1c78fffff

def z303 : W := mkw 0x3feb6200ffed081e 0x01ff5b1007ff6840 0x7fffe200ffff0e1f 0xfbffff1007fff870

def z304 : W := mkw 0x7ffff2efffffcfbe 0x63ffff977ffffe7d 0xfffff3ffffffcfff 0xffffff9ffffffe7f

def z305 : W := mkw 0x02002b400201ac03 0x0010015a00100d60 0xc6003fc01e01fe1c 0xb63001fe00f00ff0

def z306 : W := mkw 0x17842b4cda01ac03 0x00bc215a66d00d60 0xffce3ffffe01fe1f 0xf7fe71fffff00ff0

def z307 : W := mkw 0x4080c0c39036c780 0x220406061c81b63c 0x4181c3c7907ecf8a 0x8a0c0e1e3c83f67c

def z308 : W := mkw 0x286f400d25ee02bc 0x41437a00692f7015 0x207fc03f01fe01e3 0x0903fe01f80ff00f

def z309 : W := mkw 0x4214b2ef0213cfa2 0x6210a59778109e7d 0xc00033ff0001cfe4 0x0600019ff8000e7f

def z310 : W := mkw 0x5780ebc3da27ae83 0x22bc075e1ed13d74 0xdf81ffc7fe0ffe1e 0xf6fc0ffe3ff07ff0

def z311 : W := mkw 0x401090e30012c780 0x220084871800963c 0xc1b1d3e70000cf87 0xd60d8e9f3800067c

def z312 : W := mkw 0x4870d4b3217653d0 0xa24386a5990bb29e 0x0071c03f01fe01e3 0x08038e01f80ff00f

def z313 : W := mkw 0x7ffbfbe3ffffef9f 0x23ffdfdf1fffff7c 0xffffffe7ffffff9f 0xffffffff3ffffffc

def z314 : W := mkw 0x9f6d2f1c00000000 0x04fb6978e0000000 0x3fffec1800000003 0xf1ffff60c0000000

def z315 : W := mkw 0x02802240da01ac03 0x0014011206d00d60 0x46002200fe01fe1c 0xb230011007f00ff0

def z316 : W := mkw 0x0010102000104100 0x0000808100008208 0xc00010200000c184 0x060000810000060c

def z317 : W := mkw 0x4216b2ef069bcfaa 0x6210b5977834de7d 0xe64e33ff1f8fcfff 0xbf32719ff8fc7e7f

def z318 : W := mkw 0x0000000100020280 0x0000000008001014 0x40000000100e0f88 0x0a0000000080707c

def z319 : W := mkw 0x5590d9e3d836e781 0x22ac86cf1ec1b73c 0xd9b1dfe7f07eff8f 0xdecd8eff3f83f7fc

def z320 : W := mkw 0x1500090048002001 0x00a8004802400100 0x18000c0060003000 0x00c0006003000180

def z321 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8301c20e070f18d 0x5ec180e10703878c

def z322 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x1f8003c0fe000e18 0xf0fc001e07f00070

def z323 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x99b1ffff00000004 0x44cd8ffff8000000

def z324 : W := mkw 0x9ffdbffeda01ac03 0x04ffedfff6d00d60 0xbfffffff1e000e07 0xf5fffffff8f00070

def z325 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98703c3801f001e5 0x7cc381e1c00f800f

def z326 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8303c00e071f01c 0x76c181e007038f80

def z327 : W := mkw 0x0000000021505150 0x80000000010a828a 0x40402038e1f1f1fd 0x3a020101c70f8f8f

def z328 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xd9b1ffe7f07fff9f 0xfecd8fff3f83fffc

def z329 : W := mkw 0x000000400201ac03 0x0000000200100d60 0x400000000001fe00 0x0200000000000ff0

def z330 : W := mkw 0x9f7fbfbf048a02a8 0x44fbfdfdf8245015 0xbfffffff018e01e7 0xfdfffffff80c700f

def z331 : W := mkw 0x0860000000000000 0x0043000000000000 0x1870000000000001 0x70c3800000000000

def z332 : W := mkw 0x3de94000f9640014 0x01ef4a0007cb2000 0x1fb1c000fe700018 0xf0fd8e0007f38000

def z333 : W := mkw 0x378f620ddeaf0aae 0x41bc7b106ef57855 0x278fc2071e0e0e02 0x813c7e1038f07070

def z334 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98703c18e1f1f070 0x64c381e0c70f8f83

def z335 : W := mkw 0x358b4000fdec001c 0x01ac5a0007ef6000 0x278fc000fffe001a 0x893c7e0007fff000

def z336 : W := mkw 0x1786220dde8b0aaa 0x40bc31106ef45855 0x7fce223fff8f0fff 0xfbfe7111fffc787f

def z337 : W := mkw 0x4010d0a300364380 0x220086851801b21c 0x81b1d3e7007e0187 0xdc0d8e9f3803f00c

def z338 : W := mkw 0x0204220d02030aa2 0x4010211068101855 0x4040223f01810ffd 0x3a020111f80c087f

def z339 : W := mkw 0x15800040da01ac03 0x00ac000206d00d60 0x5f800000fe01fe18 0xf2fc000007f00ff0

def z340 : W := mkw 0x887d94be21505150 0x8443eca5f10a828a 0x207fc03f01f001e3 0x0903fe01f80f800f

def z341 : W := mkw 0xdf7dbfff0012c780 0x26fbedfff800963c 0xffffffff0000cf87 0xf7fffffff800067c

def z342 : W := mkw 0x17822b41de8baeab 0x40bc115a0ef45d75 0xdf803fc0ff8ffffc 0xfefc01fe07fc7fff

def z343 : W := mkw 0x02062b4d068baeab 0x4010315a68345d75 0xe64e3fff1f8fffff 0xbf3271fff8fc7fff

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x40002038000101e4 0x02000101c000080f

def z345 : W := mkw 0x0080004190028680 0x000400020c801434 0xc18013e7900ecf8f 0xde0c009f3c80767c

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000100e000b 0x9800000000807000

def z347 : W := mkw 0x3df95430f9745154 0x81efcaa187cba28a 0xd9f1fc38e1f1f1fd 0x7ecf8fe1c70f8f8f

def z348 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbffffdd800000000 0x65ffffeec0000000

def z349 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x19b1c000fffe0018 0x48cd8e0007fff000

def z350 : W := mkw 0x0204220c02010802 0x0010211060100840 0x664e223f1e010e1f 0xb3327111f8f00870

def z351 : W := mkw 0x1df01430f9505150 0x80ef80a187ca828a 0xdff03c38fff1f1fd 0xfeff81e1c7ff8f8f

def z352 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc00013e7907ecf8c 0x0e00009f3c83f67c

def z353 : W := mkw 0x8214bffe0201ac03 0x0410a5fff0100d60 0xc0003fff0001fe04 0x060001fff8000ff0

def z354 : W := mkw 0x3feb2b40ffc9ac1f 0x01ff595a07fe4d60 0xffce3fc0ff81fe1c 0xf7fe71fe07fc0ff0

def z355 : W := mkw 0x9f7dbfbe02010802 0x04fbedfdf0100840 0xffffffff1e010e1f 0xf7fffffff8f00870

def z356 : W := mkw 0xbfffffbefdfc515c 0x85fffffdf7efe28a 0xfffffffffffff1ff 0xffffffffffffff8f

def z357 : W := mkw 0x0002000004880008 0x0000100000244000 0x664e20381f8f01ff 0xbb327101c0fc780f

def z358 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x4031c027907ecf8b 0x0a018e013c83f67c

def z359 : W := mkw 0xc8fdd4ff9036c780 0x2647eea7fc81b63c 0xe1ffd3ff907ecf8f 0xdf0ffe9ffc83f67c

def z360 : W := mkw 0x1fe92b40da01ac03 0x00ff495a06d00d60 0xffffffc0fe01fe1f 0xf7fffffe07f00ff0

def z361 : W := mkw 0x0860000021400010 0x00430000010a0000 0x18300000e0700000 0x40c1800007038000

def z362 : W := mkw 0x200200006dc8001c 0x01001000036e4000 0x000000006f800010 0x00000000037c0000

def z363 : W := mkw 0x0a74363d23535bf2 0xc053a1b1e91a9adf 0xd8703e3fe1f1fffd 0x7ec381f1ff0f8fff

def z364 : W := mkw 0x3d69000069400014 0x01eb4800034a0000 0x1800000060000000 0x00c0000003000000

def z365 : W := mkw 0xddf9ddf39036c780 0x26efceef9c81b63c 0xd9b1dfe7907ecf8f 0xdecd8eff3c83f67c

def z366 : W := mkw 0x02002b0002012803 0x0010015800100940 0x00002c0000013000 0x0000016000000980

def z367 : W := mkw 0x1d69000000000000 0x00eb480000000000 0x19b1c00000000000 0x40cd8e0000000000

def z368 : W := mkw 0x9f7dbfbe00104100 0x04fbedfdf0008208 0xffffffff8070c18f 0xfffffffffc03860c

def z369 : W := mkw 0x970d2b0c00000000 0x04b8695860000000 0x260e000000000000 0x0130700000000000

def z370 : W := mkw 0x0a66261c27c9187a 0xc0533130e13e48c3 0x3e4e2c186f813070 0x21f27160c37c0983

def z371 : W := mkw 0x17002b004a012803 0x00b8015802500940 0x5e002e007e013e1c 0xb2f0017003f009f0

def z372 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff018101ff 0xfffffffff80c080f

def z373 : W := mkw 0x0876143d25da53f8 0xc043b0a1e92ed29f 0x207e003f01fe01e3 0x0903f001f80ff00f

def z374 : W := mkw 0x0080400190260280 0x000402000c813014 0x41b1c227907e0f8f 0xda0d8e113c83f07c

def z375 : W := mkw 0xbffdffbef9640014 0x05ffeffdf7cb2000 0xbfffffffe0700007 0xf5ffffffff038000

def z376 : W := mkw 0x0200220102030a82 0x0010011008101854 0x460022271e0f0f9f 0xba30011138f0787c

def z377 : W := mkw 0xbf7fbfbe6dc8001c 0x05fbfdfdf36e4000 0xbfffffff6f800017 0xf5fffffffb7c0000

def z378 : W := mkw 0x4090d0e29034c500 0x220486871481a628 0x81b1d3e78070c007 0xd40d8e9f3c038600

def z379 : W := mkw 0x0010143000105140 0x800080a18000828a 0x00000038000001e0 0x00000001c000000f

def z380 : W := mkw 0x17806b40da25ac03 0x00bc035a06d12d60 0xdfb1ffc0fe7ffe1f 0xfefd8ffe07f3fff0

def z381 : W := mkw 0x9f7fbfbf27db5bfa 0xc4fbfdfdf93edadf 0xffffffffffffffff 0xffffffffffffffff

def z382 : W := mkw 0x5ff0fff3fb77ffd3 0xa2ff87ff9fdbbffe 0xdff1ffffffffffff 0xfeff8fffffffffff

def z383 : W := mkw 0x3feb6b00ffed281f 0x01ff5b5807ff6940 0x3fffec00ffff301b 0xf9ffff6007fff980

def z384 : W := mkw 0x758bc0c3dcae868c 0x23ac5e061ee57434 0x278fc3c71e0e0e02 0x813c7e1e38f07070

def z385 : W := mkw 0x00020001068b0aaa 0x4000100008345855 0x000000001e0e0e00 0x0000000000f07070

def z386 : W := mkw 0x1f602f106b413853 0x80fb0178835a09c2 0x1e402c186f813070 0x20f20160c37c0983

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x818013c000000004 0xd40c009e00000000

def z388 : W := mkw 0x3de94000f9640014 0x01ef4a0007cb2000 0x19b1c000f07e000b 0xd8cd8e000783f000

def z389 : W := mkw 0x4080c0c290248400 0x2204060614812420 0x0181c1c000000000 0x000c0e0e00000000

def z390 : W := mkw 0x15800000d8000000 0x00ac000006c00000 0x078000001e000000 0x803c000000f00000

def z391 : W := mkw 0x9f6d2f1c00000000 0x04fb6978e0000000 0xbfce3fd800000004 0xf5fe71fec0000000

def z392 : W := mkw 0x4082404196bfcfaa 0x620412020cb5fe7d 0x400000009fffcff8 0x0a00000004fffe7f

def z393 : W := mkw 0x9f7dbfbe21400010 0x04fbedfdf10a0000 0xbfffffffe1f0001f 0xfdffffffff0f8000

def z394 : W := mkw 0x6092d0e3fdfec79c 0x230496871feff63c 0xc1b1d3e7fffecf9f 0xde0d8e9f3ffff67c

def z395 : W := mkw 0x17903b60da11ed03 0x00bc81db06d08f68 0xdfb03fe0fe71ff9d 0xfefd81ff07f38ffc

def z396 : W := mkw 0x0090d0a290240000 0x0004868514812000 0x81b1d3e7907e000f 0xdc0d8e9f3c83f000

def z397 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x3f8fc000fe0e001a 0xf1fc7e0007f07000

def z398 : W := mkw 0x401090a300124380 0x220084851800921c 0x0000002700000180 0x000000013800000c

def z399 : W := mkw 0x0080004090008400 0x0004000204800420 0x400000009000ce08 0x0200000004800670

def z400 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e023f1f8e0fe3 0x89327011f8fc707f

def z401 : W := mkw 0x9f7dbffe0201ac03 0x04fbedfff0100d60 0xffffffff0001fe07 0xf7fffffff8000ff0

def z402 : W := mkw 0x000200000689082a 0x4000100000344841 0x000000000f810070 0x00000000007c0803

def z403 : W := mkw 0x7dfbd0e2fdfcc51c 0x23efde8717efe628 0xbfffd1c0fffec01b 0xfdfffe8e07fff600

def z404 : W := mkw 0x68fbd0e3b5fec79c 0x2347de871daff63c 0xe1ffd3e791fecf8f 0xdf0ffe9f3c8ff67c

def z405 : W := mkw 0x08f01470b150d550 0x804780a3858a86aa 0xd9f03ff8f1f1fffd 0xfecf81ffc78f8fff

def z406 : W := mkw 0x17002b0000000000 0x00b8015800000000 0x1e002c0000000000 0x20f0016000000000

def z407 : W := mkw 0x0002000004880008 0x0000100000244000 0x000000001f8e0018 0x0800000000fc7000

def z408 : W := mkw 0x02002b400201ac03 0x0010015a00100d60 0xd8003fc0e001fe1c 0x76c001fe07000ff0

def z409 : W := mkw 0x000000004a012803 0x0000000002500940 0x000000006e013010 0x0000000003700980

def z410 : W := mkw 0x0080004090008400 0x0004000204800420 0xd9803fc0f001fe1c 0xf6cc01fe07800ff0

def z411 : W := mkw 0x378f620ddeaf0aae 0x41bc7b106ef57855 0x67cfe23f1f8f0fff 0xbb3e7f11f8fc787f

def z412 : W := mkw 0x1f692b0000000000 0x00fb495800000000 0xbfffffc000000007 0xf5fffffe00000000

def z413 : W := mkw 0x4286624d96bfcfaa 0x621433126cb5fe7d 0x664e223f9fffcfff 0xbb327111fcfffe7f

def z414 : W := mkw 0x3d6b04106dc8105c 0x81eb5820836e4082 0x3e4e2c186f813070 0x21f27160c37c0983

def z415 : W := mkw 0x28eb4000fdec001c 0x01475a0007ef6000 0x207fc000fffe001b 0x0903fe0007fff000

def z416 : W := mkw 0x0870143000000000 0x004380a180000000 0x98301c0000000000 0x44c180e000000000

def z417 : W := mkw 0x3d6b40006dec001c 0x01eb5a00036f6000 0x3e7fc0006ffe0013 0x29f3fe00037ff000

def z418 : W := mkw 0x0010143000000000 0x000080a180000000 0x80003c3800000004 0x040001e1c0000000

def z419 : W := mkw 0x3d6b00006dc8001c 0x01eb5800036e4000 0x3e7e0000eff00019 0x79f3f000077f8000

def z420 : W := mkw 0x00020001068b0aaa 0x4000100008345855 0x404020381f8f0ffd 0x3a020101c0fc787f

def z421 : W := mkw 0x0006000d068b0aaa 0x4000300068345855 0x604e003f1f8f0ffb 0x0b027001f8fc787f

def z422 : W := mkw 0x17062b0c4e89282b 0x40b8315862744941 0x3e4e2c186f813070 0x21f27160c37c0983

def z423 : W := mkw 0x0a76363d27db5bfa 0xc053b1b1e93edadf 0x667e223f1fff0fff 0xbb33f111f8fff87f

def z424 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x604e223f018f0fe7 0x0b027111f80c787f

def z425 : W := mkw 0x0286620d96af0aaa 0x401433106cb57855 0x67ffe23f9fff0fff 0xfb3fff11fcfff87f

def z426 : W := mkw 0x000009400000a401 0x0000004a00000520 0x80001dc00000f000 0x040000ee00000780

def z427 : W := mkw 0x0204220d02030aa2 0x4010211068101855 0x4600223f1e010ffc 0xb2300111f8f0087f

def z428 : W := mkw 0x0006000d048a02a8 0x4000300068245015 0x200e0007000e0002 0x0100700038007000

def z429 : W := mkw 0x0000000000105140 0x800000000000828a 0x400000000001f1e0 0x0200000000000f8f

def z430 : W := mkw 0x5590d9e2d834e501 0x22ac86cf16c1a728 0x99b1ddc0e070f000 0x44cd8eee07038780

def z431 : W := mkw 0x800d808e00000000 0x04006c0470000000 0x200fc00700000002 0x01007e0038000000

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000200000018d 0x1a0000010000000c

def z433 : W := mkw 0x0280224092018c02 0x0014011204900c60 0xc78033c09e01ce1c 0xf63c019e04f00e70

def z434 : W := mkw 0x4080c0c390268680 0x220406061c813434 0xc181d3c7900ece0e 0xd60c0e9e3c807670

def z435 : W := mkw 0x0216322d069b4baa 0x4010b1916834da5d 0xe67e323f9fffcfff 0xff33f191fcfffe7f

def z436 : W := mkw 0x001090a200000000 0x0000848510000000 0x81b1d1c000000000 0x440d8e8e00000000

def z437 : W := mkw 0x02002b400201ac03 0x0010015a00100d60 0x000003c000000e00 0x0000001e00000070

def z438 : W := mkw 0x971dbbae00000000 0x04b8eddd70000000 0xa7bfd3e700000007 0xd53dfe9f38000000

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400038018001e1 0x08020001c00c000f

def z440 : W := mkw 0x35894000d8240004 0x01ac4a0006c12000 0x0181c00000000000 0x000c0e0000000000

def z441 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8303c38e071f1e4 0x46c181e1c7038f8f

def z442 : W := mkw 0xd78debcf90268680 0x26bc6f5e7c813434 0x278fc3c7100e0e02 0x813c7e1e38807070

def z443 : W := mkw 0x3deb4001ffef0abe 0x41ef5a000fff7855 0x7fffc000ffff0ffb 0xfbfffe0007fff87f

def z444 : W := mkw 0x9f7dbfbe4a012803 0x04fbedfdf2500940 0xbfffffff6e013017 0xf5fffffffb700980

def z445 : W := mkw 0x3f6f220d6fcb0abe 0x41fb79106b7e5855 0x7e4e223f7f8f0fff 0xbbf27111fbfc787f

def z446 : W := mkw 0x4010d0e30036c780 0x220086871801b63c 0xc031d3e7007ecf87 0x0e018e9f3803f67c

def z447 : W := mkw 0x286b000025c8001c 0x01435800012e4000 0x204e000001800000 0x01027000000c0000

def z448 : W := mkw 0x4090d0e29034c500 0x220486871481a628 0x81b1d1c0907ec00b 0xdc0d8e8e0483f600

def z449 : W := mkw 0xd79dfbef9036c780 0x26bcefdf7c81b63c 0xe7bfd3e7907ecf8f 0xdf3dfe9f3c83f67c

def z450 : W := mkw 0x7dfbd0a3fdfe439c 0x23efde851feff21c 0x3fffc027fffe019b 0xf9fffe013ffff00c

def z451 : W := mkw 0x0870143000104100 0x004380a180008208 0xd8703c388070c18d 0x7ec381e1c403860c

def z452 : W := mkw 0x887f94bf048a02a8 0x4443fca5f8245015 0x207fc03f018e01e3 0x0903fe01f80c700f

def z453 : W := mkw 0x17002b004a012803 0x00b8015802500940 0xde003c00ee01f01c 0x76f001e007700f80

def z454 : W := mkw 0x7deb4041fdfec79c 0x23ef5a020feff63c 0x7fffc000fffecf9b 0xfbfffe0007fff67c

def z455 : W := mkw 0x0860000021400010 0x00430000010a0000 0x1840000061800010 0x20c20000030c0000

def z456 : W := mkw 0x4870d4b3217653d0 0xa24386a5990bb29e 0xd871fc3fe1fff1ff 0x7ec38fe1ff0fff8f

def z457 : W := mkw 0x0000000021505150 0x80000000010a828a 0xd8003c00e1f1f1fc 0x7ec001e0070f8f8f

def z458 : W := mkw 0x0206220c0689082a 0x4010311060344841 0x664e20380f8101fd 0x3b327101c07c080f

def z459 : W := mkw 0x7df9d0e3f976c794 0x23efce871fcbb63c 0xd9b1d3e7f07ecf8f 0xdecd8e9f3f83f67c

def z460 : W := mkw 0x759bd0e3dcbec78c 0x23acde871ee5f63c 0xe7bfd3e79e7ecf8f 0xdf3dfe9f3cf3f67c

def z461 : W := mkw 0x2002400025ec001c 0x01001200012f6000 0x0000000001fe0000 0x08000000000ff000

def z462 : W := mkw 0x28eb4000b5ec001c 0x01475a0005af6000 0x21ffc00091fe000b 0xd90ffe00048ff000

def z463 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x4070203801f101fd 0x3a038101c00f880f

def z464 : W := mkw 0x48f0d4f3b176d7d0 0xa24786a79d8bb6be 0xc1f1d3ff91fecfef 0xde0f8e9ffc8ff67f

def z465 : W := mkw 0x401094f30012d7c0 0xa20084a7980096be 0xc0003fff0001ffe4 0x060001fff8000fff

def z466 : W := mkw 0x3d6b400025ec001c 0x01eb5a00012f6000 0x3fffc00001fe0003 0xf9fffe00000ff000

def z467 : W := mkw 0xa87fd4be25ec001c 0x0543fea5f12f6000 0x207fc03f01fe0003 0x0903fe01f80ff000

def z468 : W := mkw 0xc294ffff9036c780 0x2614a7fffc81b63c 0xc1b1ffff907ecf8f 0xde0d8ffffc83f67c

def z469 : W := mkw 0x3deb4000dcac000c 0x01ef5a0006e56000 0x3fffc0001e0e0003 0xf1fffe0000f07000

def z470 : W := mkw 0x0000000102030aa2 0x4000000008101855 0x4000000000010fe0 0x020000000000087f

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0003c000001f004 0x060001e000000f80

def z472 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x40700038e1f1f1f9 0x0a038001c70f8f8f

def z473 : W := mkw 0x00800000d8000000 0x0004000006c00000 0x00000000fe000018 0x0000000007f00000

def z474 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000eff00010 0x61fffe00077f8000

def z475 : W := mkw 0x408040409034c500 0x220402020481a628 0x000000008070c000 0x0000000004038600

def z476 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x27ffc3ff00000003 0x813ffe1ff8000000

def z477 : W := mkw 0x286b400025ec001c 0x01435a00012f6000 0x387fc000e1fe001b 0x79c3fe00070ff000

def z478 : W := mkw 0xc87dd4bf00364380 0x2643eea5f801b21c 0x207fc03f007e0183 0x0903fe01f803f00c

def z479 : W := mkw 0x0200220002010802 0x0010011000100840 0x4000220000010e04 0x0200011000000870

def z480 : W := mkw 0x400080c300028680 0x2200040618001434 0x000003c700000e00 0x0000001e38000070

def z481 : W := mkw 0x17002b0000000000 0x00b8015800000000 0x078003c000000000 0x803c001e00000000

def z482 : W := mkw 0x00020001068b0aaa 0x4000100008345855 0x664e00001f8f0ffb 0xbb32700000fc787f

def z483 : W := mkw 0x00020001068b0aaa 0x4000100008345855 0x400002271f8f0fff 0x9a00001138fc787f

def z484 : W := mkw 0x4080404190268680 0x220402020c813434 0x00000000100e0e00 0x0000000000807070

def z485 : W := mkw 0x0000000021505150 0x80000000010a828a 0x0000000001f001e0 0x08000000000f800f

def z486 : W := mkw 0x2286620dffef0abe 0x411433106fff7855 0x664e223fffff0fff 0xbb327111fffff87f

def z487 : W := mkw 0x9fed2f5cda01ac03 0x04ff697ae6d00d60 0xffce3fd8fe01fe1c 0xf7fe71fec7f00ff0

def z488 : W := mkw 0x9f79bfb200000000 0x04fbcdfd90000000 0x9fb1ffc000000004 0xf4fd8ffe00000000

def z489 : W := mkw 0x1d79143000000000 0x00ebc8a180000000 0xbffffc3800000007 0xf5ffffe1c0000000

def z490 : W := mkw 0x801494be00000000 0x0400a4a5f0000000 0x0000003f00000000 0x00000001f8000000

def z491 : W := mkw 0x17062b0d068b0aaa 0x40b8315868345855 0xffce3fff1f8f0fff 0xfffe71fff8fc787f

def z492 : W := mkw 0x0000000100020280 0x0000000008001014 0x00000027000e0183 0x080000013800700c

def z493 : W := mkw 0x02802b409201ac03 0x0014015a04900d60 0xc1803fc09001fe0c 0xd60c01fe04800ff0

def z494 : W := mkw 0x57806b41da37ef83 0x22bc035a0ed1bf7c 0xdf803fc0fe7fff9c 0xfefc01fe07f3fffc

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000018101f8 0x0a000000000c080f

def z496 : W := mkw 0x3dfb5430fdec001c 0x01efdaa187ef6000 0xbffffc38fffe001f 0xfdffffe1c7fff000

def z497 : W := mkw 0x4210bbe30213ef83 0x221085df18109f7c 0xc0003fe70001ff84 0x060001ff38000ffc

def z498 : W := mkw 0x8214bfbe00000000 0x0410a5fdf0000000 0xa64e3fff00000007 0xb53271fff8000000

def z499 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x3e7fec3f00000003 0x21f3ff61f8000000

def z500 : W := mkw 0x3dfbd0a2fdec001c 0x01efde8517ef6000 0xbfffd3e7fffe001f 0xfdfffe9f3ffff000

def z501 : W := mkw 0x1ff03f70fb51fd53 0x80ff81fb87da8fea 0xdfb03fc0fe71fe1c 0xf6fd81fe07f38ff0

def z502 : W := mkw 0x0010143000105140 0x800080a18000828a 0x80001c000000f000 0x040000e000000780

def z503 : W := mkw 0x1f6f220d068b0aaa 0x40fb791068345855 0x7fffe23f1f8f0fff 0xfbffff11f8fc787f

def z504 : W := mkw 0x0860041021401050 0x80430020810a0082 0x58402c38618131fd 0x3ac20161c30c098f

def z505 : W := mkw 0x009010609010c500 0x0004808304808628 0xc1b013e09070cf8d 0xde0d809f0483867c

def z506 : W := mkw 0x8a7db6be00000000 0x0453edb5f0000000 0x267fe23f00000007 0xb133ff11f8000000

def z507 : W := mkw 0x378b6b40deadac0f 0x01bc5b5a06f56d60 0xff8fffc0fe0ffe1e 0xf7fc7ffe07f07ff0

def z508 : W := mkw 0x1509000000000000 0x00a8480000000000 0x278fc00000000002 0x813c7e0000000000

def z509 : W := mkw 0xdffdffff90268680 0x26ffeffffc813434 0xbfffffff100e0e07 0xf5fffffff8807070

def z510 : W := mkw 0x1710bba200000000 0x00b885dd10000000 0x9fb1ffe700000007 0xf4fd8fff38000000

def z511 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x5e002c00fe01fe18 0x22f0016007f00ff0

def z512 : W := mkw 0x17842b4dda03aea3 0x40bc215a6ed01d75 0xdf803ffffe01fffc 0xf6fc01fffff00fff

def z513 : W := mkw 0x8204ab8e00000000 0x0410255c70000000 0x000003c700000000 0x0000001e38000000

def z514 : W := mkw 0x0286224d968b8eaa 0x401431126cb45c75 0xe7ce33ff9f8fcfff 0xff3e719ffcfc7e7f

def z515 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x4000223f1f8f0ffc 0x0a000111f8fc787f

def z516 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e20181f8f0ff8 0x2b327100c0fc787f

def z517 : W := mkw 0x17042b0c00000000 0x00b8215860000000 0xbfce3fff00000007 0xf5fe71fff8000000

def z518 : W := mkw 0x978dabceda01ac03 0x04bc6d5e76d00d60 0x278fc3c71e000e02 0x813c7e1e38f00070

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000020010000e0c 0x9200001000800070

def z520 : W := mkw 0x20804000f9640014 0x0104020007cb2000 0x00000000e0700000 0x0000000007038000

def z521 : W := mkw 0x0a76363c27d9597a 0xc053b1b1e13ecacb 0xfe7e3c38eff1f1fd 0x7ff3f1e1c77f8f8f

def z522 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98703c38e070f005 0x74c381e1c7038780

def z523 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x660e223f1e0f0fe6 0x83307111f8f0787f

def z524 : W := mkw 0x401090e30012c780 0x220084871800963c 0xc00013e7100ecf8f 0x9e00009f3880767c

def z525 : W := mkw 0x001090a300020280 0x0000848518001014 0xc1b1d3e7100e0f8f 0xde0d8e9f3880707c

def z526 : W := mkw 0x3de94000f9640014 0x01ef4a0007cb2000 0x3fffc000e0700003 0xf1fffe0007038000

def z527 : W := mkw 0xbfffffbedcac000c 0x05fffffdf6e56000 0xbfffffff1e0e0007 0xf5fffffff8f07000

def z528 : W := mkw 0x0206220c0689082a 0x4010311060344841 0x260e00000e000000 0x0130700000700000

def z529 : W := mkw 0x001090a200000000 0x0000848510000000 0x800013e700000004 0x0400009f38000000

def z530 : W := mkw 0x3d6b00006dc8001c 0x01eb5800036e4000 0x3fffc0006f800013 0xf1fffe00037c0000

def z531 : W := mkw 0x0214363d02135be2 0xc010a1b1e8109adf 0xc0003e3f0001ffe4 0x060001f1f8000fff

def z532 : W := mkw 0x00800040fb51fd53 0x8004000207da8fea 0x40000000fff1fff8 0x0a00000007ff8fff

def z533 : W := mkw 0x0204220c02010822 0x4010211060100841 0x0000201800010060 0x00000100c0000803

def z534 : W := mkw 0x0080000090000000 0x0004000004800000 0x0180000090000008 0xd00c000004800000

def z535 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x39ffc000e1fe0003 0x49cffe00070ff000

def z536 : W := mkw 0x17802b41da03ae83 0x00bc015a0ed01d74 0xdf803fe7fe0fff9f 0xfefc01ff3ff07ffc

def z537 : W := mkw 0x40804041da37ef83 0x220402020ed1bf7c 0x40000000fe7fff98 0x0a00000007f3fffc

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040203800000005 0x30020101c0000000

def z539 : W := mkw 0x5790fbe2da35ed03 0x22bc87df16d1af68 0xdfb1ffc0fe71fe1c 0xf6fd8ffe07f38ff0

def z540 : W := mkw 0x0006000d048a02a8 0x4000300068245015 0x604e203f018f01ff 0x3b027101f80c780f

def z541 : W := mkw 0x0000041000001040 0x8000002080000082 0x00002c1800013060 0x00000160c0000983

def z542 : W := mkw 0x3f6b2b006fc9281f 0x01fb5958037e4940 0x3e4e2c006f813010 0x21f27160037c0980

def z543 : W := mkw 0x9f7fbfbe04880008 0x04fbfdfdf0244000 0xbfffffff1f8e001f 0xfdfffffff8fc7000

def z544 : W := mkw 0x3fef620cffed083e 0x41ff7b1067ff6841 0x3fffe018ffff007b 0xf9ffff00c7fff803

def z545 : W := mkw 0x9ffdffbe90240000 0x04ffeffdf4812000 0xbfffffff907e000f 0xfdfffffffc83f000

def z546 : W := mkw 0x0206220c0689082a 0x4010311060344841 0x264e20181f8f007b 0xb9327100c0fc7803

def z547 : W := mkw 0x4296f2ef96bfcfaa 0x6214b7977cb5fe7d 0xe7bfd3e79e7ecf8f 0xdf3dfe9f3cf3f67c

def z548 : W := mkw 0x48f0d4f3b176d7d0 0xa24786a79d8bb6be 0xd9b1dfe7f07eff8f 0xdecd8eff3f83f7fc

def z549 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xd9803fc0e001fe04 0x46cc01fe07000ff0

def z550 : W := mkw 0x9f6d2f1c00000000 0x04fb6978e0000000 0x3e4e2e3f00000007 0xb1f27171f8000000

def z551 : W := mkw 0xbf6f2f1c6dc8001c 0x05fb7978e36e4000 0x3e4e2c186f800010 0x21f27160c37c0000

def z552 : W := mkw 0x00800040da01ac03 0x0004000206d00d60 0xd8003c00fe01fe1c 0x76c001e007f00ff0

def z553 : W := mkw 0x20824000fdec001c 0x0104120007ef6000 0x01b1c000fffe001b 0xd80d8e0007fff000

def z554 : W := mkw 0x0004000d000202a0 0x4000200068001015 0x0000003f000001e0 0x00000001f800000f

def z555 : W := mkw 0x17862b4dde8baeab 0x40bc315a6ef45d75 0x67ce23ff1f8f0fff 0xbb3e711ff8fc787f

def z556 : W := mkw 0xbdf9ddb2f9640014 0x05efceed97cb2000 0x99b1ddc0e0700000 0x44cd8eee07038000

def z557 : W := mkw 0x0204220c00000000 0x0010211060000000 0x0000223f00000004 0x00000111f8000000

def z558 : W := mkw 0xdfffffff96bfcfaa 0x66fffffffcb5fe7d 0xffffffff9fffcfff 0xfffffffffcfffe7f

def z559 : W := mkw 0x9d7d94be00000000 0x04ebeca5f0000000 0x3fffc03f00000003 0xf1fffe01f8000000

def z560 : W := mkw 0x8216bfbf068b0aaa 0x4410b5fdf8345855 0xe64e3fff1f8f0fff 0xbf3271fff8fc787f

def z561 : W := mkw 0x17002b004a012803 0x00b8015802500940 0x9f803fc06e013014 0xf4fc01fe03700980

def z562 : W := mkw 0x0206220d048a02a8 0x4010311068245015 0x264e223f018e01e7 0xb9327111f80c700f

def z563 : W := mkw 0x9794bffeda01ac03 0x04bca5fff6d00d60 0xdf803ffffe01fe1c 0xf6fc01fffff00ff0

def z564 : W := mkw 0x0010102000104100 0x0000808100008208 0x803010008070c000 0x4401808004038600

def z565 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x18700038e1f001f9 0x78c38001c70f800f

def z566 : W := mkw 0x0860000021400010 0x00430000010a0000 0x58702038e1f101fd 0x7ac38101c70f880f

def z567 : W := mkw 0x8a7fb6bf068b0aaa 0x4453fdb5f8345855 0x667fe23f1f8f0fff 0xbb33ff11f8fc787f

def z568 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x9f803fc01e000e04 0xf4fc01fe00f00070

def z569 : W := mkw 0x0870143021400010 0x004380a1810a0000 0x98703c38e1f0001d 0x7cc381e1c70f8000

def z570 : W := mkw 0x9d799db200000000 0x04ebcced90000000 0x99f1fdf800000005 0x74cf8fefc0000000

def z571 : W := mkw 0x02022201068b0aaa 0x4010111008345855 0x460022001f8f0ffc 0xba30011000fc787f

def z572 : W := mkw 0x0870143000105140 0x804380a18000828a 0xd8703c380001f1e5 0x76c381e1c0000f8f

def z573 : W := mkw 0x7df9d0e2f974c514 0x23efce8717cba628 0x99b1d1c0e070c000 0x44cd8e8e07038600

def z574 : W := mkw 0x978dabceda01ac03 0x04bc6d5e76d00d60 0xff8fffc7fe01fe1e 0xf7fc7ffe3ff00ff0

def z575 : W := mkw 0x0080404090248400 0x0004020204812420 0xc1b1d3c0907ece0f 0xde0d8e9e0483f670

def z576 : W := mkw 0x9fffbfffde8baeab 0x44fffdfffef45d75 0xffffffffff8fffff 0xfffffffffffc7fff

def z577 : W := mkw 0x970fab8f068b0aaa 0x44b87d5c78345855 0x278fc3c71e0e0e02 0x813c7e1e38f07070

def z578 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0xfffffc00fffff01f 0xffffffe007ffff80

def z579 : W := mkw 0x02002b0000000000 0x0010015800000000 0x80003fc000000004 0x040001fe00000000

def z580 : W := mkw 0xbdffd4befdec001c 0x05effea5f7ef6000 0x3fffc03ffffe001b 0xf9fffe01fffff000

def z581 : W := mkw 0x28f25430fdfc515c 0x814792a187efe28a 0xd8703c38fffff1fd 0x7ec381e1c7ffff8f

def z582 : W := mkw 0x0216b2af068b0aaa 0x4010b59578345855 0xe7fff3ff1f8f0fff 0xff3fff9ff8fc787f

def z583 : W := mkw 0x0002000004880008 0x0000100000244000 0x264e00000f800010 0x21327000007c0000

def z584 : W := mkw 0x200b400004ac000c 0x01005a0000256000 0x200fc000000e0002 0x01007e0000007000

def z585 : W := mkw 0x401090e30012c780 0x220084871800963c 0xc03013e78070cf8d 0x5e01809f3c03867c

def z586 : W := mkw 0x9f7d3f3c00000000 0x04fbe9f9e0000000 0xbe7e3c3800000005 0x75f3f1e1c0000000

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x400020000001001c 0x3200010000000800

def z588 : W := mkw 0x15800940d800a401 0x00ac004a06c00520 0x018001c000000000 0x000c000e00000000

def z589 : W := mkw 0x4090d0e29034c500 0x220486871481a628 0xc1b1d3c09070ce0c 0xd60d8e9e04838670

def z590 : W := mkw 0x009090e290008400 0x0004848714800420 0xc1b1d3e79000ce0f 0xd60d8e9f3c800670

def z591 : W := mkw 0x9f6f2f1d068b0aaa 0x44fb7978e8345855 0x7e4e2e3f1f8f0fff 0xbbf27171f8fc787f

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040201801810070 0x20020100c00c0803

def z593 : W := mkw 0x0080004090008400 0x0004000204800420 0x018003c010000e00 0x800c001e00800070

def z594 : W := mkw 0x1f703f3021505150 0x80fb81f9810a828a 0xdff03ff8e1f1f1fd 0xfeff81ffc70f8f8f

def z595 : W := mkw 0x0000000000104100 0x0000000000008208 0x400000008070c188 0x0a0000000403860c

def z596 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x660e02271e0e0f8f 0x9b30701138f0707c

def z597 : W := mkw 0x9714bfbe00000000 0x04b8a5fdf0000000 0x9f803fff00000004 0xf4fc01fff8000000

def z598 : W := mkw 0x0010143000105140 0x800080a18000828a 0xc0303c388071f1ed 0x5e0181e1c4038f8f

def z599 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3e4e0000fffe0018 0x29f2700007fff000

def z600 : W := mkw 0x401090e20010c500 0x2200848710008628 0x800011c00000c000 0x0400008e00000600

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x01b1c00000000003 0xd00d8e0000000000

def z602 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x1f802fc07e013e10 0xa0fc017e03f009f0

def z603 : W := mkw 0x0010143000105140 0x800080a18000828a 0xc0403c380181f1fd 0x3e0201e1c00c0f8f

def z604 : W := mkw 0x0860000021400010 0x00430000010a0000 0x0070000001f00001 0x08038000000f8000

def z605 : W := mkw 0x20824000fdfc515c 0x8104120007efe28a 0x40000000fffff1f8 0x0a00000007ffff8f

def z606 : W := mkw 0x0204220d02030aa2 0x4010211068101855 0x4000223f100f0fef 0x9a000111f880787f

def z607 : W := mkw 0xb78feb8edcac000c 0x05bc7f5c76e56000 0x278fc3c71e0e0002 0x813c7e1e38f07000

def z608 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fbfc000fe7e0002 0xc1fdfe0007f3f000

def z609 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x81b1d1e7807ec183 0x4c0d8e8f3c03f60c

def z610 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xc78013c09e00ce0c 0xd63c009e04f00670

def z611 : W := mkw 0x4286e2cf96af8eaa 0x621437167cb57c75 0x278fc3c71e0e0e02 0x813c7e1e38f07070

def z612 : W := mkw 0x4000c08300260280 0x2200060418013014 0x0001c007000e0002 0x00000e0038007000

def z613 : W := mkw 0x0a70363023515952 0x805381b1811a8aca 0xde703e38fff1fffd 0xfef381f1c7ff8fff

def z614 : W := mkw 0x0870143000000000 0x004380a180000000 0xd8703c38018101fd 0x7ec381e1c00c080f

def z615 : W := mkw 0xbf7fffbe25ec001c 0x05fbfffdf12f6000 0xbfffffff01fe0007 0xfdfffffff80ff000

def z616 : W := mkw 0x17862b4dde8baeab 0x40bc315a6ef45d75 0x278e03c71e0e0e02 0x813c701e38f07070

def z617 : W := mkw 0x0004000c00000000 0x0000200060000000 0x204e003f00000003 0x01027001f8000000

def z618 : W := mkw 0x287b543025fc515c 0x8143daa1812fe28a 0x207fc03801fe01e3 0x0903fe01c00ff00f

def z619 : W := mkw 0x0002000127db5bfa 0xc0001000093edadf 0x40000000fffffff8 0x0a00000007ffffff

def z620 : W := mkw 0x0876143d25da53f8 0xc043b0a1e92ed29f 0xf87e3c3fe1fff1ff 0x7fc3f1e1ff0fff8f

def z621 : W := mkw 0x0872143127db5bfa 0xc04390a1893edadf 0xd8703c38fffffffd 0x7ec381e1c7ffffff

def z622 : W := mkw 0x1d79143021505150 0x80ebc8a1810a828a 0xfffffc38e1f1f1ff 0xffffffe1c70f8f8f

def z623 : W := mkw 0x9d799db221505150 0x84ebcced910a828a 0xd9f1fdf8e1f1f1fd 0x7ecf8fefc70f8f8f

def z624 : W := mkw 0x0a66261d27cb1afa 0xc0533130e93e58d7 0x7e4e2e3f7f8f3fff 0xbbf27171fbfc79ff

def z625 : W := mkw 0x4286e2cf96af8eaa 0x621437167cb57c75 0x67cfe3ff1f8f0fff 0xbb3e7f1ff8fc787f

def z626 : W := mkw 0xdf7dffbf00364380 0x26fbeffdf801b21c 0xbfffffff007e0187 0xfdfffffff803f00c

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00010008000c00c 0x5600008004000600

def z628 : W := mkw 0x1790bbe2da01ac03 0x00bc85df16d00d60 0xdfb1ffe7fe01fe1f 0xf6fd8fff3ff00ff0

def z629 : W := mkw 0x0200220002010802 0x0010011000100840 0xde003e00fe01fe1c 0xf6f001f007f00ff0

def z630 : W := mkw 0x40804041b176d7d0 0xa20402020d8bb6be 0x40000000f1fffff8 0x0a000000078fffff

def z631 : W := mkw 0x0870102021504110 0x00438081010a8208 0xd8701020e1f0c19d 0x7ec38081070f860c

def z632 : W := mkw 0x0010102021505150 0x80008081010a828a 0xc0301020e1f1f1fd 0x5e018081070f8f8f

def z633 : W := mkw 0x0010102100124380 0x000080810800921c 0xc0301227907ecf8f 0xde0180913c83f67c

def z634 : W := mkw 0x0000000002010802 0x0000000000100840 0x400000001e010e18 0x0200000000f00870

def z635 : W := mkw 0x0090502090344100 0x000482810481a208 0xc1b1d020907ec18f 0xde0d8e810483f60c

def z636 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x478023c01e010e1c 0xb23c011e00f00870

def z637 : W := mkw 0x15800000d8000000 0x00ac000006c00000 0x19800000e0000000 0x40cc000007000000

def z638 : W := mkw 0x15800000d8000000 0x00ac000006c00000 0xdf803c00fe01f01c 0xf6fc01e007f00f80

def z639 : W := mkw 0x3d6b00006dc8001c 0x01eb5800036e4000 0x3e4e00007f8e001b 0xb9f2700003fc7000

def z640 : W := mkw 0x48f0d4f2b174d550 0xa24786a7958ba6aa 0x99b1ddc0e070f000 0x44cd8eee07038780

def z641 : W := mkw 0x48f0d4f39036c780 0x224786a79c81b63c 0xd9f1ffff907ecf8f 0xfecf8ffffc83f67c

def z642 : W := mkw 0x4216f2af06bf4baa 0x6210b7957835fa5d 0x667fe23f1fff0fff 0xbb33ff11f8fff87f

def z643 : W := mkw 0x0080400090240000 0x0004020004812000 0x00000000907e0008 0x080000000483f000

def z644 : W := mkw 0x3fff763dffff5bfe 0xc1fffbb1effffadf 0xfffffe3fffffffff 0xfffffff1ffffffff

def z645 : W := mkw 0x3feb6b00fdec001c 0x01ff5b5807ef6000 0xbfffffc0fffe001f 0xfdfffffe07fff000

def z646 : W := mkw 0x9f7d3f3c21505150 0x84fbe9f9e10a828a 0xfe7e3c38e1f1f1fd 0x7ff3f1e1c70f8f8f

def z647 : W := mkw 0x4090d0e29034c500 0x220486871481a628 0xc1b1d1e08070c18d 0x5e0d8e8f0403860c

def z648 : W := mkw 0x17002b004a012803 0x00b8015802500940 0x060000000e000000 0x0030000000700000

def z649 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x478003c0fe01fe18 0x823c001e07f00ff0

def z650 : W := mkw 0x020222000689080a 0x0010111000344840 0x664e22001f8f0e1f 0xbb32711000fc7870

def z651 : W := mkw 0x17802b40fb51fd53 0x80bc015a07da8fea 0xdf803fc0fff1fffc 0xfefc01fe07ff8fff

def z652 : W := mkw 0x2a6f620d27ef0abe 0x41537b10693f7855 0x667fe23f1fff0fff 0xbb33ff11f8fff87f

def z653 : W := mkw 0x0862000025c80018 0x00431000012e4000 0x3e7e0000fffe001b 0xf9f3f00007fff000

def z654 : W := mkw 0x0000000100020280 0x0000000008001014 0x4000022700000f84 0x020000113800007c

def z655 : W := mkw 0x0860000021505150 0x80430000010a828a 0x58700000e1f1f1f9 0x7ac38000070f8f8f

def z656 : W := mkw 0x0200220002010802 0x0010011000100840 0x060002001e000e00 0x8030001000f00070

def z657 : W := mkw 0x3fef620dffef0abe 0x41ff7b106fff7855 0x3fffc207fffe0e1b 0xf9fffe103ffff070

def z658 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98701c00e1f0f019 0x7cc380e0070f8780

def z659 : W := mkw 0x0010102000104100 0x0000808100008208 0xc070303881f1c1fd 0x7e038181c40f8e0f

def z660 : W := mkw 0x48f0d4f2b174d550 0xa24786a7958ba6aa 0xd9f1fdf8e1f1f1fd 0x7ecf8fefc70f8f8f

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x98003c0000000004 0x74c001e000000000

def z662 : W := mkw 0x0860041021401050 0x80430020810a0082 0x0040001801800060 0x00020000c00c0003

def z663 : W := mkw 0x1fe02f50fb41bc53 0x80ff017a87da0de2 0xdfc03fd8ff81fe7c 0xf6fe01fec7fc0ff3

def z664 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x660e02071f8f0ffa 0x8b30701038fc787f

def z665 : W := mkw 0x08f01470fb51fd53 0x804780a387da8fea 0xd8703c38fff1fffd 0x7ec381e1c7ff8fff

def z666 : W := mkw 0x0860000021400010 0x00430000010a0000 0xd8703c00e1f1f01d 0x7ec381e0070f8f80

def z667 : W := mkw 0x08f05430b1745150 0x804782a1858ba28a 0xd9f1fc38f1fff1ff 0xfecf8fe1c78fff8f

def z668 : W := mkw 0x00020001048a0288 0x0000100008245014 0x664e02271f8e0f9f 0xbb32701138fc707c

def z669 : W := mkw 0x02802b40da01ac03 0x0014015a06d00d60 0xc0003fc0fe01fe1c 0x060001fe07f00ff0

def z670 : W := mkw 0x20824001ffef0abe 0x410412000fff7855 0x40000000ffff0ff8 0x0a00000007fff87f

def z671 : W := mkw 0x3df95430f9745154 0x81efcaa187cba28a 0x99b1dc00e070f000 0x44cd8ee007038780

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030000080700009 0x5801800004038000

def z673 : W := mkw 0x0000000100020280 0x0000000008001014 0x4040223f118f0fff 0xba020111f88c787f

def z674 : W := mkw 0x15804000d8240000 0x00ac020006c12000 0x1fb1c000fe7e001b 0xf8fd8e0007f3f000

def z675 : W := mkw 0x487094f32152d7d0 0xa24384a7990a96be 0xd8703fffe1f1fffd 0x7ec381ffff0f8fff

def z676 : W := mkw 0x0870143021401050 0x804380a1810a0082 0x98703c3861813075 0x74c381e1c30c0983

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000001800019 0x38020000000c0000

def z678 : W := mkw 0x2869400021640014 0x01434a00010b2000 0x0031c00000700000 0x00018e0000038000

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000e001f018 0x0200000007000f80

def z680 : W := mkw 0x0a66220d27cb0aba 0x40533110693e5855 0x7e7e223fffff0fff 0xfbf3f111fffff87f

def z681 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc181d3e7100ecf86 0x860c0e9f3880767c

def z682 : W := mkw 0x08e04000b1640010 0x00470200058b2000 0x19f1c000f1fe001b 0xf8cf8e00078ff000

def z683 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e203f0f8f01f3 0x29327101f87c780f

def z684 : W := mkw 0x17062b0d4e8b2aab 0x40b831586a745955 0x7e4e2e3f7f8f3fff 0xbbf27171fbfc79ff

def z685 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xc070103881f0c1ed 0x5e038081c40f860f

def z686 : W := mkw 0x1df01d70f950f551 0x80ef80eb87ca87aa 0xd9f03df8e1f1f1fd 0x7ecf81efc70f8f8f

def z687 : W := mkw 0x02042b4d0203aea3 0x4010215a68101d75 0xc0003fff0001ffe4 0x060001fff8000fff

def z688 : W := mkw 0x4010d0a300364380 0x220086851801b21c 0x4031c227107e0f8f 0x9a018e113883f07c

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x264e000000000003 0xb132700000000000

def z690 : W := mkw 0x3f6f220c6fc9083e 0x41fb7910637e4841 0x3e4e20186f810070 0x21f27100c37c0803

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000022700000007 0x9000001138000000

def z692 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x9f803dc0ee01f010 0x64fc01ee07700f80

def z693 : W := mkw 0x350b00004c88000c 0x01a8580002644000 0x260e00000e000000 0x0130700000700000

def z694 : W := mkw 0x17802200da010802 0x00bc011006d00840 0x5f802200fe010e1c 0xf2fc011007f00870

def z695 : W := mkw 0x02103f700211fd43 0x801081fb80108fea 0xc0003ff80001ffe4 0x060001ffc0000fff

def z696 : W := mkw 0x4096d0ef94bec7a8 0x6204b6877ca5f63d 0xe1ffd3ff91fecfef 0xdf0ffe9ffc8ff67f

def z697 : W := mkw 0x3deb4040ffedac1f 0x01ef5a0207ff6d60 0x7fffc000fffffe1b 0xfbfffe0007fffff0

def z698 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e223f1e0e0e07 0xb1327111f8f07070

def z699 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8403c386181f1f4 0x26c201e1c30c0f8f

def z700 : W := mkw 0x17862b4dde8baeab 0x40bc315a6ef45d75 0xff8e3fc7fe0ffe1e 0xf7fc71fe3ff07ff0

def z701 : W := mkw 0x9f7fbfbf068b0aaa 0x44fbfdfdf8345855 0xbfffffff1e0e0e07 0xf5fffffff8f07070

def z702 : W := mkw 0x9f6f2f1c0689082a 0x44fb7978e0344841 0x3e4e2c180f810070 0x21f27160c07c0803

def z703 : W := mkw 0x5790fbe3da37ef83 0x22bc87df1ed1bf7c 0xc7b1d3e79e7ecf8f 0xde3d8e9f3cf3f67c

def z704 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fcfc0007f8e0012 0xa1fe7e0003fc7000

def z705 : W := mkw 0x0000004000008400 0x0000000200000420 0xc00013c00000ce04 0x0600009e00000670

def z706 : W := mkw 0x5790bbe3da13ef83 0x22bc85df1ed09f7c 0xdf803fe7fe01ff9c 0xf6fc01ff3ff00ffc

def z707 : W := mkw 0x970dab8e21505150 0x84b86d5c710a828a 0x678fc3c7e1f1f1fa 0x8b3c7e1e3f0f8f8f

def z708 : W := mkw 0x0006000d068b0aaa 0x4000300068345855 0x664e003f1f8f0ffb 0xbb327001f8fc787f

def z709 : W := mkw 0x68f25471fdfed7dc 0xa34792a38feff6be 0xd8703c38fffffffd 0x7ec381e1c7ffffff

def z710 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x27ffe3ff00000007 0xb13fff1ff8000000

def z711 : W := mkw 0x3deb4410fdec105c 0x81ef5a2087ef6082 0x7fffec38ffff31ff 0xfbffff61c7fff98f

def z712 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff8070000f 0xfdfffffffc038000

def z713 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffff01f1f1e7 0xfffffffff80f8f8f

def z714 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff01810077 0xf5fffffff80c0803

def z715 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fc07e01fe14 0xa6fc01fe03f00ff0

def z716 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x58702c38e1f1f1f9 0x2ac38161c70f8f8f

def z717 : W := mkw 0x3deb4040fdec841c 0x01ef5a0207ef6420 0x7fffc000fffece1b 0xfbfffe0007fff670

def z718 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x81b1d3e7907ecf83 0xcc0d8e9f3c83f67c

def z719 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fe0fe01ff9d 0xfefc01ff07f00ffc

def z720 : W := mkw 0x1586094ddc8aa6a9 0x40ac304a6ee45535 0xb9ce1dffe18ef1e3 0x4dce70efff0c778f

def z721 : W := mkw 0x359b5430dcbc514c 0x81acdaa186e5e28a 0xe78ffc381e0ff1e6 0x873c7fe1c0f07f8f

def z722 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x01b1c3c7107e0e02 0x800d8e1e3883f070

def z723 : W := mkw 0xa296ffbefdec001c 0x0514b7fdf7ef6000 0x80003ffffffe001c 0x0c0001fffffff000

def z724 : W := mkw 0x9f7dbfbe48000000 0x04fbedfdf2400000 0xbfffffff6e000017 0xf5fffffffb700000

def z725 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffff61f131f7 0xfdfffffffb0f898f

def z726 : W := mkw 0x0860041021505150 0x80430020810a828a 0x58402c38e1f1f1fd 0x3ac20161c70f8f8f

def z727 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x41b1c3e7107e0f8f 0x9a0d8e1f3883f07c

def z728 : W := mkw 0x0000000021505150 0x80000000010a828a 0xd8403c38e1f1f1fd 0x7ec201e1c70f8f8f

def z729 : W := mkw 0x9d7d9dbe21505150 0x84ebecedf10a828a 0xf9fffdffe1f1f1ff 0x7fcfffefff0f8f8f

def z730 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000fffe0018 0x69fffe0007fff000

def z731 : W := mkw 0x48e0c4d3b16696d0 0xa24706269d8b34b6 0x19c1efdf718f3e72 0xa0ce0f7efb8c79f3

def z732 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8403c38e1f1f1fc 0x2ec201e1c70f8f8f

def z733 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff0000018f 0xfffffffff800000c

def z734 : W := mkw 0x001090a300124380 0x000084851800921c 0xc1b1d3e7907ecf8f 0xde0d8e9f3c83f67c

def z735 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc0001ffe0003 0xf9fffe0000fff000

def z736 : W := mkw 0xdfed6f5d9036c780 0x26ff6b7aec81b63c 0x7e4e2c18907ecf88 0x2bf27160c483f67c

def z737 : W := mkw 0x3deb4940fdeca41d 0x01ef5a4a07ef6520 0xfffffdc0fffff01f 0xffffffee07ffff80

def z738 : W := mkw 0x5710fba34a376b83 0x22b887dd1a51bb5c 0x1e31ec276e7f3193 0x28f18f613b73f98c

def z739 : W := mkw 0x15800940da01ac03 0x00ac004a06d00d60 0xd9803dc0fe01fe1c 0x76cc01ee07f00ff0

def z740 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xbf8fdfc700000002 0xc5fc7efe38000000

def z741 : W := mkw 0x0a76363d27db5bfa 0xc053b1b1e93edadf 0xbe3e1e07fe7efe02 0xc5f1f0f03ff3f7f0

def z742 : W := mkw 0x0204a28e00000000 0x0010251470000000 0x27cfe3ff00000007 0xb13e7f1ff8000000

def z743 : W := mkw 0x3deb4040fdec841c 0x01ef5a0207ef6420 0xbfffd1c0fffec01b 0xfdfffe8e07fff600

def z744 : W := mkw 0x3d6b40006dec001c 0x01eb5a00036f6000 0x3e7fc000effe001b 0x79f3fe00077ff000

def z745 : W := mkw 0x4080c0c390268680 0x220406061c813434 0x01b1c3c7907e0e02 0xc00d8e1e3c83f070

def z746 : W := mkw 0x4082404196af8eaa 0x620412020cb57c75 0x000000001e0e0e00 0x0000000000f07070

def z747 : W := mkw 0x17892b40da01ac03 0x00bc495a06d00d60 0xff8fffc0fe01fe1e 0xf7fc7ffe07f00ff0

def z748 : W := mkw 0x60824041b5fec79c 0x230412020daff63c 0x4000000091fecf88 0x0a000000048ff67c

def z749 : W := mkw 0x087094b221505150 0x804384a5910a828a 0xd9f1fdf8e1f1f1fd 0x7ecf8fefc70f8f8f

def z750 : W := mkw 0x17842b4cda01ac23 0x40bc215a66d00d61 0xdf803fd8fe01fe7c 0xf6fc01fec7f00ff3

def z751 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0xe64e3e3f1f8fffff 0xbf3271f1f8fc7fff

def z752 : W := mkw 0x4090d4f39036d7c0 0xa20486a79c81b6be 0xd9b1fffff07fffff 0xfecd8fffff83ffff

def z753 : W := mkw 0x88fd94feda01ac03 0x0447eca7f6d00d60 0x607fc03ffe01fe1b 0x0303fe01fff00ff0

def z754 : W := mkw 0x971dbbae00000000 0x04b8eddd70000000 0xa78fd3e700000006 0x853c7e9f38000000

def z755 : W := mkw 0x9d7b9db3068b0aaa 0x44ebdced98345855 0xd9b1ddc01f8f0ff8 0x4ecd8eee00fc787f

def z756 : W := mkw 0x0204a28e00000000 0x0010251470000000 0x278fc3c700000002 0x813c7e1e38000000

def z757 : W := mkw 0x3deb4000dcac000c 0x01ef5a0006e56000 0x3fffc0009e7e000b 0xf9fffe0004f3f000

def z758 : W := mkw 0x1d7990a221504110 0x00ebcc85110a8208 0xffffd3e7e1f0c19f 0xfffffe9f3f0f860c

def z759 : W := mkw 0x4080c0c390268680 0x220406061c813434 0x41b1c3e7907e0f8f 0xda0d8e1f3c83f07c

def z760 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffffe1f0f1e7 0xfdffffffff0f878f

def z761 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x7fffc200fffe0e1f 0xfbfffe1007fff070

def z762 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0xfffffc38fffff1ff 0xffffffe1c7ffff8f

def z763 : W := mkw 0x15824000dcac0008 0x00ac120006e56000 0x3fffc000fffe001b 0xf9fffe0007fff000

def z764 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc227fffe001f 0xf9fffe113ffff000

def z765 : W := mkw 0x20824000fdec001c 0x0104120007ef6000 0x27ffc000fffe001b 0xf93ffe0007fff000

def z766 : W := mkw 0x7d7b90e36ddac79c 0x23ebdc871b6ed63c 0xfe4e13e76f80cf94 0x27f2709f3b7c067c

def z767 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfbfffc700000006 0xf5fdfffe38000000

def z768 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffdfc700000003 0xf5fffefe38000000

def z769 : W := mkw 0x2a6b6b4027edac1f 0x01535b5a013f6d60 0xe07fffc001fffe07 0x0f03fffe000ffff0

def z770 : W := mkw 0x800d808e00000000 0x04006c0470000000 0x218fc3c700000002 0x810c7e1e38000000

def z771 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xa7ffffff00000007 0x853ffffff8000000

def z772 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfbfffff00000006 0xc5fdfffff8000000

def z773 : W := mkw 0x0010102000104100 0x0000808100008208 0xd8703c38e1f1f1fd 0x7ec381e1c70f8f8f

def z774 : W := mkw 0x3deb4900fdec001c 0x01ef5a4807ef6000 0xbfffddc0fffe001b 0xfdfffeee07fff000

def z775 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xfe7e3c38e1f1f1ff 0xfff3f1e1c70f8f8f

def z776 : W := mkw 0x9d799db200000000 0x04ebcced90000000 0xbfffdfe700000007 0xf5fffeff38000000

def z777 : W := mkw 0x9f7dbfbe21401050 0x84fbedfdf10a0082 0xbfffffff01800067 0xf5fffffff80c0003

def z778 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xffce3fc0fe01fe1f 0xf7fe71fe07f00ff0

def z779 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xd9803fc0fe01fe1c 0x46cc01fe07f00ff0

def z780 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0xfe4e3e3f1f8f0fff 0xfff271f1f8fc787f

def z781 : W := mkw 0x9f7dbfbe00105140 0x84fbedfdf000828a 0xbfffffff000001e7 0xf5fffffff800000f

def z782 : W := mkw 0x4214b6ff0213dfe2 0xe210a5b7f8109eff 0xc0003fff0001ffe4 0x060001fff8000fff

def z783 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fc0fe0ffe1f 0xfefc01fe07f07ff0

def z784 : W := mkw 0x1ff03f70fb51fd53 0x80ff81fb87da8fea 0x07f003f81ff00fe1 0x883f801fc0ff807f

def z785 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e7807ecf87 0x4e0d8e9f3c03f67c

def z786 : W := mkw 0x3d6b40006dec001c 0x01eb5a00036f6000 0x3fffc0006ffe0013 0xf9fffe00037ff000

def z787 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3c7907ece0e 0xd60d8e9e3c83f670

def z788 : W := mkw 0x801d90ae00000000 0x0400ec8570000000 0xa1bfd3e700000007 0xd50dfe9f38000000

def z789 : W := mkw 0x60824041fdfed7dc 0xa30412020feff6be 0x40000000fffffff8 0x0a00000007ffffff

def z790 : W := mkw 0x17842b4cda01ac03 0x00bc215a66d00d60 0xffce3fffff81ffff 0xfffe71fffffc0fff

def z791 : W := mkw 0x9f7dbfbe02010802 0x04fbedfdf0100840 0xbfffffff0e010017 0xf5fffffff8700800

def z792 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x27bfc3c700000003 0xd13dfe1e38000000

def z793 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fbfc000fe7e001a 0xf1fdfe0007f3f000

def z794 : W := mkw 0x4080c0c39036c780 0x220406061c81b63c 0x41b1c3c7907ecf8b 0xda0d8e1e3c83f67c

def z795 : W := mkw 0x8214bfbf02135be2 0xc410a5fdf8109adf 0xc0003fff0001ffe4 0x060001fff8000fff

def z796 : W := mkw 0x970dab8e4a012803 0x04b86d5c72500940 0x278fc3c70e000002 0x813c7e1e38700000

def z797 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffe038fffe001f 0xf9ffff01c7fff000

def z798 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x67cfe3ff018101ff 0xbb3e7f1ff80c080f

def z799 : W := mkw 0x4090d4f39036d7c0 0xa20486a79c81b6be 0xc1b1dfe7907eff8f 0xde0d8eff3c83f7fc

def z800 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc7b1d3e79e7ecf9f 0xfe3d8e9f3cf3f67c

def z801 : W := mkw 0x970dab8e02010802 0x04b86d5c70100840 0x678fe3c71e010e1e 0xb33c7f1e38f00870

def z802 : W := mkw 0x4090d4f39036d7c0 0xa20486a79c81b6be 0xc1f1ffff91ffffff 0xfe0f8ffffc8fffff

def z803 : W := mkw 0x17806b40da25ac03 0x00bc035a06d12d60 0xdf81ffc0fe0ffe1e 0xf6fc0ffe07f07ff0

def z804 : W := mkw 0x087990a200000000 0x0043cc8510000000 0xa1ffd3e700000007 0xd50ffe9f38000000

def z805 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e223f1f8f0ff6 0xa3327111f8fc787f

def z806 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fc0fe01fe04 0xc6fc01fe07f00ff0

def z807 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0xbfffd3c0fffe001f 0xfdfffe9e07fff000

def z808 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdfb1ffc0fe01fe1f 0xf6fd8ffe07f00ff0

def z809 : W := mkw 0xbf7dbfbe69400014 0x05fbedfdf34a0000 0xbfffffff60000007 0xf5fffffffb000000

def z810 : W := mkw 0x3deb4040fdeca41d 0x01ef5a0207ef6520 0x3fffc000fffef01b 0xf9fffe0007fff780

def z811 : W := mkw 0x9f7dbfbe00001040 0x84fbedfdf0000082 0xbfffffff00013067 0xf5fffffff8000983

def z812 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff000101e7 0xf7fffffff800080f

def z813 : W := mkw 0x950d898e00000000 0x04a86c4c70000000 0x218fc1c700000002 0x010c7e0e38000000

def z814 : W := mkw 0x0214b2ae00104100 0x0010a59570008208 0xe7fff3ff81f1c1ff 0xff3fff9ffc0f8e0f

def z815 : W := mkw 0x1d7994b221505150 0x80ebcca5910a828a 0xffffffffe1f1f1ff 0xffffffffff0f8f8f

def z816 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x27cfe3df00000002 0xa13e7f1ef8000000

def z817 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e7907ecf86 0xc60d8e9f3c83f67c

def z818 : W := mkw 0x37896b40da25ac07 0x01bc4b5a06d12d60 0xdf81ffc0fe01fe1c 0xf6fc0ffe07f00ff0

def z819 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x27cfc3ff00000003 0x813e7e1ff8000000

def z820 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8303c38e1f1f1fc 0x4ec181e1c70f8f8f

def z821 : W := mkw 0x151990a200000000 0x00a8cc8510000000 0xa7bfd3e700000007 0xd53dfe9f38000000

def z822 : W := mkw 0x15800940da01ac03 0x00ac004a06d00d60 0x99801dc0fe00fe00 0x44cc00ee07f007f0

def z823 : W := mkw 0x9f7dbfbe21400010 0x04fbedfdf10a0000 0xffffffffe1f101ff 0xffffffffff0f880f

def z824 : W := mkw 0x1d7994b200000000 0x00ebcca590000000 0xbfffffff00000007 0xf5fffffff8000000

def z825 : W := mkw 0x9f6daf9e00000000 0x04fb6d7cf0000000 0xbfcfffdf00000006 0xf5fe7ffef8000000

def z826 : W := mkw 0x9f6daf9e00000000 0x04fb6d7cf0000000 0x3fffefdf00000003 0xf1ffff7ef8000000

def z827 : W := mkw 0x9f6f2f1c27c9187a 0xc4fb7978e13e48c3 0x3e4e2c186f813070 0x21f27160c37c0983

def z828 : W := mkw 0x971dbbae00000000 0x04b8eddd70000000 0xa7fff3ff00000007 0xf53fff9ff8000000

def z829 : W := mkw 0xbf6f2f1c6fc9083e 0x45fb7978e37e4841 0x3e4e2c186f810070 0x21f27160c37c0803

def z830 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x667e223f9fff0fff 0xfb33f111fcfff87f

def z831 : W := mkw 0x17002b0002010802 0x00b8015800100840 0xdf803fc0fe01fe1c 0xf6fc01fe07f00ff0

def z832 : W := mkw 0xbf6f2f1c6fc9281f 0x05fb7978e37e4940 0x3e4e2c186f813010 0x21f27160c37c0980

def z833 : W := mkw 0x9f7dbfbe00104100 0x04fbedfdf0008208 0xffffffff81f1c1ff 0xfffffffffc0f8e0f

def z834 : W := mkw 0x9f7dbfbe4a012803 0x04fbedfdf2500940 0xffffffffee01f01f 0xf7ffffffff700f80

def z835 : W := mkw 0x0a74b6be00000000 0x0053a5b5f0000000 0xbfffffff00000007 0xf5fffffff8000000

def z836 : W := mkw 0x3fed620dfb670ab6 0x41ff6b106fdb3855 0x59b1e23fe0710fe4 0x42cd8f11ff03887f

def z837 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff018001e7 0xfdfffffff80c000f

def z838 : W := mkw 0x3deb4940fdeca41d 0x01ef5a4a07ef6520 0xffffdfc0fffefe1f 0xfffffefe07fff7f0

def z839 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff10000e0f 0xf7fffffff8800070

def z840 : W := mkw 0x0090d0e290248400 0x0004868714812420 0xc1b1d3e7907ece0f 0xde0d8e9f3c83f670

def z841 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803dc0fe01fe18 0x66fc01ee07f00ff0

def z842 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x3fffc3ff00000003 0xf1fffe1ff8000000

def z843 : W := mkw 0x358b4000fdec001c 0x01ac5a0007ef6000 0x27bfc000fffe001b 0xd93dfe0007fff000

def z844 : W := mkw 0x1f79bba200000000 0x00fbcddd10000000 0xbfffffe700000007 0xf5ffffff38000000

def z845 : W := mkw 0x02002b400201ac03 0x0010015a00100d60 0xde003fc0fe01fe1c 0xf6f001fe07f00ff0

def z846 : W := mkw 0x9f7dbfbe4a012803 0x04fbedfdf2500940 0xbfffffff0e000007 0xf5fffffff8700000

def z847 : W := mkw 0x02802b40da01ac03 0x0014015a06d00d60 0xd8003fc0fe01fe1c 0x76c001fe07f00ff0

def z848 : W := mkw 0x1de94000d8240000 0x00ef4a0006c12000 0x3fffc000fe7e001b 0xf9fffe0007f3f000

def z849 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803ff8fe01fffc 0xf6fc01ffc7f00fff

def z850 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf801fc0fe00fe0c 0xd6fc00fe07f007f0

def z851 : W := mkw 0x08e24000b5ec0018 0x0047120005af6000 0x3fffc000fffe001b 0xf9fffe0007fff000

def z852 : W := mkw 0x0006000d048a02a8 0x4000300068245015 0x664e023f1f8e0fff 0xbb327011f8fc707f

def z853 : W := mkw 0x8a7db6be00000000 0x0453edb5f0000000 0xa7fff3ff00000007 0xf53fff9ff8000000

def z854 : W := mkw 0x9f7dbfbe21401050 0x84fbedfdf10a0082 0xffffffff618131ff 0xfffffffffb0c098f

def z855 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e223f1f8f0ffc 0x2b327111f8fc787f

def z856 : W := mkw 0x0090d0a390260280 0x000486851c813014 0xc1b1d3e7907e0f8f 0xde0d8e9f3c83f07c

def z857 : W := mkw 0x17002b404a01ac03 0x00b8015a02500d60 0xde003fc0ee01fe1c 0x76f001fe07700ff0

def z858 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000fffe0003 0xc9fffe0007fff000

def z859 : W := mkw 0x8214bfbe00000000 0x0410a5fdf0000000 0xa7ffffff00000007 0xf53ffffff8000000

def z860 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffff01f101ff 0xfffffffff80f880f

def z861 : W := mkw 0x9f7dbfbe00105140 0x84fbedfdf000828a 0xffffffff0181f1ff 0xfffffffff80c0f8f

def z862 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbffffdff00000003 0x65ffffeff8000000

def z863 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x9f801fc0fe00fe18 0xf4fc00fe07f007f0

def z864 : W := mkw 0x4214bbef0213efa3 0x6210a5df78109f7d 0xc0003fff0001ffe4 0x060001fff8000fff

def z865 : W := mkw 0x4090d4f39036c780 0x220486a79c81b63c 0xc1b1ffff907ecf8f 0xde0d8ffffc83f67c

def z866 : W := mkw 0x9d7d9dbe00000000 0x04ebecedf0000000 0xb9fffdff00000007 0x75cfffeff8000000

def z867 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x27bfc3c700000002 0x813dfe1e38000000

def z868 : W := mkw 0x3deb4040fdec841c 0x01ef5a0207ef6420 0x3fffc3c0fffe0e1b 0xf9fffe1e07fff070

def z869 : W := mkw 0x971dbfbe00000000 0x04b8edfdf0000000 0xa7cfffff00000007 0xb53e7ffff8000000

def z870 : W := mkw 0x9f7dbfbe23515952 0x84fbedfdf11a8aca 0xfffffffffff1ffff 0xffffffffffff8fff

def z871 : W := mkw 0x4082404196af8eaa 0x620412020cb57c75 0x400000001f8f0ff8 0x0a00000000fc787f

def z872 : W := mkw 0x971dbfbe00000000 0x04b8edfdf0000000 0xbf8fffff00000006 0xf5fc7ffff8000000

def z873 : W := mkw 0x17842b4cda01ac03 0x00bc215a66d00d60 0xdf803ffffe01fe1c 0xf6fc01fffff00ff0

def z874 : W := mkw 0xc214bfff0213ef83 0x2610a5fff8109f7c 0xc0003fff0001ff84 0x060001fff8000ffc

def z875 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fc0ee01fe14 0x66fc01fe07700ff0

def z876 : W := mkw 0x68f25061fdfec79c 0x234792830feff63c 0xd8701020fffecf9d 0x7ec3808107fff67c

def z877 : W := mkw 0x9f6dab8e21400010 0x04fb6d5c710a0000 0x3fffc3c7e1f0001b 0xf9fffe1e3f0f8000

def z878 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3e7fc000fffe001b 0x29f3fe0007fff000

def z879 : W := mkw 0x02062b0d068b2aab 0x4010315868345955 0x664e2e3f1f8f3fff 0xbb327171f8fc79ff

def z880 : W := mkw 0x087094b221505150 0x804384a5910a828a 0xd8703fffe1f1f1fd 0x7ec381ffff0f8f8f

def z881 : W := mkw 0x4090d0e3d836c780 0x220486871ec1b63c 0xc1b1d3e7fe7ecf9f 0xde0d8e9f3ff3f67c

def z882 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703c38e1f1f1e5 0x4ec381e1c70f8f8f

def z883 : W := mkw 0x9f7dbfbe21401050 0x84fbedfdf10a0082 0xffffffffe181f07f 0xf7ffffffff0c0f83

def z884 : W := mkw 0x9f7dbfbe00104100 0x04fbedfdf0008208 0xbfffffff8070c007 0xf5fffffffc038600

def z885 : W := mkw 0x4296f2ee96bdcd2a 0x6214b79774b5ee69 0xa7fff1d88ff1c070 0x653fff8ec47f8e03

def z886 : W := mkw 0x9f7dbfbe00105140 0x84fbedfdf000828a 0xffffffffe001f1ff 0xf7ffffffff000f8f

def z887 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fc0ff81fffc 0xfefc01fe07fc0fff

def z888 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffff81f0c1ef 0xfffffffffc0f860f

def z889 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffdf00000002 0xe5fffffef8000000

def z890 : W := mkw 0x4082404194bec788 0x220412020ca5f63c 0x400000009ffecf98 0x0a00000004fff67c

def z891 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x01b1c3e7907e0f8b 0xd80d8e1f3c83f07c

def z892 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xff8fffc7e001f01e 0xf7fc7ffe3f000f80

def z893 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffdfff00000003 0xc5fffefff8000000

def z894 : W := mkw 0x8a7dbfbe00000000 0x0453edfdf0000000 0xa1ffffff00000007 0xd50ffffff8000000

def z895 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff00000004 0x65fffffff8000000

def z896 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffffe071f01f 0xf7ffffffff038f80

def z897 : W := mkw 0x9f7dbfbe48002001 0x04fbedfdf2400100 0xbfffffff60003007 0xf5fffffffb000180

def z898 : W := mkw 0x9d7d9dbe00000000 0x04ebecedf0000000 0xb9ffdfff00000007 0xd5cffefff8000000

def z899 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc0007ffe0013 0xa9fffe0003fff000

def z900 : W := mkw 0x60824041dcae868c 0x230412020ee57434 0x000000001e0e0e00 0x0000000000f07070

def z901 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xa78fd3c700000006 0xd53c7e9e38000000

def z902 : W := mkw 0x17806b40da25ac03 0x00bc035a06d12d60 0xdf803fc0fe7ffe1c 0xfefc01fe07f3fff0

def z903 : W := mkw 0x9f6dab8e00000000 0x04fb6d5c70000000 0x3fffe3ff00000007 0xf1ffff1ff8000000

def z904 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffffe1f001ff 0xfdffffffff0f800f

def z905 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0x27ffc3ff01f001e3 0x893ffe1ff80f800f

def z906 : W := mkw 0x1d6b000025c80018 0x00eb5800012e4000 0x3fffc000fffe001b 0xf9fffe0007fff000

def z907 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffff00700007 0xf5fffffff8038000

def z908 : W := mkw 0x9f7dbfbe00105140 0x84fbedfdf000828a 0xbfffffff0000f007 0xf5fffffff8000780

def z909 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xde703c38fff1f1fd 0xfef381e1c7ff8f8f

def z910 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdfb03fc0fe71fe1d 0xfefd81fe07f38ff0

def z911 : W := mkw 0x9f7dbfbe00104100 0x04fbedfdf0008208 0xffffffff0000c187 0xf7fffffff800060c

def z912 : W := mkw 0x887d94be00000000 0x0443eca5f0000000 0x21ffc3ff00000003 0x810ffe1ff8000000

def z913 : W := mkw 0x887994b221505150 0x8443cca5910a828a 0xd871fc38e1f1f1fd 0x7ec38fe1c70f8f8f

def z914 : W := mkw 0x9f6daf9e00000000 0x04fb6d7cf0000000 0x27cfc3df00000002 0x813e7e1ef8000000

def z915 : W := mkw 0x17002b404a01ac03 0x00b8015a02500d60 0xdf803fc06e01fe14 0xf6fc01fe03700ff0

def z916 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0xe7ce33ff1f8f0fff 0xff3e719ff8fc787f

def z917 : W := mkw 0x9f7dbfbe00105140 0x84fbedfdf000828a 0xffffffff8071f1ef 0xfffffffffc038f8f

def z918 : W := mkw 0x40824041b7ffdffa 0xe20412020dbffeff 0x40000000fffffff8 0x0a00000007ffffff

def z919 : W := mkw 0x60824041ffffcfbe 0x630412020ffffe7d 0x40000000ffffcff8 0x0a00000007fffe7f

def z920 : W := mkw 0x971dbfbe00105140 0x84b8edfdf000828a 0xe78fffff0001f1e6 0x873c7ffff8000f8f

def z921 : W := mkw 0x9f7dbfbe02010802 0x04fbedfdf0100840 0xffffffff00010e07 0xf7fffffff8000870

def z922 : W := mkw 0x0870143021505150 0x804380a1810a828a 0x98703c38e1f1f1f1 0x6cc381e1c70f8f8f

def z923 : W := mkw 0x5786ebcfdeafaeab 0x62bc375e7ef57d75 0x278fc3c71e0e0e02 0x813c7e1e38f07070

def z924 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff100e000f 0xfdfffffff8807000

def z925 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xd9b1d3e7f07ecf9f 0xfecd8e9f3f83f67c

def z926 : W := mkw 0x3deb4410fdec001c 0x01ef5a2087ef6000 0x3fffec18fffe001b 0xf9ffff60c7fff000

def z927 : W := mkw 0x60824041ffffef9f 0x230412020fffff7c 0x40000000ffffff98 0x0a00000007fffffc

def z928 : W := mkw 0x9f7dbfbe21504110 0x04fbedfdf10a8208 0xffffffffe1f0c19f 0xffffffffff0f860c

def z929 : W := mkw 0x17806b40da25ac03 0x00bc035a06d12d60 0xdfb1ffc0fe71fe1c 0xf6fd8ffe07f38ff0

def z930 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x27ffc0009ffe000b 0xd93ffe0004fff000

def z931 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e7f07fff9f 0xde0d8e9f3f83fffc

def z932 : W := mkw 0x9f7dbfbe21400010 0x04fbedfdf10a0000 0xbfffffff61800017 0xf5fffffffb0c0000

def z933 : W := mkw 0x0a74b6be21505150 0x8053a5b5f10a828a 0xffffffffe1f1f1ff 0xffffffffff0f8f8f

def z934 : W := mkw 0x9f7dbfbe02010802 0x04fbedfdf0100840 0xffffffff1f810fff 0xfffffffff8fc087f

def z935 : W := mkw 0x1f6d2b0c00000000 0x00fb695860000000 0xbfffffff00000007 0xf5fffffff8000000

def z936 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e223fff8fffff 0xbb327111fffc7fff

def z937 : W := mkw 0x9f7dbfbe21401050 0x84fbedfdf10a0082 0xbfffffffe1f1307f 0xfdffffffff0f8983

def z938 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x9f803fc0fe01fe10 0xe4fc01fe07f00ff0

def z939 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x7fffc000ffff01fb 0xfbfffe0007fff80f

def z940 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffffe181f1ff 0xffffffffff0c0f8f

def z941 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffe018ffff007b 0xf9ffff00c7fff803

def z942 : W := mkw 0x9f7dbfbe6b413853 0x84fbedfdf35a09c2 0xbfffffff6f813077 0xf5fffffffb7c0983

def z943 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff0001f007 0xf7fffffff8000f80

def z944 : W := mkw 0x0860000021400010 0x00430000010a0000 0xd8703c38e1f1f1fd 0x7ec381e1c70f8f8f

def z945 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e791ffcfff 0xde0d8e9f3c8ffe7f

def z946 : W := mkw 0x9f6daf9e00000000 0x04fb6d7cf0000000 0x3fcfefff00000007 0xb1fe7f7ff8000000

def z947 : W := mkw 0x0080404190268680 0x000402020c813434 0xc1b1d3e7907ecf8f 0xde0d8e9f3c83f67c

def z948 : W := mkw 0x9f7dbfbe02012803 0x04fbedfdf0100940 0xbfffffff00013007 0xf5fffffff8000980

def z949 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdfc03ff8fe01fe1d 0xf6fe01ffc7f00ff0

def z950 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x7e4e223fff8f0fff 0xfbf27111fffc787f

def z951 : W := mkw 0x4090d0e39036d7c0 0xa20486871c81b6be 0xc1b1d3e7907fffef 0xde0d8e9f3c83ffff

def z952 : W := mkw 0x970daf9e00000000 0x04b86d7cf0000000 0x278fefdf00000002 0x813c7f7ef8000000

def z953 : W := mkw 0x15800940da01ac03 0x00ac004a06d00d60 0xd9801fc0fe01fe1c 0xd6cc00fe07f00ff0

def z954 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1f1d3ff91fecfef 0xde0f8e9ffc8ff67f

def z955 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x81b1d3e7907ece07 0xd40d8e9f3c83f670

def z956 : W := mkw 0x9d7d9dbe00000000 0x04ebecedf0000000 0x21ffc1ff00000003 0x010ffe0ff8000000

def z957 : W := mkw 0x4010d0a300364380 0x220086851801b21c 0xc1b1d3e7107e0f8f 0xde0d8e9f3883f07c

def z958 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x81b1d3e7107e0f87 0xdc0d8e9f3883f07c

def z959 : W := mkw 0x9f7dbfbe21400010 0x04fbedfdf10a0000 0xffffffffe1f1f01f 0xffffffffff0f8f80

def z960 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1f1d3e791fecf9f 0xfe0f8e9f3c8ff67c

def z961 : W := mkw 0x9f7dbfbe00104100 0x04fbedfdf0008208 0xffffffffe071f19f 0xffffffffff038f8c

def z962 : W := mkw 0x087094b221505150 0x804384a5910a828a 0xd871fc3fe1f1f1ff 0x7ec38fe1ff0f8f8f

def z963 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703e38f1f1fffd 0xfec381f1c78f8fff

def z964 : W := mkw 0x9f6dab8e00000000 0x04fb6d5c70000000 0xbfffffc700000007 0xf5fffffe38000000

def z965 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e203f1f8f0ffb 0x2b327101f8fc787f

def z966 : W := mkw 0x9f6dab8e00000000 0x04fb6d5c70000000 0x3fcfc3c700000002 0xa1fe7e1e38000000

def z967 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff0001001f 0xf7fffffff8000800

def z968 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fbfc000fe7e000b 0xd9fdfe0007f3f000

def z969 : W := mkw 0x286b400025ec001c 0x01435a00012f6000 0x267fc0001ffe0003 0x8933fe0000fff000

def z970 : W := mkw 0x17842b4cda01ac03 0x00bc215a66d00d60 0xffce3fd8fe01fe1c 0xf7fe71fec7f00ff0

def z971 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff60013017 0xf5fffffffb000980

def z972 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x41b1c3e7907ecf8b 0x8a0d8e1f3c83f67c

def z973 : W := mkw 0x9f7dbfbe21400010 0x04fbedfdf10a0000 0xbfffffff01f00007 0xfdfffffff80f8000

def z974 : W := mkw 0x9f7dbfbe00104100 0x04fbedfdf0008208 0xbfffffff00700187 0xfdfffffff803800c

def z975 : W := mkw 0x4080c0c390268680 0x220406061c813434 0x01b1c3c7107e0e03 0x880d8e1e3883f070

def z976 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd9f1fc38e1f1f1ff 0xfecf8fe1c70f8f8f

def z977 : W := mkw 0x9f7dbbae00000000 0x04fbeddd70000000 0xbfffd3e700000007 0xf5fffe9f38000000

def z978 : W := mkw 0x978d2b4cda01ac03 0x04bc695a66d00d60 0xff8e3fc0fe01fe1c 0xf7fc71fe07f00ff0

def z979 : W := mkw 0x971dbbae00000000 0x04b8eddd70000000 0xa7bfd3c700000002 0xc53dfe9e38000000

def z980 : W := mkw 0x9d7d94be00000000 0x04ebeca5f0000000 0xbfffd3ff00000007 0xf5fffe9ff8000000

def z981 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x27ffc0001ffe001b 0xb93ffe0000fff000

def z982 : W := mkw 0x15800940d800a401 0x00ac004a06c00520 0xdf801fc0fe00fe1c 0xf6fc00fe07f007f0

def z983 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e223f1f8f0ff3 0xa9327111f8fc787f

def z984 : W := mkw 0x3deb4410fdec105c 0x81ef5a2087ef6082 0x3fffc018fffe007b 0xf9fffe00c7fff003

def z985 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x27bfc0001e7e0003 0x893dfe0000f3f000

def z986 : W := mkw 0x15800040d8008400 0x00ac000206c00420 0xdf803fc0fe01fe1c 0xf6fc01fe07f00ff0

def z987 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf801fc0fe01fe18 0xc6fc00fe07f00ff0

def z988 : W := mkw 0xc214bfff0213cfa2 0x6610a5fff8109e7d 0xc0003fff0001cfe4 0x060001fff8000e7f

def z989 : W := mkw 0x4092506196bfcfaa 0x620492830cb5fe7d 0xc07030389fffcffd 0x7e038181c4fffe7f

def z990 : W := mkw 0x28eb4000fdec001c 0x01475a0007ef6000 0x267fc000fffe001b 0xb933fe0007fff000

def z991 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x3f8fefc700000002 0xa1fc7f7e38000000

def z992 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdfc03fc0ff81fe1d 0xfefe01fe07fc0ff0

def z993 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000fe7e0003 0xf1fffe0007f3f000

def z994 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffffe000f007 0xf5ffffffff000780

def z995 : W := mkw 0x9f7dbfbe21400010 0x04fbedfdf10a0000 0xbfffffffe0700007 0xf5ffffffff038000

def z996 : W := mkw 0x00800040da01ac03 0x0004000206d00d60 0xd9803fc0fe01fe1c 0xf6cc01fe07f00ff0

def z997 : W := mkw 0x4082404196bfcfaa 0x620412020cb5fe7d 0x400000009e7ecf88 0x0a00000004f3f67c

def z998 : W := mkw 0x9f7dbfbe4a012803 0x04fbedfdf2500940 0xffffffff7e013e1f 0xf7fffffffbf009f0

def z999 : W := mkw 0x28eb4000b5ec001c 0x01475a0005af6000 0x27ffc0009ffe001b 0xf93ffe0004fff000

def z1000 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3c7907ecf8a 0xce0d8e9e3c83f67c

def z1001 : W := mkw 0x971dbbae00000000 0x04b8eddd70000000 0xbfbfffe700000007 0xf5fdffff38000000

def z1002 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xd9b1dfe7f07eff8f 0xdecd8eff3f83f7fc

def z1003 : W := mkw 0x9d7d9dbe21505150 0x84ebecedf10a828a 0xb9ffddffe1f0f1e3 0x4dcffeefff0f878f

def z1004 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000fffe0012 0xe1fffe0007fff000

def z1005 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfbfdfc7e070f002 0xc5fdfefe3f038780

def z1006 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0xbfffdc00fffef01b 0xfdfffee007fff780

def z1007 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xd9f1fffff1ffffff 0xfecf8fffff8fffff

def z1008 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703c38f1fff1ff 0xfec381e1c78fff8f

def z1009 : W := mkw 0x001090a200000000 0x0000848510000000 0xa7ffd3e700000007 0xf53ffe9f38000000

def z1010 : W := mkw 0x9d7d9dbe00000000 0x04ebecedf0000000 0xb9bfddc700000002 0x45cdfeee38000000

def z1011 : W := mkw 0x15800940da01ac03 0x00ac004a06d00d60 0xdf801dc0fe01fe18 0xf6fc00ee07f00ff0

def z1012 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd9f03ff8e1f1f1fd 0xfecf81ffc70f8f8f

def z1013 : W := mkw 0x60824041dcbec78c 0x230412020ee5f63c 0x400000009e7ecf88 0x0a00000004f3f67c

def z1014 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1f3ff907fcfef 0xde0d8f9ffc83fe7f

def z1015 : W := mkw 0x971dbfbe00000000 0x04b8edfdf0000000 0xa78fdfc700000002 0x853c7efe38000000

def z1016 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffff6181f1f7 0xf7fffffffb0c0f8f

def z1017 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1f3e7907fcf9f 0xfe0d8f9f3c83fe7c

def z1018 : W := mkw 0x0280224092018c02 0x0014011204900c60 0xdf803fc0fe01fe1c 0xf6fc01fe07f00ff0

def z1019 : W := mkw 0x4080c0c390268680 0x220406061c813434 0xc1b1d3c7907ece0f 0xde0d8e9e3c83f670

def z1020 : W := mkw 0x9f7dbfbe21401050 0x84fbedfdf10a0082 0xbfffffff60003007 0xf5fffffffb000180

def z1021 : W := mkw 0x1f7db2ae00000000 0x00fbed9570000000 0xbffff3ff00000007 0xf5ffff9ff8000000

def z1022 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e023f1f8e0fef 0x9b327011f8fc707f

def z1023 : W := mkw 0x887f94bf25da53f8 0xc443fca5f92ed29f 0x207fc03f01fe01e3 0x0903fe01f80ff00f

def z1024 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1f1f3ff907ecf8f 0xfe0f8f9ffc83f67c

def z1025 : W := mkw 0x3deb4940fdeca41d 0x01ef5a4a07ef6520 0x3fffc1c0fffe001b 0xf9fffe0e07fff000

def z1026 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e7107ecf87 0x8e0d8e9f3883f67c

def z1027 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x278fe3c700000006 0xb13c7f1e38000000

def z1028 : W := mkw 0x0082400094ac0008 0x0004120004a56000 0x27bfc0009e7e000b 0xd93dfe0004f3f000

def z1029 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x278fc3e700000007 0x913c7e1f38000000

def z1030 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffec00ffff301b 0xf9ffff6007fff980

def z1031 : W := mkw 0x4876d4bf25fe53f8 0xe243b6a5f92ff29f 0x207fc03f01fe01e3 0x0903fe01f80ff00f

def z1032 : W := mkw 0x60824041fdee869c 0x230412020fef7434 0x00000000fffe0e18 0x0800000007fff070

def z1033 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc000effe0013 0x69fffe00077ff000

def z1034 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703c18e1f1f1f8 0x6ec381e0c70f8f8f

def z1035 : W := mkw 0x20824041ffefaebf 0x410412020fff7d75 0x40000000fffffff8 0x0a00000007ffffff

def z1036 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e223f1f8f0fe7 0x8b327111f8fc787f

def z1037 : W := mkw 0x887d94be21505150 0x8443eca5f10a828a 0xf9ffffffe1f1f1ff 0xffcfffffff0f8f8f

def z1038 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x664e023f1f8f0ffb 0x8b327011f8fc787f

def z1039 : W := mkw 0x3deb4040fdec841c 0x01ef5a0207ef6420 0xffffffc0fffffe1f 0xfffffffe07fffff0

def z1040 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffffe1f0f01f 0xfdffffffff0f8780

def z1041 : W := mkw 0x0002400004ac0008 0x0000120000256000 0x267fc0001ffe001b 0xb933fe0000fff000

def z1042 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xa7ffd3ff00000007 0xd53ffe9ff8000000

def z1043 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fffc038fffe01fb 0xf9fffe01c7fff00f

def z1044 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0xbffffc00fffe001f 0xfdffffe007fff000

def z1045 : W := mkw 0x9f6dab8e00000000 0x04fb6d5c70000000 0x27ffc3c700000003 0x813ffe1e38000000

def z1046 : W := mkw 0x0860041021505150 0x80430020810a828a 0xd8403c18e1f1f1fc 0x7ec201e0c70f8f8f

def z1047 : W := mkw 0x9f6dab8e00000000 0x04fb6d5c70000000 0x3fbfc3c700000002 0xc1fdfe1e38000000

def z1048 : W := mkw 0x9f7dbfbe6b517953 0x84fbedfdf35a8bca 0xffffffffeff1f1ff 0xffffffffff7f8f8f

def z1049 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xb9ffffff00000007 0x45cffffff8000000

def z1050 : W := mkw 0x4214b2ef0213cfa2 0x6210a59778109e7d 0xc00013e70000cf84 0x0600009f3800067c

def z1051 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xbfcfffff00000007 0xf5fe7ffff8000000

def z1052 : W := mkw 0x970dab8e02010802 0x04b86d5c70100840 0x278fc3c71e000e02 0x813c7e1e38f00070

def z1053 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x7e4e2e3f7f8f3fff 0xbbf27171fbfc79ff

def z1054 : W := mkw 0x4010d0e30036c780 0x220086871801b63c 0xc1b1d3e7007ecf87 0xde0d8e9f3803f67c

def z1055 : W := mkw 0x001490ae00000000 0x0000a48570000000 0xa1ffd3ff00000007 0xd50ffe9ff8000000

def z1056 : W := mkw 0x9f7dbfbe02010822 0x44fbedfdf0100841 0xbfffffff00010067 0xf5fffffff8000803

def z1057 : W := mkw 0x7df9d4f2f974d554 0xa3efcea797cba6aa 0x99b1ddc0e070f000 0x44cd8eee07038780

def z1058 : W := mkw 0x3d6b40006dec001c 0x01eb5a00036f6000 0x267fc0000ffe0003 0x0933fe00007ff000

def z1059 : W := mkw 0x378f6b4ddeafaeaf 0x41bc7b5a6ef57d75 0x278fc3c71e0e0e02 0x813c7e1e38f07070

def z1060 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xe7ffd3e7907ecf8f 0xff3ffe9f3c83f67c

def z1061 : W := mkw 0x48f25471b7ffdffa 0xe24792a38dbffeff 0xd8703c38fffffffd 0x7ec381e1c7ffffff

def z1062 : W := mkw 0x3deb4410fdec105c 0x81ef5a2087ef6082 0x3fffcc00fffe301b 0xf9fffe6007fff180

def z1063 : W := mkw 0x3d6b40006dec001c 0x01eb5a00036f6000 0x3e7fc0007ffe001b 0xb9f3fe0003fff000

def z1064 : W := mkw 0x971dbfbe00000000 0x04b8edfdf0000000 0xa7bfffff00000007 0xd53dfffff8000000

def z1065 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffffe071f1e7 0xf7ffffffff038f8f

def z1066 : W := mkw 0x971dbfbe00000000 0x04b8edfdf0000000 0x278fc3ff00000002 0x813c7e1ff8000000

def z1067 : W := mkw 0xbdeb4d10fdec001c 0x05ef5a6887ef6000 0x3fffcc00fffe001b 0xf9fffe6007fff000

def z1068 : W := mkw 0x887d94be00000000 0x0443eca5f0000000 0xa1ffd1ff00000003 0x450ffe8ff8000000

def z1069 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x27ffc000fffe001b 0x893ffe0007fff000

def z1070 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e223f1f8e0fe7 0xb9327111f8fc707f

def z1071 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xa78fffc700000006 0x853c7ffe38000000

def z1072 : W := mkw 0x3d6b400025ec001c 0x01eb5a00012f6000 0x3fffc0001ffe001b 0xf9fffe0000fff000

def z1073 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703e3fe1f1f1ff 0xfec381f1ff0f8f8f

def z1074 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x264e023f1f8e0ffb 0xb9327011f8fc707f

def z1075 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x27ffc0009ffe001b 0xf93ffe0004fff000

def z1076 : W := mkw 0x3deb4000fdec105c 0x81ef5a0007ef6082 0x3fffc000ffff307b 0xf9fffe0007fff983

def z1077 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x3fbfc000fffe001a 0xc9fdfe0007fff000

def z1078 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x27bfc0009e7e0002 0xc13dfe0004f3f000

def z1079 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x7fffc000fffff01b 0xfbfffe0007ffff80

def z1080 : W := mkw 0x02062b0d068b0aaa 0x4010315868345855 0xe64e3fff1f8f0fff 0xbf3271fff8fc787f

def z1081 : W := mkw 0x9f6daf9e00000000 0x04fb6d7cf0000000 0x3f8fcfc700000002 0x81fc7e7e38000000

def z1082 : W := mkw 0x9f7dbfbe02010802 0x04fbedfdf0100840 0xfffffffffe01fe1f 0xf7fffffffff00ff0

def z1083 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x27bfc0001e7e0002 0x813dfe0000f3f000

def z1084 : W := mkw 0x971dbbae00000000 0x04b8eddd70000000 0x27bfc3e700000003 0x813dfe1f38000000

def z1085 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xd9b1ffe7907ecf8f 0xfecd8fff3c83f67c

def z1086 : W := mkw 0x1509808200000000 0x00a84c0410000000 0x278fc3c700000002 0x813c7e1e38000000

def z1087 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1ffe7907fff8f 0xde0d8fff3c83fffc

def z1088 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff0180001f 0xfdfffffff80c0000

def z1089 : W := mkw 0x286b400025ec001c 0x01435a00012f6000 0x3e7fc000fffe001b 0xf9f3fe0007fff000

def z1090 : W := mkw 0x17842b4cda01ac03 0x00bc215a66d00d60 0xff8e3fc7fe01fe1e 0xf7fc71fe3ff00ff0

def z1091 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfbfdfe700000007 0xd5fdfeff38000000

def z1092 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xbfffffffe1f1f077 0xf5ffffffff0f8f83

def z1093 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0xe64e323f9f8fcfff 0xff327191fcfc7e7f

def z1094 : W := mkw 0x9f7dbfbe02010802 0x04fbedfdf0100840 0xbfffffff1e000e07 0xf5fffffff8f00070

def z1095 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xde003fc0fe01fe1c 0x26f001fe07f00ff0

def z1096 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdfc03fd8ff81fe7c 0xf6fe01fec7fc0ff3

def z1097 : W := mkw 0x00020001048a0288 0x0000100008245014 0x664e223f1f8f0fff 0xbb327111f8fc787f

def z1098 : W := mkw 0x0870143021505150 0x804380a1810a828a 0xd8703c38e1f1f1f4 0x66c381e1c70f8f8f

def z1099 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0xffffd000fffec01f 0xfffffe8007fff600

def z1100 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xffffffff8000c00f 0xf7fffffffc000600

def z1101 : W := mkw 0x40824041debfefab 0x620412020ef5ff7d 0x40000000fffffff8 0x0a00000007ffffff

def z1102 : W := mkw 0x971dbbae00104100 0x04b8eddd70008208 0xe7bfd3e78070c18f 0xdf3dfe9f3c03860c

def z1103 : W := mkw 0x887d94be21505150 0x8443eca5f10a828a 0xe1ffd3ff81f0c1ef 0xdf0ffe9ffc0f860f

def z1104 : W := mkw 0x0214b2ae00000000 0x0010a59570000000 0xa7bfd3e700000007 0xd53dfe9f38000000

def z1105 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x7fffc020fffe019f 0xfbfffe0107fff00c

def z1106 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0x9f803fc0fe00fe04 0xf4fc01fe07f007f0

def z1107 : W := mkw 0x4090d0e390268680 0x220486871c813434 0x81b1d3e7907e0e0f 0xdc0d8e9f3c83f070

def z1108 : W := mkw 0x0010143021505150 0x800080a1810a828a 0xd8003c38e1f1f1fc 0x7ec001e1c70f8f8f

def z1109 : W := mkw 0x358b4000dcac000c 0x01ac5a0006e56000 0x3fbfc000fe7e001b 0xf9fdfe0007f3f000

def z1110 : W := mkw 0x9f7dbfbe21505150 0x84fbedfdf10a828a 0xffffffffe070f18f 0xffffffffff03878c

def z1111 : W := mkw 0x687bd4b325fe53dc 0xa343dea5992ff29e 0x207fc03f01fe01e3 0x0903fe01f80ff00f

def z1112 : W := mkw 0x3deb4000fdec001c 0x01ef5a0007ef6000 0x7fffe000ffff001f 0xfbffff0007fff800

def z1113 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffffe000001f 0xf5ffffffff000000

def z1114 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0x3fffefff00000003 0xa1ffff7ff8000000

def z1115 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfcfffff00000006 0xa5fe7ffff8000000

def z1116 : W := mkw 0x9f6daf9e21401050 0x84fb6d7cf10a0082 0x3fcfefdf61813072 0xa1fe7f7efb0c0983

def z1117 : W := mkw 0x4082404194bec7a8 0x620412020ca5f63d 0x4000000091fecfe8 0x0a000000048ff67f

def z1118 : W := mkw 0x4090d0e3d836e781 0x220486871ec1b73c 0xc1b1d3e7f07eff8f 0xde0d8e9f3f83f7fc

def z1119 : W := mkw 0x17802b40da01ac03 0x00bc015a06d00d60 0xdf803fe7fe01fe1f 0xf6fc01ff3ff00ff0

def z1120 : W := mkw 0x1deb400094ac0008 0x00ef5a0004a56000 0x3fffc0009ffe001b 0xf9fffe0004fff000

def z1121 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0x81b1d3c7907ece0b 0xdc0d8e9e3c83f670

def z1122 : W := mkw 0x1714bbae00000000 0x00b8a5dd70000000 0xbfffffff00000007 0xf5fffffff8000000

def z1123 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x27cfc3c700000003 0xb13e7e1e38000000

def z1124 : W := mkw 0x286b400025ec001c 0x01435a00012f6000 0x267fc0000ffe0013 0x2933fe00007ff000

def z1125 : W := mkw 0x0879143021505150 0x8043c8a1810a828a 0xf87ffc38e1f1f1ff 0x7fc3ffe1c70f8f8f

def z1126 : W := mkw 0x4214b2af02134ba2 0x6210a59578109a5d 0x4000223f00010fe4 0x02000111f800087f

def z1127 : W := mkw 0x9f7dbfbe00000000 0x04fbedfdf0000000 0xbfffffff1e00001f 0xf5fffffff8f00000

def z1128 : W := mkw 0x17002b404a01ac03 0x00b8015a02500d60 0xde003fc07e01fe1c 0xb6f001fe03f00ff0

def z1129 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x3f8fc3c700000002 0xf1fc7e1e38000000

def z1130 : W := mkw 0x4090d0e39036c780 0x220486871c81b63c 0xc1b1d3e7907ecf8c 0x4e0d8e9f3c83f67c

def z1131 : W := mkw 0x0860041021505150 0x80430020810a828a 0x58702c18e1f1f1f9 0x7ac38160c70f8f8f

def z1132 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x278fe3ff00000006 0x813c7f1ff8000000

def z1133 : W := mkw 0x9d7d9dbe00000000 0x04ebecedf0000000 0xbfffddff00000003 0xf5fffeeff8000000

def z1134 : W := mkw 0x887d94be00000000 0x0443eca5f0000000 0xb9ffffff00000007 0xf5cffffff8000000

def z1135 : W := mkw 0x0206220d068b0aaa 0x4010311068345855 0x67ffe23f1f8f0fff 0xfb3fff11f8fc787f

def z1136 : W := mkw 0x3f6f2b0c6fc9283f 0x41fb7958637e4941 0x3e4e2c186f813070 0x21f27160c37c0983

def z1137 : W := mkw 0x3deb4900fdec201d 0x01ef5a4807ef6100 0x3fffcc00fffe301b 0xf9fffe6007fff180

def z1138 : W := mkw 0x3deb4410fdec105c 0x81ef5a2087ef6082 0xfffffc18fffff07f 0xffffffe0c7ffff83

def z1139 : W := mkw 0x4090d4f39036d7c0 0xa20486a79c81b6be 0xc1b1d3ff907ecfef 0xde0d8e9ffc83f67f

def z1140 : W := mkw 0x970dab8e4a012803 0x04b86d5c72500940 0x3f8fefc76e013012 0xa1fc7f7e3b700980

def z1141 : W := mkw 0x1d69808200000000 0x00eb4c0410000000 0x3fffc3c700000003 0xf1fffe1e38000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z10,z5,z6]),(0,[z11,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z12,z8,z5,z6])],[(0,[z1,z2,z3,z13,z8,z5,z14]),(1,[z1,z3,z8,z5,z15,z9]),(0,[z1,z2,z3,z16,z8,z5,z6])],[(0,[z17,z1,z2,z3,z8,z5,z6]),(0,[z18,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z19,z6]),(0,[z20,z1,z21,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z22,z5,z6]),(0,[z23,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z24,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z25,z5,z6]),(0,[z26,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z27,z8,z5,z6]),(0,[z1,z2,z3,z28,z5,z6,z29]),(0,[z1,z2,z3,z8,z30,z5,z6])],[(0,[z31,z1,z2,z3,z8,z5,z6]),(1,[z32,z2,z3,z8,z5,z6]),(0,[z33,z1,z2,z3,z8,z5,z6]),(0,[z1,z34,z2,z3,z8,z5,z6]),(0,[z35,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z36,z3,z8,z5,z6])],[(0,[z1,z2,z3,z37,z8,z5,z6]),(0,[z1,z2,z38,z39,z8,z5,z6]),(0,[z1,z2,z3,z8,z40,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z41])],[(1,[z1,z2,z42,z8,z5,z6]),(0,[z43,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z44,z13,z8,z5,z6]),(0,[z1,z2,z3,z45,z46,z5,z6]),(1,[z1,z2,z3,z8,z5,z47]),(0,[z1,z2,z3,z8,z15,z48,z6]),(0,[z1,z2,z3,z8,z49,z15,z6]),(0,[z1,z2,z3,z8,z49,z5,z9]),(0,[z1,z2,z3,z8,z5,z50,z6]),(0,[z51,z1,z2,z3,z52,z5,z6]),(0,[z1,z53,z2,z3,z8,z5,z6]),(0,[z1,z54,z2,z3,z8,z5,z6]),(0,[z55,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z56]),(0,[z1,z2,z3,z8,z5,z57,z6]),(0,[z1,z3,z8,z5,z15,z6,z9]),(0,[z1,z2,z58,z3,z8,z5,z14]),(0,[z1,z2,z3,z59,z8,z5,z6])],[(0,[z60,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z61]),(0,[z1,z2,z3,z62,z8,z5,z6]),(0,[z20,z1,z2,z38,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z9]),(0,[z1,z2,z3,z63,z8,z5,z64]),(0,[z1,z2,z65,z3,z8,z5,z6])],[(0,[z66,z17,z2,z3,z8,z5,z6]),(0,[z1,z2,z67,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z69]),(0,[z70,z1,z2,z3,z8,z5,z6]),(0,[z71,z1,z2,z3,z8,z5,z6]),(0,[z72,z1,z3,z8,z5,z14,z6])],[(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z73,z1,z2,z3,z8,z5,z6]),(0,[z74,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z6])],[(1,[z1,z2,z3,z76,z5,z6]),(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z2,z3,z77,z8,z5,z6])],[(0,[z1,z2,z78,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z79,z6]),(0,[z80,z1,z2,z3,z8,z15,z6]),(0,[z80,z1,z2,z3,z8,z5,z9])],[(0,[z1,z2,z3,z81,z8,z5,z6]),(0,[z17,z1,z82,z3,z8,z5,z6]),(0,[z1,z2,z83,z3,z8,z5,z6]),(0,[z1,z34,z3,z8,z84,z5,z6]),(0,[z1,z2,z85,z3,z8,z5,z6]),(0,[z86,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z87]),(0,[z1,z2,z3,z8,z5,z88,z6])],[(0,[z89,z1,z2,z3,z8,z5,z90])],[(0,[z91,z92,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z93]),(0,[z1,z94,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z95,z8,z5,z6]),(0,[z96,z1,z2,z3,z52,z5,z6]),(0,[z1,z97,z2,z3,z8,z5,z6])],[(0,[z1,z98,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z99,z5,z6]),(0,[z1,z100,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z101]),(0,[z1,z2,z3,z8,z5,z9,z29]),(0,[z1,z2,z3,z8,z102,z5,z6])],[(0,[z103,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z104,z5,z6]),(0,[z1,z2,z3,z8,z5,z105,z6]),(0,[z106,z1,z2,z3,z8,z5,z9]),(1,[z1,z34,z3,z8,z5,z9]),(1,[z1,z2,z58,z8,z5,z107])],[(0,[z1,z2,z3,z8,z5,z6,z108]),(0,[z1,z2,z3,z109,z8,z5,z9])],[(0,[z1,z2,z3,z8,z5,z110,z6]),(0,[z1,z2,z3,z8,z5,z6,z111]),(0,[z112,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z113,z6]),(0,[z1,z2,z3,z8,z84,z5,z6]),(0,[z1,z2,z3,z8,z5,z114,z6]),(0,[z115,z1,z2,z3,z8,z48,z6]),(1,[z1,z2,z3,z8,z5,z116])]],
   [[(0,[z1,z2,z3,z8,z117,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z118])],[(0,[z119,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z120,z6])],[(0,[z1,z2,z3,z121,z8,z5,z6]),(0,[z1,z2,z3,z8,z122,z5,z6]),(0,[z1,z123,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z14,z107])],[(0,[z1,z2,z3,z8,z5,z124,z6]),(0,[z1,z2,z3,z8,z5,z6,z125]),(0,[z126,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z38,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z6,z127])],[(1,[z1,z2,z3,z8,z5,z128]),(1,[z26,z2,z39,z8,z5,z6]),(0,[z129,z1,z2,z3,z8,z5,z6]),(0,[z66,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z44,z3,z130,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z131]),(0,[z1,z2,z3,z8,z5,z132,z6]),(0,[z1,z2,z133,z3,z8,z5,z14]),(0,[z1,z2,z3,z134,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z136,z6])],[(0,[z137,z1,z2,z3,z76,z5,z6]),(0,[z138,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z139,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z140,z5,z6]),(0,[z141,z1,z2,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z142,z5,z6]),(0,[z1,z2,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z45,z143,z5,z6])],[(0,[z144,z1,z2,z3,z8,z5,z6]),(0,[z1,z34,z2,z3,z145,z5,z6]),(0,[z1,z2,z3,z8,z5,z146,z6]),(0,[z1,z2,z3,z8,z5,z48,z6]),(0,[z1,z2,z3,z147,z8,z5,z6])],[(0,[z1,z2,z3,z148,z8,z5,z6]),(0,[z1,z149,z2,z3,z8,z5,z6]),(0,[z1,z2,z44,z3,z8,z5,z14])]],
   [[(0,[z1,z2,z39,z8,z5,z6,z107]),(0,[z1,z2,z3,z8,z5,z6,z150]),(0,[z1,z2,z151,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z132]),(0,[z1,z2,z3,z8,z45,z5,z9]),(0,[z115,z1,z2,z3,z8,z5,z14]),(0,[z152,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z153,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z154])],[(0,[z1,z155,z3,z8,z5,z6,z9])],[(0,[z1,z2,z3,z8,z156,z5,z9]),(0,[z1,z2,z157,z3,z8,z5,z6]),(0,[z72,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z158,z3,z8,z5,z6])],[(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z159,z1,z2,z3,z8,z5,z6])],[(0,[z160,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z69,z107]),(1,[z20,z1,z13,z8,z5,z6]),(0,[z1,z2,z3,z8,z161,z5,z6]),(0,[z1,z2,z58,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z162,z6]),(1,[z1,z163,z3,z8,z5,z6])],[(0,[z66,z2,z164,z3,z8,z5,z6]),(0,[z1,z2,z3,z165,z8,z5,z6]),(0,[z1,z2,z3,z166,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z167]),(0,[z1,z2,z3,z168,z8,z5,z6]),(0,[z169,z1,z2,z3,z8,z5,z6])],[(1,[z137,z164,z3,z8,z5,z6]),(0,[z170,z1,z2,z3,z8,z5,z6]),(0,[z171,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z106,z1,z3,z172,z8,z5,z6]),(0,[z7,z1,z2,z3,z172,z5,z6]),(0,[z1,z2,z3,z8,z5,z173,z6])],[(1,[z1,z2,z174,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z175,z6]),(0,[z18,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z176,z3,z8,z5,z6]),(0,[z1,z2,z3,z177,z8,z5,z6])],[(0,[z2,z3,z178,z8,z46,z5,z6]),(0,[z72,z1,z34,z3,z8,z5,z6]),(0,[z1,z2,z179,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z180,z6]),(0,[z1,z2,z3,z8,z5,z181,z6]),(0,[z1,z2,z3,z182,z8,z5,z6])],[(0,[z26,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z183,z6]),(1,[z23,z1,z2,z8,z5,z68])],[(0,[z1,z2,z3,z8,z184,z5,z6]),(0,[z1,z185,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z186,z8,z5,z6]),(0,[z187,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z64,z9]),(0,[z1,z2,z3,z188,z8,z5,z6])],[(0,[z1,z2,z3,z39,z8,z5,z9]),(0,[z1,z189,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z190])],[(1,[z1,z2,z191,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z192]),(0,[z193,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z5,z68]),(0,[z1,z2,z194,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z136,z6,z41])],[(0,[z1,z2,z3,z8,z195,z5,z6]),(1,[z91,z2,z3,z8,z196,z6]),(0,[z197,z1,z2,z3,z5,z196,z6]),(0,[z1,z2,z3,z28,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z198,z6]),(0,[z1,z2,z3,z168,z8,z5,z29])]],
   [[(0,[z1,z82,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z199,z9]),(0,[z1,z2,z3,z8,z5,z14,z200]),(0,[z1,z2,z3,z147,z143,z5,z6])],[(1,[z1,z2,z3,z8,z5,z201]),(0,[z1,z2,z3,z8,z5,z202,z6])],[(0,[z203,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z204,z6]),(0,[z1,z205,z2,z3,z8,z5,z132]),(0,[z1,z2,z3,z206,z8,z5,z6]),(0,[z207,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z208,z6])],[(0,[z1,z209,z2,z3,z8,z5,z6]),(0,[z1,z2,z210,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z211,z5,z6]),(0,[z212,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z213,z6]),(0,[z1,z2,z3,z8,z5,z214,z6]),(0,[z1,z2,z3,z8,z215,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(0,[z1,z34,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z8,z5,z136,z6])],[(0,[z1,z2,z3,z8,z5,z216,z6]),(0,[z1,z2,z3,z8,z5,z69,z9]),(0,[z1,z2,z3,z8,z5,z6,z217]),(0,[z218,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z219,z64])],[(0,[z220,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z221,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z131]),(0,[z1,z2,z3,z8,z5,z222,z6]),(0,[z1,z2,z3,z8,z5,z223,z6])],[(0,[z1,z2,z44,z3,z224,z5,z6]),(0,[z1,z2,z3,z8,z5,z225,z6]),(0,[z1,z2,z3,z147,z4,z5,z6]),(0,[z1,z2,z3,z226,z8,z5,z6])]],
   [[(0,[z106,z1,z2,z3,z8,z227,z6]),(0,[z1,z2,z3,z8,z143,z5,z9]),(0,[z1,z2,z133,z3,z8,z5,z6])],[(0,[z137,z1,z2,z174,z8,z5,z6]),(0,[z228,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z229,z5,z6]),(0,[z1,z2,z3,z28,z8,z5,z29])],[(0,[z0,z1,z2,z3,z52,z5,z6]),(0,[z1,z2,z3,z8,z230,z5,z6]),(1,[z1,z2,z3,z8,z231,z6]),(0,[z232,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z14,z136]),(0,[z1,z2,z233,z3,z8,z5,z6]),(0,[z1,z234,z2,z3,z8,z5,z6])],[(0,[z2,z44,z3,z39,z8,z5,z6]),(0,[z1,z38,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z235,z8,z5,z6]),(0,[z1,z2,z236,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z102,z5,z14])],[(0,[z1,z2,z237,z3,z8,z5,z6]),(0,[z1,z238,z2,z3,z8,z5,z6]),(0,[z115,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z239,z3,z8,z48,z6])],[(0,[z240,z1,z2,z3,z8,z5,z6]),(0,[z241,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z147,z8,z84,z6]),(0,[z1,z242,z2,z3,z8,z5,z6]),(0,[z243,z1,z2,z3,z8,z5,z6])],[(0,[z7,z1,z2,z3,z45,z5,z6]),(0,[z1,z34,z2,z3,z8,z5,z93])],[(0,[z1,z2,z3,z8,z244,z5,z6]),(0,[z1,z2,z3,z245,z8,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z9]),(0,[z1,z2,z3,z246,z8,z5,z6]),(0,[z1,z2,z3,z8,z247,z5,z6]),(0,[z51,z1,z2,z239,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z248])]],
   [[(0,[z115,z1,z2,z3,z249,z5,z6]),(0,[z1,z2,z3,z250,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z251,z6]),(0,[z1,z2,z3,z8,z5,z6,z252])],[(0,[z253,z1,z2,z3,z8,z5,z6]),(0,[z160,z1,z2,z3,z8,z5,z6]),(1,[z51,z1,z2,z52,z5,z6]),(0,[z1,z2,z3,z8,z5,z254,z6]),(0,[z1,z2,z3,z8,z5,z255,z6])],[(0,[z256,z1,z2,z3,z8,z5,z6]),(0,[z1,z205,z3,z8,z45,z5,z6]),(0,[z1,z2,z3,z257,z8,z5,z6]),(0,[z1,z2,z3,z258,z8,z5,z6]),(0,[z1,z2,z3,z168,z8,z5,z120])],[(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z1,z2,z3,z8,z5,z259,z6]),(0,[z1,z2,z3,z8,z5,z260,z6]),(0,[z1,z2,z3,z8,z261,z5,z6]),(0,[z1,z2,z262,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z263,z5,z6])],[(0,[z1,z2,z3,z8,z5,z264,z6]),(0,[z1,z2,z3,z8,z5,z265,z6]),(0,[z66,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z84,z156,z6]),(0,[z7,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z219])],[(0,[z92,z2,z3,z8,z156,z5,z6]),(1,[z1,z2,z3,z142,z5,z6]),(1,[z1,z2,z3,z8,z5,z266]),(1,[z106,z1,z3,z172,z5,z6]),(0,[z80,z1,z3,z8,z5,z15,z6]),(0,[z1,z2,z3,z8,z5,z48,z14]),(0,[z1,z2,z239,z3,z8,z5,z14]),(0,[z1,z2,z3,z147,z8,z5,z14])],[(0,[z160,z1,z2,z3,z8,z5,z69]),(0,[z1,z21,z38,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z267]),(0,[z268,z1,z2,z3,z8,z5,z6])],[(0,[z26,z1,z2,z3,z8,z5,z6]),(0,[z269,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z270,z2,z3,z8,z5,z6]),(0,[z1,z82,z2,z3,z8,z5,z271]),(0,[z1,z2,z3,z8,z272,z5,z6]),(0,[z273,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z84,z5,z15,z6])],[(0,[z23,z1,z2,z3,z8,z5,z68]),(0,[z274,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z128,z6]),(0,[z1,z2,z275,z3,z8,z5,z6]),(0,[z89,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z276,z5,z6]),(0,[z72,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z133,z3,z143,z5,z6]),(0,[z1,z2,z3,z277,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z278]),(0,[z7,z1,z2,z3,z5,z64,z6])],[(0,[z1,z2,z3,z8,z46,z5,z14]),(0,[z1,z2,z58,z3,z8,z5,z107]),(0,[z1,z2,z3,z147,z8,z64,z6]),(0,[z1,z2,z3,z8,z5,z279,z6])],[(0,[z1,z2,z280,z3,z8,z5,z6]),(0,[z86,z160,z1,z2,z3,z8,z5]),(0,[z80,z1,z2,z3,z8,z5,z281]),(0,[z1,z282,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z283,z5,z6]),(0,[z1,z2,z3,z28,z8,z5,z120])],[(1,[z17,z82,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z284,z6]),(0,[z1,z2,z3,z168,z8,z5,z14]),(0,[z115,z1,z2,z8,z5,z48,z6]),(0,[z1,z2,z3,z8,z5,z285,z6]),(0,[z1,z2,z3,z8,z5,z116,z6])],[(0,[z207,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z168,z8,z135,z5])],[(0,[z20,z1,z2,z3,z8,z286,z6]),(0,[z1,z2,z3,z8,z5,z287,z6]),(1,[z1,z2,z3,z147,z4,z6])]],
   [[(0,[z137,z17,z2,z3,z8,z5,z6]),(0,[z1,z2,z288,z3,z8,z5,z6]),(0,[z1,z2,z289,z3,z8,z5,z6])],[(0,[z1,z2,z290,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z8,z5,z14]),(1,[z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z6,z291])],[(0,[z1,z2,z3,z8,z135,z5,z14]),(0,[z292,z1,z2,z3,z8,z5,z6])],[(0,[z293,z1,z2,z3,z8,z5,z6]),(0,[z294,z1,z2,z3,z8,z5,z6]),(0,[z295,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z296,z9]),(0,[z1,z2,z3,z188,z8,z5,z14])],[(0,[z1,z2,z3,z172,z8,z5,z9]),(0,[z72,z1,z155,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z64,z14]),(0,[z1,z2,z297,z3,z8,z5,z6]),(0,[z298,z1,z2,z3,z8,z5,z6])],[(0,[z86,z1,z2,z3,z8,z5,z136])],[(0,[z1,z2,z3,z299,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z281,z6]),(0,[z1,z2,z3,z8,z5,z14,z300]),(0,[z1,z2,z3,z5,z120,z6,z29])],[(0,[z1,z2,z3,z8,z301,z5,z6]),(0,[z91,z1,z2,z3,z8,z196,z6]),(0,[z91,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z302,z6])]],
   [[(0,[z1,z2,z3,z8,z303,z5,z6]),(0,[z1,z2,z3,z8,z5,z304,z6])],[(0,[z305,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z306,z8,z5,z6]),(0,[z106,z1,z2,z3,z8,z5,z6]),(0,[z80,z1,z34,z3,z8,z5,z6])],[(0,[z137,z1,z2,z42,z8,z5,z6]),(0,[z1,z32,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z307,z5,z6])],[(0,[z1,z2,z3,z308,z8,z5,z6]),(0,[z1,z2,z3,z5,z309,z196,z6]),(0,[z1,z2,z3,z8,z5,z310,z6]),(1,[z1,z2,z3,z63,z8,z5]),(0,[z1,z2,z3,z8,z311,z5,z6])],[(0,[z1,z2,z3,z8,z5,z14,z90]),(0,[z1,z2,z3,z8,z5,z312,z6]),(0,[z1,z2,z3,z8,z5,z313,z6]),(0,[z1,z2,z3,z8,z5,z314,z6])],[(0,[z1,z315,z2,z3,z8,z5,z6]),(0,[z316,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z317,z6])],[(0,[z318,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z319,z6]),(0,[z1,z2,z320,z3,z8,z5,z6]),(0,[z1,z321,z2,z3,z8,z5,z6]),(0,[z1,z2,z322,z3,z8,z5,z6])]],
   [[(0,[z82,z2,z164,z3,z8,z5,z6]),(0,[z66,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z323,z6]),(0,[z96,z7,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z9]),(0,[z1,z185,z2,z3,z8,z5,z196]),(0,[z1,z21,z2,z3,z8,z5,z266]),(0,[z1,z2,z3,z8,z5,z6,z324]),(0,[z1,z2,z3,z8,z143,z5,z14]),(0,[z1,z325,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z168,z5,z120])],[(0,[z137,z1,z2,z3,z8,z5,z9]),(0,[z1,z326,z2,z3,z8,z5,z6]),(0,[z1,z2,z239,z3,z8,z5,z6])],[(0,[z327,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z328,z6]),(0,[z329,z1,z2,z3,z8,z5,z6]),(0,[z51,z1,z2,z52,z8,z5,z6]),(0,[z7,z1,z2,z176,z8,z5,z6]),(1,[z7,z1,z2,z3,z64,z6])],[(0,[z1,z2,z3,z8,z5,z6,z330]),(0,[z1,z331,z2,z3,z8,z5,z6]),(0,[z1,z205,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z227,z5,z6]),(0,[z7,z1,z2,z3,z8,z84,z6])],[(0,[z1,z2,z3,z332,z8,z5,z6]),(0,[z1,z2,z3,z333,z8,z5,z6]),(0,[z1,z334,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z45,z5,z6]),(0,[z1,z2,z3,z335,z8,z5,z6]),(0,[z1,z2,z3,z336,z8,z5,z6]),(0,[z1,z2,z3,z8,z337,z5,z6])],[(1,[z96,z2,z3,z46,z5,z6]),(0,[z338,z1,z2,z3,z8,z5,z6]),(0,[z1,z155,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z28,z168,z5,z6]),(0,[z1,z2,z339,z3,z8,z5,z6])],[(0,[z89,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z340,z9])],[(0,[z1,z2,z3,z8,z46,z5,z6]),(0,[z1,z2,z3,z8,z156,z5,z6]),(0,[z20,z1,z2,z3,z8,z5,z192]),(0,[z1,z2,z3,z8,z4,z5,z14]),(0,[z1,z2,z3,z8,z5,z6,z341])]],
   [[(0,[z1,z2,z3,z342,z8,z5,z6]),(0,[z1,z343,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z271]),(0,[z160,z1,z2,z3,z8,z135,z5]),(0,[z1,z2,z3,z8,z5,z14,z41]),(0,[z86,z1,z2,z3,z168,z8,z5])],[(0,[z344,z1,z2,z3,z8,z5,z6]),(0,[z345,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z346,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z347,z5,z6]),(0,[z1,z2,z3,z8,z5,z348,z6]),(0,[z1,z2,z3,z349,z8,z5,z6]),(0,[z350,z1,z2,z3,z8,z5,z6])],[(0,[z137,z2,z164,z3,z8,z5,z6]),(0,[z89,z1,z2,z3,z8,z5,z69]),(0,[z1,z2,z3,z8,z49,z84,z6]),(1,[z72,z1,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z265,z14]),(0,[z7,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z351,z8,z5,z6]),(0,[z1,z2,z3,z8,z352,z5,z6])],[(0,[z2,z3,z8,z5,z69,z6,z90]),(0,[z1,z21,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z353,z6]),(0,[z1,z2,z3,z8,z354,z5,z6])],[(0,[z1,z2,z164,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z6,z355]),(0,[z66,z2,z44,z3,z8,z5,z6]),(0,[z1,z2,z3,z224,z8,z5,z6]),(0,[z1,z2,z3,z178,z8,z5,z9]),(0,[z20,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z356]),(0,[z1,z2,z3,z8,z5,z14,z9]),(0,[z23,z1,z2,z3,z8,z5,z14])],[(0,[z1,z2,z3,z8,z5,z68,z90]),(0,[z357,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z5,z6]),(0,[z1,z2,z3,z8,z358,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z359]),(0,[z1,z2,z3,z360,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z5,z6])],[(0,[z1,z361,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z64,z6]),(0,[z1,z2,z3,z362,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z87]),(0,[z1,z2,z363,z3,z8,z5,z6]),(0,[z1,z2,z3,z364,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z90,z107]),(0,[z80,z1,z2,z3,z8,z84,z6]),(0,[z51,z1,z2,z3,z8,z5,z9]),(0,[z7,z1,z2,z3,z8,z64,z6])],[(0,[z1,z2,z3,z8,z5,z6,z365]),(0,[z1,z21,z2,z3,z8,z5,z101]),(0,[z366,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z58,z8,z5,z6,z107])],[(0,[z1,z2,z3,z367,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z368]),(0,[z1,z2,z3,z8,z49,z5,z14]),(0,[z1,z2,z3,z8,z5,z369,z14]),(0,[z1,z2,z3,z28,z8,z5,z6])],[(0,[z1,z2,z370,z3,z8,z5,z6]),(0,[z1,z2,z371,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z227,z6]),(0,[z1,z2,z3,z8,z5,z199,z6])],[(1,[z1,z2,z3,z8,z5,z372]),(0,[z1,z2,z373,z3,z8,z5,z6]),(0,[z374,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z375]),(0,[z376,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z377]),(0,[z86,z1,z2,z3,z8,z6,z41])],[(0,[z1,z2,z3,z8,z378,z5,z6]),(0,[z379,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z52,z8,z5,z9])],[(1,[z1,z2,z3,z8,z286,z6]),(0,[z1,z2,z8,z143,z5,z48,z6]),(0,[z1,z2,z3,z380,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z381]),(0,[z1,z2,z3,z8,z5,z196,z9]),(0,[z1,z2,z3,z8,z5,z382,z6]),(0,[z1,z2,z3,z8,z5,z15,z9]),(1,[z1,z34,z3,z8,z84,z6]),(0,[z1,z2,z3,z8,z383,z5,z6]),(0,[z86,z1,z2,z3,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z384,z6])],[(0,[z385,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z386,z8,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z14]),(1,[z1,z2,z3,z8,z5,z14]),(1,[z1,z2,z133,z143,z5,z6]),(0,[z387,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z388,z8,z5,z6])],[(0,[z1,z2,z3,z8,z389,z5,z6]),(0,[z17,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z390,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z391,z6])],[(0,[z96,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z143,z5,z6])],[(1,[z197,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z392,z5,z6]),(0,[z20,z1,z2,z13,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z393]),(1,[z80,z1,z3,z8,z15,z6]),(0,[z1,z34,z2,z3,z8,z15,z6]),(0,[z1,z34,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z219,z6]),(0,[z1,z2,z3,z8,z5,z394,z6])],[(0,[z20,z1,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z395,z8,z5,z6]),(0,[z396,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z397,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z9]),(0,[z1,z2,z3,z8,z398,z5,z6]),(0,[z399,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z26,z1,z2,z3,z8,z5,z355]),(0,[z20,z400,z2,z3,z8,z5,z6]),(0,[z106,z1,z2,z3,z172,z5,z6]),(0,[z106,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z6,z401])],[(0,[z402,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z403,z6]),(0,[z1,z155,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z50,z9]),(0,[z1,z2,z3,z8,z5,z404,z6]),(0,[z1,z2,z405,z3,z8,z5,z6])],[(1,[z1,z155,z3,z8,z5,z9]),(0,[z1,z2,z406,z3,z8,z5,z6])],[(0,[z66,z26,z2,z3,z8,z5,z6]),(0,[z407,z1,z2,z3,z8,z5,z6]),(0,[z408,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z167]),(0,[z409,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z6])],[(0,[z410,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z145,z5,z6]),(0,[z70,z1,z2,z3,z8,z5,z9]),(0,[z7,z1,z2,z3,z147,z5,z6]),(0,[z86,z1,z2,z3,z8,z5,z41])],[(0,[z137,z1,z2,z3,z8,z5,z372]),(0,[z92,z1,z2,z3,z8,z196,z6]),(0,[z92,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z411,z8,z5,z6]),(0,[z1,z2,z3,z412,z8,z5,z6])],[(0,[z1,z2,z38,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z413,z6])],[(0,[z1,z2,z3,z414,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z356]),(0,[z51,z1,z2,z133,z8,z5,z6]),(0,[z1,z2,z3,z415,z8,z5,z6])]],
   [[(0,[z17,z2,z3,z39,z8,z5,z6]),(0,[z1,z416,z2,z3,z8,z5,z6]),(0,[z1,z2,z44,z8,z5,z6,z107]),(1,[z1,z2,z3,z8,z392,z5]),(0,[z86,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z417,z8,z5,z6])],[(0,[z2,z3,z8,z156,z5,z196,z6]),(0,[z418,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z419,z8,z5,z6]),(0,[z420,z1,z2,z3,z8,z5,z14]),(0,[z421,z1,z2,z3,z8,z5,z6]),(0,[z23,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z422,z3,z8,z5,z6]),(0,[z1,z2,z423,z3,z8,z5,z6]),(0,[z424,z1,z2,z3,z8,z5,z6]),(0,[z1,z425,z2,z3,z8,z5,z6])],[(0,[z17,z82,z2,z3,z8,z5,z6]),(0,[z426,z1,z2,z3,z8,z5,z6]),(0,[z1,z205,z2,z3,z172,z5,z6]),(0,[z1,z2,z3,z8,z45,z5,z14]),(0,[z1,z2,z133,z3,z52,z5,z6]),(0,[z427,z1,z2,z3,z8,z5,z6])],[(0,[z428,z1,z2,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z8,z328,z6]),(0,[z429,z1,z2,z3,z8,z5,z6]),(0,[z115,z1,z2,z3,z417,z5,z6]),(0,[z1,z2,z3,z8,z5,z430,z6])],[(0,[z137,z1,z164,z3,z8,z5,z6]),(0,[z160,z1,z2,z306,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z431,z6]),(0,[z1,z2,z239,z8,z143,z5,z6])],[(0,[z432,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z130,z5,z6]),(0,[z1,z433,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z156,z5,z14]),(0,[z89,z1,z2,z3,z8,z135,z5]),(0,[z1,z2,z3,z8,z434,z5,z6]),(0,[z1,z435,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z25,z6]),(0,[z436,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z192]),(0,[z437,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z281]),(0,[z1,z2,z3,z8,z5,z369,z6]),(0,[z1,z2,z3,z8,z5,z438,z6]),(0,[z1,z2,z3,z8,z49,z5,z6])]],
   [[(0,[z439,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z440,z8,z5,z6]),(0,[z1,z2,z3,z8,z84,z196,z6]),(0,[z1,z21,z2,z38,z8,z5,z6]),(0,[z1,z2,z3,z8,z84,z5,z9])],[(0,[z1,z441,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z442])],[(0,[z1,z2,z3,z8,z443,z5,z6]),(0,[z1,z2,z3,z8,z5,z120,z9]),(0,[z1,z2,z3,z8,z5,z6,z444]),(0,[z1,z2,z3,z8,z445,z5,z6])],[(0,[z1,z82,z2,z3,z8,z5,z87]),(0,[z1,z2,z3,z8,z446,z5,z6]),(0,[z1,z2,z3,z447,z8,z5,z6]),(1,[z1,z65,z3,z8,z5,z6])],[],[(1,[z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z44,z38,z8,z5,z6]),(0,[z1,z2,z3,z172,z46,z5,z6]),(0,[z1,z2,z3,z8,z448,z5,z6]),(0,[z80,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z63,z8,z5,z6]),(0,[z86,z1,z2,z3,z28,z8,z5])],[(1,[z1,z2,z3,z8,z264,z6]),(0,[z106,z1,z2,z3,z45,z5,z6]),(0,[z1,z2,z3,z8,z5,z14,z449]),(0,[z1,z2,z3,z8,z5,z6,z300]),(0,[z1,z2,z3,z8,z5,z450,z6])],[(0,[z1,z2,z3,z147,z8,z15,z6]),(0,[z1,z451,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z39,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z452,z6]),(0,[z1,z2,z3,z172,z8,z5,z6]),(0,[z1,z2,z453,z3,z8,z5,z6]),(0,[z1,z2,z3,z147,z8,z4,z6]),(0,[z1,z2,z3,z8,z5,z454,z6])],[(0,[z1,z455,z2,z3,z8,z5,z6]),(0,[z51,z1,z2,z3,z8,z5,z14]),(1,[z1,z2,z3,z249,z5,z6]),(0,[z1,z2,z3,z8,z5,z456,z6]),(0,[z457,z1,z2,z3,z8,z5,z6])],[(0,[z197,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z28,z8,z5,z14])],[(0,[z1,z82,z2,z3,z8,z5,z14]),(0,[z458,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z68,z6,z107]),(0,[z1,z2,z3,z28,z8,z135,z5])],[(0,[z1,z2,z3,z8,z5,z459,z6]),(0,[z1,z2,z3,z8,z5,z460,z6]),(0,[z1,z2,z3,z461,z8,z5,z6]),(0,[z1,z2,z3,z462,z8,z5,z6])],[(0,[z1,z463,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z464,z6]),(0,[z1,z2,z3,z109,z8,z5,z6]),(0,[z1,z2,z3,z8,z465,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z107]),(0,[z1,z2,z3,z466,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z467]),(0,[z1,z2,z3,z8,z5,z6,z468])],[(0,[z1,z2,z58,z3,z8,z5,z9]),(0,[z1,z2,z3,z469,z8,z5,z6]),(0,[z1,z2,z3,z143,z5,z64,z6])],[(0,[z137,z1,z2,z3,z8,z25,z6]),(0,[z470,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z172,z178,z5,z6]),(1,[z160,z2,z3,z8,z5,z90]),(0,[z471,z1,z2,z3,z8,z5,z6]),(0,[z1,z472,z2,z3,z8,z5,z6]),(0,[z86,z1,z163,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z39,z13,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z15,z14]),(0,[z218,z1,z2,z3,z8,z5,z14]),(0,[z473,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z239,z8,z49,z5,z6]),(0,[z23,z1,z2,z58,z8,z5,z6])],[(0,[z0,z1,z2,z3,z46,z5,z6]),(0,[z1,z2,z3,z474,z8,z5,z6]),(0,[z1,z2,z3,z8,z475,z5,z6]),(0,[z20,z1,z2,z3,z8,z5,z476]),(0,[z1,z2,z3,z477,z8,z5,z6]),(0,[z1,z3,z8,z5,z14,z6,z9]),(0,[z1,z2,z3,z8,z5,z6,z478])],[(0,[z2,z164,z3,z39,z8,z5,z6]),(0,[z1,z2,z38,z3,z8,z5,z6])],[(0,[z479,z1,z2,z3,z8,z5,z6]),(0,[z106,z1,z205,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z480,z5,z6]),(0,[z1,z2,z481,z3,z8,z5,z14]),(0,[z482,z1,z2,z3,z8,z5,z6]),(0,[z483,z1,z2,z3,z8,z5,z6])],[(0,[z96,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z484,z5,z9])],[(0,[z137,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z309,z6]),(0,[z485,z1,z2,z3,z8,z5,z6]),(0,[z1,z34,z3,z8,z5,z6,z9]),(0,[z420,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z486,z8,z5,z6]),(1,[z86,z1,z2,z3,z8,z41]),(0,[z1,z2,z3,z8,z5,z6,z487])],[(0,[z1,z2,z3,z8,z5,z488,z6]),(0,[z1,z2,z3,z489,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z490,z6]),(0,[z1,z2,z491,z3,z8,z5,z6])],[(0,[z17,z1,z164,z3,z8,z5,z6]),(0,[z492,z1,z2,z3,z8,z5,z6]),(0,[z1,z205,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z47]),(0,[z1,z2,z133,z8,z143,z5,z6]),(0,[z1,z493,z2,z3,z8,z5,z6])]],
   [[(1,[z400,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z494,z6])],[(0,[z495,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z496,z5,z6]),(0,[z1,z2,z3,z8,z5,z497,z6])],[(0,[z1,z2,z3,z8,z5,z498,z6]),(0,[z1,z2,z3,z172,z143,z5,z6]),(0,[z1,z2,z3,z8,z5,z499,z6]),(0,[z1,z2,z3,z8,z500,z5,z6])],[(0,[z1,z2,z3,z501,z8,z5,z6]),(0,[z502,z1,z2,z3,z8,z5,z6]),(0,[z26,z1,z2,z39,z8,z5,z6]),(0,[z1,z2,z3,z503,z8,z5,z6])],[(0,[z1,z504,z2,z3,z8,z5,z6]),(0,[z505,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z506,z6]),(0,[z0,z2,z3,z178,z8,z5,z6]),(0,[z1,z2,z3,z507,z8,z5,z6]),(0,[z1,z2,z508,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z509]),(0,[z1,z2,z3,z8,z5,z6,z9]),(0,[z1,z2,z3,z8,z5,z136,z9]),(0,[z1,z2,z510,z3,z8,z5,z6]),(0,[z1,z2,z511,z3,z8,z5,z6])],[(0,[z1,z2,z3,z512,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z513,z6]),(0,[z1,z514,z2,z3,z8,z5,z6]),(0,[z7,z1,z2,z380,z8,z5,z6]),(0,[z515,z1,z2,z3,z8,z5,z6]),(0,[z516,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z517,z3,z8,z5,z6]),(0,[z91,z2,z3,z8,z5,z196,z6]),(1,[z1,z2,z3,z145,z5,z6]),(0,[z1,z2,z3,z8,z5,z518,z6]),(0,[z23,z1,z2,z3,z8,z5,z107])]],
   [[(0,[z519,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z520,z8,z5,z6]),(0,[z1,z2,z521,z3,z8,z5,z6]),(0,[z1,z522,z2,z3,z8,z5,z6]),(0,[z523,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z164,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z524,z5,z6]),(0,[z525,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z526,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z527]),(0,[z1,z2,z3,z172,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z93])],[(0,[z528,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z52,z8,z143,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z101]),(1,[z1,z2,z176,z8,z5,z6]),(0,[z529,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z39,z8,z5,z6]),(0,[z1,z2,z44,z3,z8,z5,z9]),(1,[z1,z2,z3,z8,z328,z6]),(0,[z1,z2,z3,z8,z5,z431,z14]),(0,[z1,z2,z3,z530,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z5,z136])],[(0,[z1,z531,z2,z3,z8,z5,z6]),(0,[z23,z1,z2,z44,z8,z5,z6]),(0,[z532,z1,z2,z3,z8,z5,z6]),(0,[z115,z1,z2,z3,z8,z5,z9]),(0,[z51,z1,z2,z3,z8,z5,z6])],[(0,[z26,z1,z2,z44,z8,z5,z6]),(0,[z533,z1,z2,z3,z8,z5,z6]),(0,[z534,z1,z2,z3,z8,z5,z6])],[(0,[z1,z82,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z535,z8,z5,z6]),(0,[z1,z2,z3,z536,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z107]),(0,[z1,z2,z3,z8,z537,z5,z6])]],
   [[(0,[z538,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z539,z6]),(0,[z540,z1,z2,z3,z8,z5,z6]),(0,[z541,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z542,z5,z6])],[(1,[z1,z2,z3,z130,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z543]),(0,[z1,z2,z3,z8,z544,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z545])],[(0,[z1,z2,z3,z8,z5,z14,z29]),(0,[z1,z2,z3,z52,z8,z5,z6]),(0,[z546,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z547,z6]),(0,[z1,z2,z3,z8,z5,z548,z6]),(0,[z1,z2,z549,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z550,z6]),(0,[z1,z2,z3,z8,z5,z6,z551])],[(0,[z218,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z69,z6]),(0,[z1,z2,z3,z8,z5,z15,z6]),(0,[z552,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z28,z5,z29]),(0,[z1,z2,z3,z553,z8,z5,z6])],[(0,[z554,z1,z2,z3,z8,z5,z6]),(0,[z96,z1,z2,z3,z46,z5,z6]),(0,[z1,z2,z3,z555,z8,z5,z6]),(0,[z7,z1,z2,z3,z8,z15,z6]),(0,[z1,z2,z3,z8,z5,z6,z556])],[(0,[z7,z1,z2,z3,z8,z4,z6])],[(0,[z1,z2,z481,z3,z8,z5,z6]),(0,[z1,z2,z3,z172,z8,z5,z14]),(1,[z115,z1,z2,z8,z48,z6]),(0,[z1,z2,z239,z3,z8,z5,z444])]],
   [[(0,[z96,z1,z2,z3,z8,z5,z6]),(0,[z1,z21,z2,z13,z8,z5,z6]),(0,[z1,z2,z3,z52,z5,z64,z6])],[(0,[z557,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z558]),(0,[z1,z2,z3,z8,z5,z559,z6]),(0,[z1,z2,z3,z8,z5,z560,z6]),(0,[z1,z2,z561,z3,z8,z5,z6])],[(0,[z1,z2,z3,z42,z8,z5,z6]),(0,[z91,z1,z2,z3,z8,z5,z14]),(1,[z1,z2,z3,z8,z5,z438]),(0,[z562,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z563,z6])],[(0,[z564,z1,z2,z3,z8,z5,z6]),(0,[z1,z565,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z68,z6])],[(0,[z66,z1,z2,z39,z8,z5,z6]),(0,[z1,z566,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z567,z6])],[(0,[z89,z160,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z27,z5,z6]),(0,[z1,z2,z568,z3,z8,z5,z6]),(0,[z1,z569,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z142,z8,z5,z6]),(0,[z51,z1,z2,z8,z5,z48,z6]),(0,[z115,z1,z2,z239,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z570,z6]),(0,[z96,z1,z2,z3,z178,z5,z6]),(1,[z1,z21,z38,z8,z5,z6]),(0,[z51,z1,z2,z3,z143,z5,z6])]],
   [[(0,[z91,z1,z2,z3,z8,z156,z6]),(0,[z1,z2,z2,z3,z8,z5,z9]),(0,[z571,z1,z2,z3,z8,z5,z6]),(0,[z1,z572,z2,z3,z8,z5,z6])],[(0,[z1,z2,z174,z3,z8,z5,z6]),(0,[z92,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z476]),(0,[z1,z2,z3,z8,z5,z201,z6]),(0,[z1,z2,z3,z8,z5,z573,z6])],[(0,[z1,z2,z3,z8,z5,z14,z574]),(0,[z575,z1,z2,z3,z8,z5,z6]),(0,[z86,z1,z65,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z5,z14])],[(0,[z137,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z6,z576]),(1,[z1,z185,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z577,z6]),(0,[z1,z2,z3,z8,z578,z5,z6]),(0,[z1,z2,z3,z8,z286,z5,z6]),(0,[z106,z1,z2,z3,z8,z5,z47]),(0,[z579,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z580]),(0,[z86,z1,z2,z3,z8,z135,z6])],[(0,[z26,z2,z3,z39,z8,z5,z6]),(0,[z1,z2,z3,z581,z8,z5,z6]),(0,[z1,z582,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z355]),(0,[z26,z1,z2,z3,z8,z5,z128]),(0,[z1,z205,z2,z3,z8,z5,z14])],[(0,[z66,z1,z2,z44,z8,z5,z6]),(0,[z583,z1,z2,z3,z8,z5,z6]),(0,[z20,z1,z2,z3,z578,z5,z6]),(0,[z1,z2,z3,z584,z8,z5,z6]),(0,[z1,z2,z3,z8,z585,z5,z6]),(0,[z1,z2,z3,z8,z5,z586,z6]),(0,[z86,z1,z2,z3,z8,z5,z68])]],
   [[(1,[z1,z2,z3,z5,z309,z6])],[(0,[z587,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z372]),(0,[z1,z2,z588,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z589,z5,z6])],[(0,[z96,z1,z2,z3,z143,z5,z6]),(0,[z590,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z591,z6])],[(0,[z592,z1,z2,z3,z8,z5,z6]),(0,[z593,z1,z2,z3,z8,z5,z6]),(0,[z72,z1,z3,z8,z5,z15,z6]),(0,[z1,z2,z3,z8,z5,z200,z6]),(0,[z1,z2,z3,z594,z8,z5,z6])],[(1,[z1,z2,z3,z224,z5,z6]),(1,[z1,z2,z3,z8,z5,z368]),(0,[z80,z1,z2,z3,z8,z5,z368]),(0,[z595,z1,z2,z3,z8,z5,z6]),(0,[z596,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z508,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z597,z6]),(0,[z598,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z599,z8,z5,z6])],[(0,[z1,z2,z3,z8,z600,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z381]),(0,[z1,z2,z3,z8,z5,z513,z14]),(0,[z601,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z168,z5,z120,z6])],[(0,[z1,z2,z3,z8,z196,z15,z6]),(0,[z400,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z602,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z449])],[(0,[z603,z1,z2,z3,z8,z5,z6]),(0,[z1,z604,z2,z3,z8,z5,z6]),(0,[z1,z21,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z605,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z5,z107]),(0,[z1,z163,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z164,z3,z8,z5,z14]),(0,[z1,z2,z3,z178,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z14,z14]),(0,[z606,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z607])],[(1,[z1,z2,z3,z608,z5,z6]),(0,[z1,z2,z3,z8,z609,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z13,z8,z5,z9]),(1,[z1,z205,z3,z45,z5,z6]),(0,[z1,z2,z610,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z611,z6]),(0,[z160,z1,z2,z191,z8,z5,z6]),(0,[z1,z2,z3,z8,z612,z5,z6]),(0,[z1,z2,z3,z8,z5,z48,z9]),(0,[z1,z2,z239,z3,z8,z5,z9]),(0,[z1,z2,z3,z147,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z296,z6])],[(1,[z0,z2,z3,z178,z5,z6]),(1,[z1,z2,z3,z8,z135,z136])],[(0,[z20,z32,z2,z3,z8,z5,z6])],[(0,[z1,z2,z613,z3,z8,z5,z6]),(0,[z1,z614,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z615]),(0,[z1,z2,z239,z3,z8,z49,z6])],[(0,[z91,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z393]),(1,[z1,z2,z239,z8,z49,z6])],[(0,[z1,z2,z3,z616,z8,z5,z6]),(0,[z617,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z90]),(0,[z89,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z618,z8,z5,z6]),(0,[z72,z1,z2,z3,z8,z5,z9])]],
   [[(0,[z619,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z620,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z46,z5,z9]),(0,[z1,z2,z3,z8,z156,z15,z6]),(0,[z1,z2,z621,z3,z8,z5,z6]),(0,[z1,z34,z2,z3,z8,z84,z6]),(0,[z1,z2,z3,z622,z8,z5,z6])],[(1,[z1,z2,z306,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z623,z6]),(0,[z1,z2,z3,z52,z172,z5,z6]),(0,[z1,z2,z624,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z625,z6]),(0,[z1,z2,z3,z52,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z6,z626])],[(0,[z1,z2,z3,z8,z76,z5,z6]),(0,[z627,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z168,z8,z5,z9]),(0,[z1,z2,z3,z628,z8,z5,z6])],[(0,[z629,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z196,z14]),(0,[z1,z2,z3,z8,z630,z5,z6]),(0,[z170,z1,z2,z3,z8,z5,z9]),(0,[z552,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z8,z49,z5,z48,z6]),(0,[z1,z2,z239,z3,z8,z5,z116]),(0,[z1,z2,z3,z8,z135,z5,z41])],[(0,[z1,z205,z2,z3,z45,z5,z6]),(0,[z1,z631,z2,z3,z8,z5,z6]),(0,[z632,z1,z2,z3,z8,z5,z6])],[(0,[z633,z1,z2,z3,z8,z5,z6]),(0,[z634,z1,z2,z3,z8,z5,z6]),(0,[z635,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z417,z5,z6]),(0,[z1,z2,z58,z3,z8,z5,z68])],[(0,[z17,z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z636,z3,z8,z5,z6]),(0,[z1,z2,z637,z3,z8,z5,z6]),(0,[z89,z86,z1,z2,z3,z8,z5]),(0,[z20,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z638,z3,z8,z5,z6]),(0,[z1,z2,z179,z3,z8,z5,z9])],[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z639,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z476,z6]),(0,[z1,z2,z3,z8,z135,z5,z9])]],
   [[(1,[z1,z2,z3,z8,z5,z175]),(0,[z1,z2,z3,z8,z5,z231,z6]),(0,[z1,z2,z3,z8,z5,z640,z6]),(0,[z1,z34,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z484,z5,z6]),(0,[z1,z2,z3,z8,z5,z641,z6]),(0,[z1,z2,z3,z8,z5,z642,z6]),(0,[z643,z1,z2,z3,z8,z5,z6])],[(0,[z137,z1,z2,z3,z608,z5,z6]),(0,[z137,z1,z2,z3,z8,z264,z6]),(0,[z1,z2,z3,z8,z644,z5,z6]),(0,[z1,z2,z3,z8,z645,z5,z6]),(0,[z1,z2,z3,z8,z5,z646,z6])],[(0,[z1,z2,z3,z8,z647,z5,z6]),(0,[z1,z2,z648,z3,z8,z5,z6]),(0,[z1,z2,z649,z3,z8,z5,z6]),(0,[z193,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z68,z14]),(0,[z650,z1,z2,z3,z8,z5,z6])],[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z651,z8,z5,z6])],[(0,[z160,z1,z2,z3,z8,z5,z90]),(0,[z1,z2,z3,z8,z5,z574,z6]),(0,[z1,z2,z3,z652,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z41])],[(0,[z1,z653,z2,z3,z8,z5,z6]),(0,[z23,z1,z2,z39,z8,z5,z6]),(0,[z654,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z340,z6])],[(0,[z0,z1,z2,z3,z178,z5,z6]),(0,[z1,z2,z3,z178,z45,z5,z6]),(0,[z1,z34,z2,z3,z8,z5,z438]),(0,[z1,z655,z2,z3,z8,z5,z6])],[(0,[z656,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z657,z5,z6]),(0,[z1,z658,z2,z3,z8,z5,z6]),(0,[z659,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z660,z6]),(0,[z661,z1,z2,z3,z8,z5,z6]),(0,[z1,z662,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z663,z8,z5,z6]),(0,[z664,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z665,z3,z8,z5,z6])]],
   [[(0,[z92,z1,z2,z3,z8,z5,z14]),(0,[z1,z205,z2,z3,z8,z5,z393]),(0,[z1,z2,z2,z3,z8,z5,z14]),(0,[z1,z666,z2,z3,z8,z5,z6]),(0,[z1,z2,z667,z3,z8,z5,z6])],[(0,[z668,z1,z2,z3,z8,z5,z6]),(0,[z1,z669,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z670,z8,z5,z6]),(0,[z160,z2,z3,z8,z5,z6,z90]),(0,[z1,z2,z3,z8,z84,z48,z6]),(0,[z385,z1,z2,z3,z8,z5,z9])],[(0,[z1,z21,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z671,z5,z6]),(0,[z86,z1,z2,z3,z8,z5,z14]),(1,[z1,z2,z3,z8,z5,z444])],[(0,[z1,z2,z3,z178,z8,z5,z6]),(0,[z1,z2,z3,z8,z392,z5,z196]),(0,[z89,z2,z3,z8,z5,z69,z6]),(0,[z672,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z14,z6]),(0,[z1,z2,z133,z3,z8,z5,z9])],[(0,[z137,z1,z82,z3,z8,z5,z6]),(0,[z106,z1,z2,z3,z8,z5,z201]),(0,[z673,z1,z2,z3,z8,z5,z6])],[(1,[z92,z2,z3,z8,z156,z6]),(0,[z92,z1,z2,z3,z8,z156,z6]),(0,[z1,z2,z191,z3,z8,z5,z6]),(0,[z1,z3,z172,z8,z45,z5,z6]),(1,[z1,z3,z8,z5,z14,z9]),(0,[z1,z2,z674,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z675,z6]),(0,[z1,z676,z2,z3,z8,z5,z6])],[(0,[z677,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z678,z8,z5,z6]),(1,[z1,z2,z3,z578,z5,z6]),(0,[z679,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z680,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z681,z5,z6]),(0,[z1,z2,z3,z52,z45,z5,z6]),(0,[z1,z2,z682,z3,z8,z5,z6]),(0,[z683,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z684,z3,z8,z5,z6]),(0,[z1,z685,z2,z3,z8,z5,z6])]],
   [[(0,[z137,z1,z2,z3,z8,z5,z175]),(0,[z1,z2,z44,z3,z8,z5,z6]),(0,[z1,z2,z3,z686,z8,z5,z6])],[(0,[z687,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z688,z5,z6]),(0,[z689,z1,z2,z3,z8,z5,z6]),(0,[z96,z2,z3,z8,z46,z5,z6]),(0,[z1,z2,z3,z8,z690,z5,z6]),(0,[z0,z1,z2,z3,z143,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z691,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z90]),(0,[z1,z2,z3,z8,z5,z14,z69])],[(0,[z1,z2,z692,z3,z8,z5,z6]),(0,[z1,z2,z3,z693,z8,z5,z6]),(0,[z1,z155,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z52,z147,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z29])],[(0,[z1,z2,z694,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z84,z5,z14]),(0,[z1,z2,z3,z246,z8,z5,z9]),(0,[z115,z1,z2,z3,z8,z49,z6])],[(0,[z1,z2,z3,z608,z8,z5,z6]),(0,[z1,z695,z2,z3,z8,z5,z6]),(0,[z23,z1,z2,z8,z5,z68,z6])],[(0,[z1,z2,z3,z8,z5,z696,z6]),(0,[z160,z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z120,z14]),(0,[z1,z2,z3,z8,z697,z5,z6])],[(0,[z1,z2,z3,z8,z5,z266,z6]),(0,[z106,z1,z2,z3,z8,z231,z6]),(0,[z698,z1,z2,z3,z8,z5,z6]),(0,[z1,z699,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z700,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z701]),(0,[z1,z2,z3,z8,z5,z271,z6]),(0,[z96,z0,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z196,z6]),(0,[z1,z2,z3,z8,z5,z702,z6]),(0,[z1,z2,z3,z8,z5,z703,z6]),(0,[z1,z2,z3,z704,z8,z5,z6]),(0,[z705,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z380,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z8,z5,z128]),(0,[z1,z2,z3,z578,z286,z6]),(0,[z1,z205,z3,z45,z5,z6])],[(0,[z92,z2,z3,z8,z156,z14]),(0,[z1,z3,z8,z5,z14,z707]),(0,[z708,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z709])],[(0,[z1,z2,z3,z8,z5,z710]),(0,[z0,z2,z3,z178,z5,z6]),(0,[z1,z2,z3,z711,z5,z6]),(0,[z1,z2,z3,z578,z5,z14]),(0,[z1,z2,z3,z8,z5,z712]),(0,[z1,z2,z380,z8,z84,z6]),(0,[z7,z1,z2,z3,z64,z9]),(0,[z1,z2,z3,z8,z5,z713])],[(0,[z1,z2,z3,z8,z5,z714]),(0,[z673,z2,z3,z8,z196,z6]),(0,[z400,z2,z3,z8,z5,z476])],[(0,[z1,z2,z3,z8,z5,z132])],[(0,[z137,z164,z3,z8,z25,z6]),(0,[z17,z82,z3,z8,z5,z271]),(0,[z96,z2,z3,z46,z5,z9]),(0,[z1,z2,z715,z8,z5,z6]),(0,[z1,z2,z239,z8,z49,z6])],[(0,[z160,z582,z2,z3,z8,z5]),(0,[z1,z205,z3,z45,z5,z393]),(0,[z1,z716,z3,z8,z5,z6]),(0,[z1,z2,z3,z717,z5,z6])],[(0,[z1,z2,z3,z8,z718,z6]),(0,[z1,z2,z174,z8,z25,z6]),(0,[z32,z2,z3,z8,z328,z6])]],
   [[(0,[z1,z3,z616,z8,z5,z9]),(0,[z20,z400,z13,z8,z5,z6]),(0,[z106,z1,z3,z172,z227,z6])],[(0,[z1,z2,z719,z8,z5,z6]),(0,[z2,z720,z3,z8,z5,z6]),(0,[z1,z621,z3,z8,z5,z9]),(1,[z1,z3,z721,z5,z6])],[(0,[z1,z2,z3,z8,z722,z6]),(0,[z1,z2,z380,z8,z5,z14]),(0,[z1,z2,z3,z5,z120,z723])],[(0,[z137,z164,z3,z8,z5,z6]),(0,[z1,z2,z3,z142,z286,z6]),(0,[z7,z1,z2,z3,z219,z64])],[(0,[z137,z164,z3,z8,z264,z6]),(0,[z1,z334,z3,z8,z5,z9]),(0,[z160,z1,z65,z3,z8,z5])],[(0,[z1,z2,z174,z8,z5,z6]),(0,[z17,z82,z3,z8,z5,z87]),(0,[z1,z2,z306,z8,z5,z69]),(0,[z1,z2,z3,z8,z5,z724]),(0,[z1,z2,z3,z8,z5,z725])],[(0,[z1,z2,z174,z8,z264,z6])],[(0,[z1,z726,z3,z8,z5,z6]),(0,[z32,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z328,z476])]],
   [[(0,[z1,z2,z3,z608,z5,z175]),(0,[z1,z2,z3,z8,z727,z6]),(0,[z728,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z145,z5,z93])],[(0,[z1,z2,z3,z8,z5,z729]),(0,[z1,z2,z3,z730,z5,z6]),(0,[z1,z2,z3,z8,z731,z6]),(0,[z1,z3,z8,z5,z641,z9]),(0,[z1,z732,z3,z8,z5,z6])],[(0,[z1,z2,z42,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z733]),(0,[z734,z1,z2,z3,z8,z6]),(0,[z2,z613,z39,z8,z5,z6]),(0,[z1,z2,z191,z8,z5,z6]),(0,[z1,z522,z3,z8,z5,z9]),(0,[z1,z2,z3,z735,z5,z6]),(0,[z86,z1,z2,z3,z8,z736])],[(0,[z1,z2,z3,z737,z5,z6]),(0,[z1,z2,z3,z8,z738,z6])],[(0,[z1,z2,z3,z8,z227,z9]),(0,[z1,z2,z739,z8,z5,z14])],[(0,[z96,z1,z2,z380,z5,z6]),(0,[z1,z2,z3,z8,z5,z201]),(0,[z575,z1,z2,z3,z64,z6])],[],[(0,[z1,z2,z3,z8,z5,z740]),(0,[z197,z1,z185,z2,z3,z5]),(0,[z1,z2,z3,z8,z286,z9]),(0,[z1,z2,z179,z8,z5,z131]),(1,[z1,z2,z8,z738,z6])]],
   [[(0,[z1,z2,z3,z76,z5,z14]),(0,[z137,z741,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z660,z9]),(0,[z1,z2,z3,z578,z5,z192]),(0,[z1,z34,z3,z8,z731,z6]),(0,[z1,z34,z3,z8,z84,z9]),(0,[z742,z1,z2,z3,z8,z5]),(0,[z1,z665,z3,z8,z5,z9]),(0,[z51,z1,z2,z462,z5,z6])],[(0,[z17,z741,z3,z8,z5,z6]),(0,[z1,z2,z3,z743,z5,z6]),(0,[z1,z2,z3,z744,z5,z6]),(0,[z1,z2,z3,z8,z5,z707]),(0,[z1,z2,z133,z143,z5,z9]),(0,[z1,z667,z3,z8,z5,z9])],[(0,[z1,z2,z3,z8,z745,z6]),(0,[z1,z2,z3,z8,z746,z5]),(0,[z1,z2,z747,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z748]),(0,[z1,z2,z3,z8,z5,z444])],[(0,[z1,z3,z8,z15,z50,z9])],[(0,[z1,z749,z3,z8,z5,z6]),(0,[z160,z2,z191,z8,z5,z90]),(0,[z1,z2,z638,z143,z5,z6]),(0,[z1,z34,z3,z8,z84,z93]),(0,[z1,z3,z8,z84,z731,z6]),(0,[z170,z1,z2,z3,z8,z167])],[(0,[z1,z2,z750,z8,z5,z6]),(0,[z92,z2,z3,z8,z156,z6]),(0,[z197,z1,z2,z3,z15,z6]),(0,[z197,z1,z2,z3,z5,z9]),(0,[z751,z2,z3,z8,z5,z6]),(0,[z80,z1,z3,z8,z15,z9]),(0,[z1,z3,z8,z5,z14,z9]),(0,[z1,z2,z3,z8,z752,z6]),(0,[z1,z2,z8,z5,z753,z6]),(0,[z1,z2,z3,z8,z5,z754])],[(0,[z2,z3,z8,z5,z755,z6]),(0,[z1,z2,z3,z578,z5,z6]),(0,[z1,z2,z3,z8,z231,z6]),(0,[z1,z2,z249,z5,z48,z6])],[(0,[z756,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z757,z5,z6]),(0,[z1,z2,z3,z758,z8,z5]),(0,[z1,z3,z8,z5,z675,z9])]],
   [[(0,[z1,z2,z3,z8,z759,z6]),(0,[z1,z2,z3,z8,z5,z760]),(0,[z1,z2,z3,z761,z5,z6]),(0,[z1,z2,z3,z762,z5,z6]),(0,[z1,z2,z763,z3,z5,z6]),(0,[z1,z2,z3,z764,z5,z6]),(0,[z91,z185,z2,z3,z8,z196]),(0,[z1,z2,z3,z765,z5,z6]),(0,[z1,z2,z380,z45,z5,z6]),(0,[z1,z2,z3,z188,z5,z120]),(0,[z1,z2,z3,z8,z766,z6])],[(0,[z1,z2,z3,z8,z5,z767]),(0,[z1,z2,z3,z8,z5,z768]),(0,[z1,z2,z3,z769,z5,z6])],[(0,[z1,z2,z3,z8,z5,z770])],[(0,[z1,z2,z157,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z771]),(0,[z1,z2,z380,z147,z5,z6])],[(0,[z1,z2,z3,z8,z5,z772]),(0,[z773,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z775,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z776]),(0,[z1,z2,z3,z8,z5,z777]),(0,[z1,z3,z594,z8,z5,z14])],[(0,[z1,z2,z778,z8,z5,z6]),(0,[z1,z2,z779,z8,z5,z6]),(0,[z32,z2,z3,z8,z5,z192]),(0,[z780,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z781]),(0,[z7,z1,z2,z3,z287,z6]),(0,[z70,z1,z2,z8,z5,z340]),(1,[z1,z2,z769,z5,z6]),(0,[z1,z2,z3,z5,z6,z723])],[(0,[z1,z2,z3,z5,z782,z6]),(0,[z1,z2,z783,z8,z5,z6]),(0,[z1,z2,z784,z8,z5,z6]),(0,[z1,z3,z172,z721,z5,z6]),(0,[z1,z2,z3,z27,z5,z93])],[(0,[z1,z2,z3,z8,z785,z6]),(0,[z26,z2,z39,z8,z5,z14]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z86,z1,z163,z3,z8,z41])]],
   [[(0,[z1,z2,z42,z8,z25,z6]),(0,[z1,z2,z3,z8,z787,z6]),(0,[z1,z2,z3,z8,z5,z788]),(0,[z1,z2,z3,z8,z5,z789]),(0,[z1,z2,z790,z8,z5,z9])],[(0,[z1,z2,z3,z8,z5,z791]),(0,[z1,z2,z3,z8,z5,z266]),(0,[z106,z1,z3,z172,z5,z6]),(0,[z1,z2,z239,z8,z247,z6]),(0,[z1,z2,z3,z8,z5,z792])],[(0,[z1,z2,z3,z793,z5,z6]),(0,[z1,z21,z38,z8,z5,z101])],[(0,[z1,z2,z3,z8,z794,z6]),(0,[z1,z2,z3,z5,z795,z9])],[(0,[z1,z2,z3,z8,z5,z796])],[(0,[z1,z2,z3,z797,z5,z6]),(0,[z1,z2,z3,z8,z5,z798])],[(0,[z1,z2,z42,z8,z5,z6]),(0,[z1,z2,z3,z8,z799,z6]),(0,[z1,z2,z3,z8,z800,z6]),(0,[z1,z2,z3,z8,z5,z801]),(1,[z1,z2,z3,z5,z723])],[(0,[z1,z2,z42,z608,z5,z6]),(0,[z1,z2,z42,z8,z264,z6]),(0,[z1,z2,z3,z8,z25,z9]),(0,[z1,z2,z3,z8,z802,z6]),(0,[z1,z2,z803,z8,z5,z6]),(0,[z1,z65,z3,z8,z5,z41])]],
   [[(0,[z1,z2,z739,z8,z5,z6]),(0,[z20,z1,z13,z8,z5,z14]),(0,[z1,z163,z3,z8,z5,z14])],[(0,[z17,z82,z3,z8,z5,z6]),(0,[z400,z2,z3,z578,z5,z6]),(0,[z1,z3,z8,z15,z48,z9]),(0,[z1,z3,z8,z49,z15,z9]),(0,[z1,z2,z804,z3,z8,z5])],[(0,[z137,z164,z3,z8,z5,z14]),(0,[z805,z2,z3,z8,z5,z6]),(0,[z1,z451,z3,z8,z5,z9])],[(0,[z1,z2,z806,z8,z5,z6]),(0,[z1,z65,z3,z8,z5,z9]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z1,z2,z3,z147,z4,z6]),(0,[z1,z2,z808,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z809])],[(0,[z1,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z76,z264,z6]),(0,[z1,z2,z3,z810,z5,z6])],[(0,[z1,z2,z3,z8,z264,z9]),(0,[z1,z2,z3,z8,z5,z811]),(0,[z1,z2,z747,z8,z5,z6]),(0,[z115,z1,z2,z417,z48,z6]),(1,[z1,z2,z3,z766,z6])],[(0,[z1,z3,z8,z5,z707,z9]),(0,[z1,z65,z3,z8,z5,z68])]],
   [[(0,[z1,z2,z3,z8,z5,z812]),(0,[z408,z1,z2,z52,z5,z6])],[(0,[z1,z2,z3,z8,z5,z813]),(0,[z1,z814,z2,z3,z8,z5]),(0,[z1,z2,z191,z8,z5,z14]),(0,[z1,z2,z3,z249,z5,z9]),(0,[z1,z2,z3,z815,z8,z5]),(0,[z1,z2,z3,z4,z766,z6])],[(0,[z338,z2,z3,z178,z5,z6]),(0,[z91,z2,z3,z8,z196,z14]),(0,[z1,z2,z3,z8,z5,z816]),(0,[z1,z784,z13,z8,z5,z6]),(0,[z1,z34,z3,z8,z10,z6]),(0,[z1,z472,z3,z8,z5,z14])],[(0,[z1,z2,z3,z8,z817,z6]),(0,[z1,z2,z818,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z819]),(0,[z1,z2,z3,z8,z5,z101])],[(0,[z1,z820,z3,z8,z5,z6]),(0,[z1,z2,z3,z172,z227,z6]),(0,[z171,z1,z3,z172,z5,z6]),(0,[z1,z34,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z135,z50]),(0,[z1,z2,z3,z28,z5,z300]),(0,[z1,z2,z58,z8,z5,z107]),(0,[z1,z2,z3,z5,z766,z6])],[(0,[z1,z2,z3,z578,z328,z6]),(0,[z1,z2,z821,z3,z8,z5]),(0,[z1,z2,z822,z8,z5,z9])],[(0,[z1,z441,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z823]),(0,[z1,z2,z3,z824,z8,z5]),(0,[z1,z2,z3,z8,z5,z116])],[(0,[z1,z2,z3,z8,z5,z825]),(0,[z1,z2,z3,z8,z5,z826])]],
   [[(0,[z741,z164,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z827,z6]),(0,[z1,z2,z3,z8,z5,z828]),(0,[z1,z2,z3,z8,z6,z829]),(0,[z830,z2,z3,z8,z5,z6]),(0,[z1,z65,z3,z28,z8,z5])],[(0,[z1,z2,z831,z8,z5,z9]),(0,[z1,z2,z3,z8,z6,z832]),(0,[z1,z2,z3,z168,z5,z454])],[(0,[z1,z2,z3,z8,z5,z833]),(0,[z1,z2,z3,z8,z5,z834])],[(0,[z1,z2,z835,z3,z8,z5]),(0,[z26,z2,z39,z8,z5,z6]),(0,[z2,z3,z178,z836,z5,z6]),(0,[z86,z1,z2,z306,z8,z5])],[(0,[z1,z2,z3,z8,z5,z837]),(0,[z1,z2,z3,z76,z5,z175]),(0,[z1,z2,z3,z838,z5,z6])],[(0,[z1,z2,z3,z8,z5,z839]),(0,[z1,z2,z517,z8,z5,z107]),(0,[z1,z2,z3,z8,z231,z14]),(0,[z1,z569,z3,z8,z5,z9]),(0,[z840,z1,z2,z3,z8,z6])],[(0,[z1,z2,z841,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z842]),(0,[z20,z1,z13,z8,z5,z192]),(0,[z1,z2,z3,z843,z5,z6]),(0,[z7,z1,z2,z3,z64,z6])],[(0,[z1,z2,z3,z844,z8,z5])]],
   [[(0,[z845,z1,z2,z8,z5,z6]),(0,[z91,z197,z2,z3,z196,z6]),(0,[z400,z2,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z846]),(0,[z1,z205,z3,z45,z5,z132]),(0,[z1,z3,z8,z5,z731,z6]),(0,[z1,z847,z2,z8,z5,z14]),(0,[z1,z2,z3,z848,z5,z6]),(0,[z86,z1,z2,z3,z8,z223])],[(0,[z1,z2,z849,z8,z5,z6]),(0,[z1,z2,z850,z8,z5,z6]),(0,[z1,z2,z851,z3,z5,z6]),(0,[z1,z2,z8,z5,z738,z6])],[(0,[z540,z2,z44,z8,z5,z6]),(0,[z1,z2,z239,z249,z5,z6])],[(0,[z852,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z853]),(0,[z1,z2,z3,z8,z5,z854]),(0,[z1,z3,z8,z156,z15,z9]),(0,[z20,z1,z13,z8,z5,z6]),(0,[z1,z163,z3,z8,z5,z6]),(0,[z51,z1,z2,z52,z5,z14]),(0,[z855,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z271]),(0,[z350,z2,z39,z8,z5,z6]),(0,[z1,z2,z3,z414,z4,z6]),(0,[z1,z2,z508,z3,z5,z300]),(0,[z1,z2,z3,z168,z5,z723])],[(0,[z856,z1,z2,z3,z8,z6]),(0,[z1,z2,z857,z8,z5,z6]),(0,[z72,z1,z3,z8,z5,z707]),(0,[z86,z1,z2,z3,z8,z359])],[(0,[z1,z2,z3,z858,z5,z6]),(0,[z137,z164,z3,z608,z5,z6]),(0,[z1,z2,z3,z8,z5,z859]),(0,[z1,z2,z3,z145,z5,z9]),(0,[z1,z2,z561,z8,z5,z107])]],
   [[(0,[z1,z2,z3,z8,z5,z860]),(0,[z1,z2,z3,z8,z5,z861]),(0,[z1,z2,z3,z142,z5,z14]),(0,[z106,z1,z3,z172,z5,z14])],[(0,[z1,z2,z174,z608,z5,z6]),(0,[z1,z2,z3,z8,z5,z862]),(0,[z659,z1,z3,z8,z15,z6]),(0,[z350,z2,z3,z8,z5,z90])],[(0,[z1,z2,z3,z578,z5,z476]),(0,[z1,z2,z3,z45,z227,z6]),(0,[z23,z1,z2,z8,z5,z68]),(0,[z1,z2,z3,z8,z736,z41])],[(0,[z1,z2,z863,z8,z5,z6]),(0,[z1,z2,z3,z8,z25,z372]),(0,[z1,z2,z3,z5,z864,z6]),(0,[z1,z2,z3,z8,z865,z6]),(0,[z1,z2,z176,z8,z5,z9]),(0,[z1,z2,z3,z246,z5,z356])],[(0,[z197,z1,z2,z3,z392,z5]),(0,[z1,z2,z3,z8,z328,z9])],[(0,[z1,z2,z3,z8,z5,z87]),(0,[z1,z2,z3,z8,z5,z866]),(0,[z1,z2,z3,z8,z5,z867])],[(0,[z656,z2,z39,z8,z5,z6]),(0,[z91,z2,z3,z8,z196,z6]),(0,[z1,z2,z3,z868,z5,z6]),(0,[z1,z34,z3,z145,z5,z9]),(0,[z1,z572,z3,z8,z5,z9]),(0,[z7,z1,z2,z380,z64,z6])],[(0,[z160,z2,z3,z8,z5,z200])]],
   [[(0,[z17,z82,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z227,z6]),(0,[z1,z2,z8,z5,z68,z753])],[(0,[z1,z2,z3,z8,z5,z372]),(0,[z1,z2,z3,z8,z5,z869]),(0,[z1,z2,z3,z8,z5,z870]),(0,[z1,z2,z39,z8,z5,z355]),(0,[z1,z2,z3,z130,z5,z9]),(0,[z1,z2,z3,z8,z871,z5])],[(0,[z1,z2,z3,z8,z264,z372]),(0,[z1,z2,z3,z8,z5,z872]),(0,[z1,z2,z3,z147,z4,z14])],[(0,[z1,z2,z3,z8,z286,z6]),(0,[z1,z21,z38,z8,z5,z266]),(0,[z80,z1,z3,z8,z15,z281]),(0,[z1,z3,z8,z5,z9,z442]),(0,[z1,z65,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z723])],[(0,[z1,z2,z549,z52,z5,z6]),(0,[z1,z2,z873,z8,z5,z6]),(0,[z1,z2,z380,z8,z15,z6]),(0,[z1,z2,z3,z5,z6,z874])],[(0,[z1,z2,z875,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z876]),(0,[z1,z2,z133,z143,z5,z6]),(0,[z1,z2,z3,z28,z500,z5])],[(0,[z137,z164,z3,z8,z5,z175]),(0,[z1,z2,z3,z8,z5,z877]),(0,[z18,z2,z3,z8,z5,z200]),(0,[z1,z2,z3,z878,z5,z6])],[(0,[z32,z2,z3,z8,z5,z476]),(0,[z115,z1,z2,z8,z48,z9]),(0,[z879,z2,z3,z8,z5,z6]),(0,[z1,z880,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z174,z8,z5,z175]),(0,[z253,z1,z3,z8,z5,z9]),(0,[z89,z1,z65,z3,z8,z5]),(0,[z1,z2,z3,z8,z881,z6]),(0,[z1,z2,z3,z8,z135,z173]),(0,[z1,z2,z3,z147,z766,z6])],[(0,[z1,z882,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z883])],[(0,[z1,z2,z3,z8,z5,z884]),(0,[z1,z2,z3,z8,z885,z6]),(0,[z1,z2,z3,z8,z5,z886])],[(0,[z1,z2,z887,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z888]),(0,[z1,z2,z239,z8,z49,z444])],[(0,[z1,z2,z44,z8,z5,z355]),(0,[z1,z847,z2,z8,z5,z6]),(0,[z1,z236,z3,z8,z5,z9])],[(0,[z1,z504,z3,z8,z5,z9]),(0,[z1,z2,z3,z27,z15,z6]),(0,[z1,z2,z3,z27,z5,z9])],[(0,[z1,z2,z3,z8,z5,z889]),(0,[z1,z2,z3,z8,z890,z5]),(0,[z1,z2,z3,z8,z891,z6]),(0,[z1,z2,z3,z142,z5,z192]),(0,[z1,z2,z3,z8,z5,z892]),(0,[z106,z1,z3,z721,z5,z6]),(0,[z1,z155,z3,z8,z5,z9])],[(0,[z1,z2,z3,z8,z5,z893]),(0,[z1,z21,z38,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z894])]],
   [[(0,[z1,z2,z3,z8,z5,z895]),(0,[z1,z3,z8,z5,z15,z368]),(0,[z51,z1,z2,z52,z5,z6]),(0,[z1,z2,z3,z8,z6,z736]),(0,[z1,z2,z3,z8,z136,z736])],[(0,[z1,z676,z3,z8,z5,z9]),(0,[z1,z3,z8,z5,z14,z646])],[(0,[z1,z2,z3,z8,z5,z896]),(0,[z1,z2,z3,z8,z5,z897]),(0,[z1,z3,z784,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z898]),(0,[z20,z1,z13,z8,z328,z6]),(0,[z1,z666,z3,z45,z5,z6]),(0,[z1,z3,z258,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z219])],[(0,[z1,z2,z3,z8,z392,z5]),(0,[z1,z2,z3,z8,z5,z755]),(0,[z1,z2,z3,z142,z5,z6]),(0,[z1,z2,z3,z899,z5,z6]),(0,[z1,z34,z3,z27,z5,z9]),(0,[z1,z2,z3,z8,z5,z900]),(0,[z1,z2,z790,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z901]),(0,[z1,z2,z902,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z903]),(0,[z7,z1,z2,z3,z64,z14])],[(0,[z1,z741,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z904])],[(0,[z629,z2,z39,z8,z5,z6]),(0,[z1,z2,z3,z5,z795,z6]),(0,[z1,z2,z3,z8,z5,z905]),(0,[z1,z2,z3,z906,z5,z9]),(0,[z552,z1,z2,z8,z5,z431])]],
   [[(0,[z1,z2,z3,z8,z5,z907]),(0,[z1,z2,z3,z8,z5,z908]),(0,[z1,z909,z3,z8,z5,z6]),(0,[z96,z2,z3,z46,z5,z14]),(0,[z1,z2,z3,z5,z309,z9]),(0,[z1,z2,z306,z8,z5,z90]),(0,[z1,z2,z910,z8,z5,z6])],[],[(0,[z1,z2,z3,z8,z5,z911]),(0,[z7,z1,z2,z3,z460,z6]),(0,[z1,z2,z3,z8,z5,z912])],[(0,[z1,z2,z3,z8,z25,z6]),(0,[z1,z3,z8,z5,z913,z6]),(0,[z20,z32,z13,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z281]),(0,[z1,z54,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z914]),(0,[z1,z2,z915,z8,z5,z6])],[(0,[z1,z2,z3,z224,z5,z9]),(0,[z1,z3,z622,z8,z5,z14]),(0,[z916,z2,z3,z8,z5,z6])],[(0,[z17,z326,z3,z8,z5,z6]),(0,[z1,z280,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z917])],[(0,[z1,z2,z3,z8,z135,z79])],[(0,[z1,z2,z3,z8,z918,z5]),(0,[z1,z2,z3,z8,z5,z919]),(0,[z1,z2,z3,z8,z5,z920]),(0,[z1,z65,z3,z8,z5,z6]),(0,[z1,z699,z3,z8,z5,z9]),(0,[z1,z2,z3,z109,z5,z199]),(0,[z1,z2,z3,z8,z5,z736]),(0,[z1,z2,z3,z8,z135,z736])]],
   [[(0,[z1,z2,z3,z8,z5,z921]),(0,[z1,z922,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z923,z6]),(0,[z1,z2,z3,z8,z5,z924]),(0,[z1,z2,z3,z8,z925,z6]),(0,[z170,z1,z3,z8,z15,z9]),(0,[z1,z2,z3,z926,z5,z6]),(0,[z1,z2,z3,z8,z5,z927]),(0,[z1,z2,z3,z8,z5,z928])],[(0,[z1,z2,z3,z608,z5,z9]),(0,[z1,z2,z929,z8,z5,z6]),(0,[z1,z288,z3,z8,z5,z9]),(0,[z1,z2,z3,z930,z5,z6]),(0,[z1,z2,z3,z8,z931,z6]),(0,[z1,z205,z3,z45,z5,z9]),(0,[z1,z163,z3,z8,z5,z438])],[(0,[z253,z164,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z183,z6]),(0,[z1,z2,z453,z8,z49,z6]),(0,[z51,z1,z2,z769,z5,z6])],[(0,[z0,z2,z3,z178,z5,z9]),(0,[z1,z94,z3,z45,z5,z6]),(0,[z1,z3,z8,z5,z707,z6]),(0,[z1,z2,z297,z143,z5,z6])],[(0,[z26,z2,z39,z8,z5,z355]),(0,[z1,z2,z3,z8,z5,z932])],[(0,[z1,z2,z3,z836,z5,z6]),(0,[z1,z2,z933,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z934])],[(0,[z1,z2,z239,z8,z49,z9])],[(0,[z1,z2,z3,z935,z8,z5]),(0,[z400,z2,z3,z142,z5,z6]),(0,[z936,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z227,z14]),(0,[z1,z2,z3,z8,z5,z937])]],
   [[(0,[z1,z2,z938,z8,z5,z6]),(0,[z1,z2,z3,z939,z5,z6]),(0,[z197,z1,z2,z3,z84,z6]),(0,[z20,z1,z13,z8,z5,z476]),(1,[z1,z3,z8,z731,z6]),(0,[z80,z1,z3,z8,z731,z6]),(0,[z1,z3,z8,z5,z302,z9])],[(0,[z1,z2,z42,z8,z5,z175]),(0,[z1,z2,z3,z8,z5,z940]),(0,[z0,z1,z2,z380,z5,z6]),(0,[z1,z2,z306,z8,z5,z9]),(0,[z1,z2,z822,z8,z5,z6])],[(0,[z1,z2,z3,z941,z5,z6]),(0,[z458,z2,z3,z8,z156,z6]),(0,[z1,z2,z3,z8,z286,z14]),(0,[z1,z2,z3,z8,z5,z942]),(0,[z1,z2,z3,z63,z8,z5])],[(0,[z137,z164,z3,z76,z5,z6]),(0,[z91,z2,z3,z8,z885,z6]),(0,[z160,z2,z3,z8,z5,z90]),(0,[z1,z2,z3,z8,z5,z943]),(0,[z1,z34,z3,z8,z84,z14])],[(0,[z1,z944,z3,z8,z5,z6]),(0,[z1,z2,z133,z143,z5,z14])],[(0,[z1,z2,z174,z76,z5,z6]),(0,[z1,z2,z3,z8,z945,z6]),(0,[z1,z504,z3,z8,z84,z6]),(0,[z32,z2,z38,z8,z5,z6]),(0,[z1,z2,z3,z417,z5,z9])],[(0,[z1,z2,z3,z8,z5,z946]),(0,[z947,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z5,z948]),(0,[z1,z2,z8,z5,z753,z107])],[(0,[z1,z2,z949,z8,z5,z6]),(0,[z950,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z951,z6]),(0,[z1,z2,z3,z8,z102,z369]),(0,[z1,z2,z239,z8,z49,z116]),(0,[z1,z2,z3,z8,z5,z952]),(0,[z1,z2,z3,z168,z5,z120])]],
   [[(0,[z197,z1,z2,z3,z5,z14]),(0,[z1,z2,z953,z8,z5,z6]),(0,[z80,z1,z3,z8,z15,z14])],[(0,[z1,z2,z3,z8,z954,z6]),(0,[z1,z2,z3,z8,z955,z6]),(0,[z1,z2,z3,z8,z5,z956]),(0,[z1,z2,z3,z8,z957,z6]),(0,[z1,z614,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z958,z6]),(0,[z1,z34,z3,z8,z84,z438]),(0,[z1,z2,z3,z8,z5,z959])],[(0,[z1,z2,z3,z8,z960,z6]),(0,[z1,z315,z2,z8,z5,z68]),(0,[z1,z2,z3,z8,z5,z961]),(0,[z1,z962,z3,z8,z5,z6])],[(0,[z1,z963,z3,z8,z5,z6]),(0,[z327,z1,z3,z8,z5,z14]),(0,[z1,z2,z3,z142,z328,z6]),(0,[z1,z2,z3,z8,z5,z964])],[(0,[z96,z2,z3,z46,z5,z6]),(0,[z965,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z966])],[(0,[z32,z2,z3,z578,z5,z6]),(0,[z1,z155,z3,z8,z5,z707])],[(0,[z1,z2,z3,z8,z5,z967]),(0,[z1,z2,z3,z968,z5,z6]),(0,[z1,z2,z3,z969,z5,z6]),(0,[z1,z2,z970,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z971]),(0,[z1,z2,z3,z8,z972,z6])],[(0,[z2,z741,z3,z8,z5,z6]),(0,[z1,z2,z720,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z973])]],
   [[(0,[z1,z2,z3,z8,z5,z974]),(0,[z1,z2,z3,z8,z975,z6])],[(0,[z1,z2,z3,z8,z231,z47]),(0,[z1,z976,z3,z8,z5,z6]),(0,[z7,z1,z2,z3,z384,z6])],[(0,[z1,z2,z78,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z977]),(0,[z1,z2,z8,z5,z978,z6]),(0,[z72,z1,z3,z8,z5,z14])],[(0,[z96,z2,z3,z836,z5,z6]),(0,[z1,z2,z3,z8,z5,z979]),(0,[z1,z2,z3,z8,z5,z980])],[(0,[z1,z493,z2,z52,z5,z6]),(0,[z7,z1,z2,z3,z63,z64])],[(0,[z1,z2,z8,z49,z738,z6])],[(0,[z1,z2,z3,z981,z5,z6]),(0,[z92,z2,z3,z8,z885,z6]),(0,[z92,z2,z3,z8,z156,z9]),(0,[z7,z1,z2,z176,z64,z6])],[(0,[z1,z2,z3,z578,z5,z9]),(0,[z1,z2,z176,z8,z5,z6]),(0,[z1,z2,z769,z8,z5,z6])]],
   [[(0,[z1,z2,z982,z8,z5,z6]),(0,[z32,z2,z3,z142,z5,z6]),(0,[z1,z2,z3,z8,z328,z6]),(0,[z983,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z286,z192]),(0,[z72,z1,z3,z8,z5,z438]),(0,[z1,z2,z179,z8,z5,z107])],[],[(0,[z1,z2,z3,z8,z25,z14]),(0,[z1,z2,z3,z721,z5,z6]),(0,[z1,z2,z3,z147,z211,z6])],[(0,[z1,z2,z3,z984,z5,z6])],[(0,[z106,z1,z3,z172,z5,z47]),(0,[z1,z2,z3,z985,z5,z6]),(0,[z86,z1,z65,z3,z8,z41])],[(0,[z1,z2,z3,z608,z5,z372]),(0,[z1,z2,z3,z130,z5,z6]),(0,[z1,z2,z986,z8,z5,z6]),(0,[z1,z2,z3,z8,z102,z136])],[(0,[z1,z2,z987,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z988]),(0,[z1,z2,z8,z738,z48,z6])],[(0,[z137,z164,z174,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z989]),(0,[z1,z34,z3,z8,z84,z6]),(0,[z1,z2,z380,z8,z5,z9]),(0,[z170,z1,z2,z3,z8,z41])]],
   [[(0,[z1,z2,z3,z8,z5,z14]),(0,[z1,z2,z3,z990,z5,z6]),(0,[z1,z2,z3,z142,z5,z476]),(0,[z1,z3,z8,z5,z9,z449]),(0,[z1,z2,z3,z8,z5,z991]),(0,[z1,z2,z3,z28,z5,z29])],[(0,[z1,z2,z992,z8,z5,z6]),(0,[z1,z2,z3,z608,z5,z14]),(0,[z1,z2,z3,z8,z264,z14]),(0,[z1,z2,z3,z993,z5,z6]),(0,[z1,z2,z3,z8,z5,z994]),(0,[z1,z2,z3,z8,z5,z995])],[(0,[z1,z3,z8,z5,z9,z607]),(0,[z996,z1,z2,z8,z5,z14])],[(0,[z1,z2,z3,z8,z997,z5]),(0,[z1,z2,z3,z8,z5,z998])],[(0,[z197,z1,z2,z3,z5,z6]),(0,[z603,z1,z3,z172,z5,z6]),(0,[z32,z2,z3,z8,z5,z9]),(0,[z80,z1,z3,z8,z15,z6]),(0,[z1,z2,z3,z249,z5,z14])],[(0,[z1,z2,z3,z999,z5,z6]),(0,[z115,z1,z2,z8,z738,z6])],[(0,[z1,z2,z42,z76,z5,z6]),(0,[z1,z2,z3,z8,z1000,z6]),(0,[z1,z2,z3,z8,z5,z1001]),(0,[z1,z2,z3,z8,z5,z438])],[(0,[z1,z2,z42,z8,z5,z9]),(0,[z1,z2,z3,z8,z1002,z6]),(0,[z1,z2,z3,z8,z5,z1003])]],
   [[(0,[z1,z2,z3,z1004,z5,z6]),(0,[z1,z2,z3,z8,z5,z1005]),(0,[z1,z2,z3,z1006,z5,z6]),(0,[z1,z2,z3,z8,z1007,z6]),(0,[z1,z1008,z3,z8,z5,z6]),(0,[z1009,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1010])],[(0,[z357,z2,z3,z46,z5,z6]),(0,[z1,z2,z1011,z8,z5,z6]),(0,[z1,z2,z306,z8,z5,z14]),(0,[z1,z2,z58,z8,z5,z574]),(0,[z1,z2,z769,z143,z5,z6]),(0,[z1,z1012,z3,z8,z5,z6])],[(0,[z1,z405,z3,z8,z5,z9])],[(0,[z126,z2,z39,z8,z5,z6]),(0,[z1,z21,z38,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1013])],[(0,[z1,z2,z3,z8,z1014,z6]),(0,[z1,z2,z3,z8,z5,z1015]),(0,[z1,z2,z3,z8,z5,z1016])],[(0,[z1,z2,z3,z8,z1017,z6]),(0,[z1,z2,z3,z76,z5,z9]),(0,[z1,z1018,z2,z8,z5,z6]),(0,[z1,z2,z275,z143,z5,z6]),(0,[z89,z2,z3,z8,z5,z413])],[(0,[z20,z1,z13,z578,z5,z6]),(0,[z1,z2,z3,z8,z1019,z6]),(0,[z1,z189,z3,z8,z5,z9])],[(0,[z1,z2,z3,z8,z5,z1020])]],
   [[(0,[z2,z720,z39,z8,z5,z6]),(0,[z1,z2,z3,z1021,z8,z5]),(0,[z1022,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z1023,z9]),(0,[z212,z1,z3,z8,z5,z14])],[(0,[z1,z2,z3,z8,z1024,z6]),(0,[z1,z2,z3,z1025,z5,z6]),(0,[z400,z2,z3,z8,z286,z6]),(0,[z1,z2,z3,z8,z1026,z6]),(0,[z575,z1,z2,z8,z48,z6])],[(0,[z1,z2,z3,z8,z5,z1027]),(0,[z26,z2,z720,z8,z5,z6])],[(0,[z1028,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1029]),(0,[z400,z2,z3,z8,z5,z14])],[(0,[z253,z1,z13,z8,z5,z6]),(0,[z1,z2,z3,z5,z309,z6]),(0,[z1,z151,z3,z8,z5,z14]),(0,[z1,z2,z3,z1030,z5,z6])],[(0,[z1,z2,z8,z5,z1031,z6]),(0,[z1,z34,z3,z8,z15,z9]),(0,[z1,z2,z3,z8,z5,z1032])],[(0,[z1,z2,z3,z1033,z5,z6]),(0,[z1,z1034,z3,z8,z5,z6]),(0,[z86,z1,z2,z3,z8,z214]),(0,[z1,z2,z3,z8,z5,z192]),(0,[z86,z1,z2,z3,z8,z449])],[(0,[z1,z2,z3,z608,z25,z6]),(0,[z1,z2,z3,z1035,z8,z5]),(0,[z1,z185,z2,z3,z5,z309]),(0,[z1036,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z168,z5,z199]),(0,[z1,z2,z3,z8,z5,z1037])]],
   [[(0,[z1,z2,z3,z224,z5,z6]),(0,[z1038,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z368]),(0,[z1,z3,z8,z5,z369,z9]),(0,[z1,z2,z3,z1039,z5,z6]),(0,[z1,z3,z8,z5,z438,z9])],[(0,[z1,z566,z3,z45,z5,z6]),(0,[z1,z2,z3,z8,z5,z1040]),(0,[z152,z1,z3,z8,z15,z6]),(0,[z1,z34,z3,z145,z84,z6]),(0,[z1,z2,z3,z8,z827,z9])],[(0,[z2,z3,z8,z5,z885,z6]),(0,[z1,z2,z3,z8,z231,z201]),(0,[z1,z2,z3,z145,z5,z14])],[(0,[z2,z3,z836,z46,z5,z6]),(0,[z1,z21,z784,z8,z5,z6]),(0,[z193,z2,z3,z8,z5,z381]),(0,[z1,z2,z8,z5,z14,z978]),(0,[z1041,z1,z2,z3,z5,z6]),(0,[z23,z1,z2,z8,z5,z753])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z26,z2,z39,z8,z5,z9]),(0,[z0,z2,z3,z836,z5,z6]),(0,[z1,z2,z3,z8,z5,z1042]),(0,[z1,z38,z784,z8,z5,z6]),(0,[z170,z1,z3,z8,z15,z6]),(0,[z1,z2,z3,z188,z5,z513]),(0,[z1,z2,z3,z28,z5,z723])],[(0,[z1,z2,z3,z608,z5,z6]),(0,[z1,z2,z3,z8,z264,z6]),(0,[z1,z65,z3,z8,z5,z136])],[(0,[z1,z2,z3,z1043,z5,z6]),(0,[z1,z2,z3,z608,z264,z6]),(0,[z91,z2,z3,z309,z196,z6]),(0,[z996,z1,z2,z8,z5,z6]),(0,[z1,z3,z8,z5,z181,z14]),(0,[z1,z2,z176,z8,z5,z14])],[(1,[z2,z3,z8,z885,z6]),(0,[z1,z2,z3,z8,z328,z14]),(0,[z1,z2,z3,z1044,z5,z6]),(0,[z1,z34,z3,z8,z5,z368]),(0,[z552,z1,z2,z8,z5,z68]),(0,[z1,z2,z3,z8,z5,z1045]),(0,[z1,z1046,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z136])]],
   [[(0,[z137,z164,z42,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1047]),(0,[z1,z3,z147,z8,z15,z9]),(0,[z1,z2,z3,z145,z5,z438]),(0,[z1,z2,z3,z249,z5,z6]),(0,[z7,z1,z2,z3,z766,z6])],[(0,[z1,z2,z3,z8,z5,z1048])],[(0,[z1,z2,z3,z8,z5,z393]),(0,[z1,z3,z8,z5,z456,z9])],[(0,[z1,z2,z3,z8,z5,z1049])],[(0,[z1,z2,z3,z5,z1050,z6]),(0,[z1,z2,z3,z8,z5,z1051]),(0,[z1,z2,z3,z8,z5,z1052]),(0,[z1,z2,z3,z130,z5,z14]),(0,[z207,z1,z2,z3,z8,z449])],[(0,[z1,z2,z306,z8,z5,z6]),(0,[z1053,z2,z3,z8,z5,z6]),(0,[z20,z1,z13,z8,z5,z9]),(0,[z106,z1,z3,z172,z5,z201]),(0,[z1,z163,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z1054,z6])],[(0,[z1,z2,z3,z8,z25,z175])],[(0,[z137,z164,z3,z8,z5,z9]),(0,[z1,z2,z380,z172,z5,z6]),(0,[z632,z1,z3,z8,z5,z14]),(0,[z1,z2,z674,z143,z5,z6])]],
   [[(0,[z1,z2,z831,z8,z5,z6]),(0,[z1055,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1056]),(0,[z1,z2,z3,z27,z84,z6])],[(0,[z1,z2,z174,z8,z5,z9]),(0,[z66,z2,z237,z8,z5,z6]),(0,[z2,z3,z8,z5,z755,z90]),(0,[z400,z2,z3,z8,z5,z192]),(0,[z2,z3,z8,z5,z1057,z6]),(0,[z1,z2,z3,z1058,z5,z6]),(0,[z1,z2,z3,z417,z5,z6]),(0,[z1,z2,z3,z5,z723,z29])],[(0,[z26,z2,z39,z8,z5,z128]),(0,[z32,z2,z3,z8,z286,z6]),(0,[z115,z1,z2,z8,z48,z14]),(0,[z1,z2,z491,z8,z5,z107])],[(0,[z1,z2,z42,z8,z5,z372]),(1,[z741,z3,z8,z5,z6]),(0,[z1,z3,z1059,z8,z5,z6]),(0,[z23,z1,z2,z8,z5,z506]),(0,[z1,z2,z3,z8,z1060,z6]),(0,[z96,z2,z3,z652,z5,z6]),(0,[z2,z3,z8,z885,z196,z6]),(0,[z1,z2,z3,z8,z5,z1061]),(0,[z160,z2,z3,z8,z5,z755]),(0,[z1,z2,z3,z8,z227,z47]),(1,[z1,z3,z8,z5,z707])],[(0,[z1,z2,z3,z8,z5,z175]),(0,[z598,z1,z3,z8,z15,z6]),(0,[z1,z2,z143,z5,z208,z6]),(0,[z86,z1,z2,z3,z8,z41])],[(0,[z1,z2,z3,z8,z264,z175]),(0,[z1,z2,z3,z1062,z5,z6]),(1,[z1,z2,z3,z8,z736])],[(0,[z1,z2,z191,z8,z5,z9]),(0,[z106,z1,z3,z172,z231,z6]),(0,[z734,z1,z2,z3,z8,z9]),(0,[z1,z2,z52,z769,z5,z6])],[(0,[z400,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z91,z2,z3,z8,z196,z9]),(0,[z160,z2,z306,z8,z5,z90]),(0,[z1,z3,z8,z5,z14,z623]),(0,[z1,z34,z3,z27,z84,z6])]],
   [[(0,[z1,z97,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z1064]),(0,[z1,z2,z3,z27,z5,z14])],[(0,[z1,z2,z3,z76,z5,z372]),(0,[z1,z2,z3,z8,z5,z1065]),(0,[z171,z1,z3,z8,z5,z9]),(0,[z23,z1,z2,z8,z5,z340]),(0,[z1,z2,z3,z8,z5,z1066]),(0,[z1,z65,z3,z168,z8,z5])],[(0,[z1,z2,z3,z5,z6,z1067]),(0,[z1,z2,z3,z8,z286,z476]),(0,[z1,z21,z38,z8,z5,z14])],[(0,[z1,z2,z3,z8,z5,z1068]),(0,[z1,z2,z3,z1069,z5,z6]),(0,[z1070,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1071])],[(0,[z1,z2,z3,z1072,z5,z6]),(0,[z1,z1073,z3,z8,z5,z6]),(0,[z1074,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z328,z192])],[(0,[z1,z2,z3,z145,z5,z6]),(0,[z1,z2,z3,z27,z5,z438]),(0,[z1,z54,z3,z8,z84,z6])],[(0,[z1,z2,z3,z1075,z5,z6]),(0,[z1,z2,z3,z1076,z5,z6])]],
   [[(0,[z1,z2,z3,z1077,z5,z6]),(0,[z1,z2,z3,z1078,z5,z6]),(0,[z1,z2,z3,z1079,z5,z6]),(1,[z1,z784,z8,z5,z6]),(0,[z1,z2,z3,z147,z465,z6]),(0,[z1,z3,z8,z5,z518,z9]),(0,[z1080,z2,z3,z8,z5,z6])],[(0,[z17,z2,z42,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1081])],[(0,[z1,z2,z3,z8,z5,z1082]),(0,[z1,z2,z3,z1083,z5,z6]),(1,[z2,z3,z836,z5,z6]),(0,[z1,z2,z3,z8,z231,z9]),(0,[z1,z699,z3,z8,z84,z6]),(0,[z1,z655,z3,z8,z5,z14]),(0,[z1,z2,z3,z8,z5,z1084])],[(0,[z1,z2,z3,z5,z309,z14]),(0,[z1,z2,z3,z8,z1085,z6]),(0,[z1,z2,z1086,z3,z8,z5])],[(0,[z91,z2,z3,z8,z392,z196]),(0,[z1,z2,z3,z8,z1087,z6]),(0,[z1,z2,z511,z8,z5,z68])],[(0,[z1,z2,z3,z8,z5,z1088])],[(0,[z1,z2,z3,z1089,z5,z6]),(0,[z2,z3,z8,z156,z885,z6]),(0,[z1,z2,z1090,z8,z5,z14])],[(0,[z1,z2,z3,z8,z5,z1091]),(0,[z1,z2,z3,z224,z5,z14]),(0,[z1,z2,z3,z8,z5,z1092]),(0,[z193,z2,z3,z8,z5,z90]),(0,[z1093,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z279,z14])]],
   [[(0,[z1,z2,z3,z8,z5,z1094]),(0,[z1,z2,z3,z246,z5,z29]),(0,[z1,z2,z239,z8,z738,z6]),(0,[z1,z65,z3,z8,z5,z107]),(0,[z1,z2,z1095,z8,z5,z6])],[(0,[z1,z2,z1096,z8,z5,z6]),(0,[z1097,z2,z3,z8,z5,z6]),(0,[z51,z1,z2,z52,z5,z9])],[(0,[z96,z425,z2,z3,z5,z6]),(0,[z1,z699,z3,z172,z5,z6]),(0,[z1,z2,z3,z8,z135,z394])],[(0,[z1,z1098,z3,z8,z5,z6]),(0,[z0,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z1099,z5,z6]),(0,[z1,z3,z721,z45,z5,z6]),(0,[z80,z1,z3,z8,z15,z368]),(0,[z1,z2,z380,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1100]),(0,[z1,z205,z3,z721,z5,z6]),(0,[z1,z205,z3,z45,z5,z14])],[(0,[z1,z2,z3,z8,z1101,z5]),(0,[z1,z2,z3,z142,z5,z9]),(0,[z106,z1,z3,z172,z5,z9]),(0,[z1,z2,z3,z8,z5,z1102]),(0,[z1,z3,z8,z5,z15,z9]),(0,[z1,z2,z3,z8,z5,z1103]),(0,[z1,z2,z481,z8,z5,z574]),(0,[z1,z2,z3,z8,z5,z753])],[(0,[z1,z1104,z2,z3,z8,z5]),(0,[z0,z2,z3,z178,z5,z14]),(0,[z115,z1,z2,z8,z48,z6])],[(0,[z1,z3,z8,z731,z15,z6])]],
   [[(0,[z1,z2,z3,z1105,z5,z6]),(0,[z1,z2,z1106,z8,z5,z6]),(0,[z32,z2,z3,z8,z5,z6])],[(0,[z20,z1,z784,z8,z5,z6]),(0,[z1,z3,z721,z8,z5,z6]),(0,[z1,z2,z3,z8,z1107,z6]),(0,[z1,z2,z239,z8,z49,z14]),(1,[z1,z2,z8,z5,z753]),(0,[z1,z2,z380,z5,z64,z6])],[(0,[z7,z1,z3,z8,z15,z9]),(0,[z1108,z1,z3,z8,z5,z6]),(0,[z115,z1,z2,z249,z48,z6]),(0,[z1,z65,z3,z8,z5,z369])],[(0,[z1,z2,z3,z76,z25,z6]),(0,[z137,z164,z3,z8,z5,z372]),(0,[z20,z1,z13,z8,z286,z6]),(0,[z7,z1,z2,z3,z105,z6])],[(0,[z1,z2,z3,z1109,z5,z6]),(0,[z1,z2,z3,z8,z5,z47]),(0,[z1,z2,z3,z27,z5,z6]),(0,[z1,z34,z3,z8,z5,z1102])],[(0,[z1,z2,z174,z8,z5,z372]),(0,[z17,z82,z3,z8,z5,z9]),(0,[z7,z1,z2,z3,z110,z6]),(0,[z1,z2,z306,z8,z135,z5]),(0,[z1,z325,z3,z8,z5,z9])],[(0,[z0,z2,z3,z5,z317,z6]),(0,[z1,z2,z3,z8,z5,z1110]),(0,[z400,z2,z3,z8,z328,z6]),(0,[z1,z2,z8,z5,z1111,z6])],[(0,[z1,z2,z3,z1112,z5,z6]),(0,[z1,z463,z38,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1113]),(0,[z1,z2,z3,z147,z4,z9]),(0,[z1,z2,z3,z766,z64,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z476]),(0,[z1,z2,z3,z8,z5,z1114]),(0,[z1,z2,z3,z8,z5,z1115]),(0,[z1,z2,z3,z8,z5,z1116]),(0,[z1,z2,z3,z417,z5,z14])],[(0,[z1,z2,z3,z76,z5,z6]),(0,[z1,z2,z174,z8,z5,z14]),(0,[z1,z2,z3,z8,z1117,z5]),(0,[z1,z2,z262,z143,z5,z6])],[(0,[z1,z2,z3,z8,z1118,z6])],[(0,[z1,z2,z1119,z8,z5,z6]),(0,[z1,z185,z2,z3,z8,z5]),(0,[z1,z2,z3,z1120,z5,z6]),(0,[z1,z2,z133,z769,z5,z6])],[(0,[z2,z164,z42,z8,z5,z6]),(0,[z1,z2,z3,z8,z1121,z6]),(0,[z1,z2,z8,z5,z1023,z6]),(0,[z1,z2,z1122,z3,z8,z5]),(0,[z1,z2,z3,z8,z227,z201])],[(0,[z1,z2,z3,z8,z5,z355]),(0,[z1,z2,z3,z8,z5,z1123]),(0,[z1,z2,z3,z1124,z5,z6]),(0,[z1,z3,z8,z5,z577,z9]),(0,[z1,z1125,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z1126,z6])],[(0,[z1,z2,z3,z906,z5,z6]),(0,[z1,z2,z3,z8,z5,z1127]),(0,[z1,z2,z1128,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z93]),(0,[z1,z282,z3,z8,z5,z9]),(0,[z1,z3,z581,z8,z5,z9]),(0,[z1,z2,z3,z8,z484,z50]),(0,[z1,z2,z3,z8,z5,z1129])],[(0,[z82,z741,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1130,z6]),(0,[z1,z1131,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z1132]),(0,[z32,z2,z13,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1133])],[(0,[z1,z2,z1090,z8,z5,z6]),(0,[z1,z94,z3,z8,z5,z9])],[(0,[z1,z2,z3,z392,z5,z309]),(0,[z1,z2,z3,z8,z5,z1134]),(0,[z410,z1,z2,z8,z48,z6])],[(0,[z2,z3,z8,z836,z5,z6]),(0,[z20,z1,z13,z142,z5,z6]),(0,[z1,z2,z58,z8,z5,z753]),(0,[z1135,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z1136,z6]),(0,[z1,z2,z3,z1137,z5,z6]),(0,[z1,z2,z3,z1138,z5,z6])],[(0,[z1,z2,z3,z8,z1139,z6]),(0,[z1,z3,z8,z5,z1102,z9]),(0,[z1,z53,z3,z8,z5,z9]),(0,[z1,z2,z3,z8,z5,z1140])],[(0,[z1,z3,z8,z196,z15,z9]),(0,[z1,z2,z3,z1141,z8,z5]),(0,[z457,z1,z3,z8,z5,z14])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 536).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1072).take 116) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1188)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [536, 536, 116] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 132).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 132).take 124).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [132, 124] = true :=
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

end PEqualNP.Outside.L_meta_46084

theorem PEqualNP.Outside.L_meta_46084 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4243126464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4243126464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46084.solve