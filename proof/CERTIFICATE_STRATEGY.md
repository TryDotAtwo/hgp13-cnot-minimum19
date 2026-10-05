# Current proof architecture

## Обновление границ задачи: полный kernel replay исключён

По прямому решению Ивана полная проверка всех секторов ядром Lean
НЕ НУЖНА и исключена из проекта, включая дополнительные цели.
Не планировать и не запускать её; не разрабатывать ради неё массовые
таблицы, индивидуальные секторные доказательства или масштабные пилоты.
Существующие результаты сохраняются только как уже полученные артефакты.
Обязательный результат: общая теория и обоснование алгоритма в Lean,
аудит конкретной реализации C++ и воспроизводимые внешние вычисления.
Этот результат нельзя называть безусловной kernel-проверкой минимума.
Любые старые планы полного kernel replay ниже являются архивными и отменены.


## Действующее решение Ивана — 2026-09-27

Обязательный результат текущей работы: формализация теоретической части
доказательства статьи в Lean плюс отдельно проверенная и воспроизводимая
внешняя вычислительная часть C++. Полный replay всех 363 секторов ядром
Lean НЕ является обязательным критерием завершения этого результата.

1. Закрыть общие математические обязательства: покрытие коротких программ,
   полноту абстрактного алгоритма, корректность отсечений, объединения
   состояний, каталогов и терминальной пассивной стоимости.
2. Проверить соответствие конкретного C++ этому алгоритму: разрядности,
   упаковку, историю, границы, сравнение меток, каталоги и терминальные тесты.
   Статический аудит не называть формальным доказательством семантики C++.
3. Проверить имеющиеся свидетельства полного успешного запуска всех секторов
   и их связь с точным исходником, инструментами и параметрами. Не повторять
   тяжёлый запуск без выявленной необходимости.
4. Сформулировать Lean-теорему с конкретной, явно названной внешней
   вычислительной предпосылкой и документировать её внешнее подтверждение.
   Не подменять этой предпосылкой недоказанные общие математические леммы.
5. Согласовать статью, реестр утверждений, статус и архив с этой границей.
   Итог нельзя называть безусловным доказательством минимума ядром Lean.

Полная kernel-теорема ExactMinimum исключена из целей проекта по решению Ивана.
Уже полученные доказательства и измерения сохраняются. Новая массовая
генерация таблиц, секторных сертификатов, SAT-пилотов и индивидуальных
теорем переходов не требуется. Сначала закрываются перечисленные выше
обязательства. Корректность статьи не предполагается: найденные пробелы
фиксируются и устраняются, а не скрываются в предпосылках.

Действующая условная теорема —
`ConcreteFiniteBoundary.exact_minimum_of_external_finite_result`.
`ExternalFiniteResult` явно означает полноту двух конкретных prefix-таблиц
и отсутствие дешёвого терминала во всех 363 абстрактных секторах.
`AbstractFiniteExclusion.no_short_in_sector` доказала общий перенос точной
терминальной стоимости к полной программе. `scripts/audit_full_run.py` и
`evidence/cpp_refinement_audit.md` документируют внешние данные и границу
соответствия C++/Lean. Они не превращают предпосылку в kernel-теорему.

# Proof architecture and current scalability gate

The archived, out-of-scope full-kernel theorem is the unconditional fixed-matrix bound
`HGP13.ExactMinimum HGP13.target 19` in the full 13-wire, 156-CNOT model.
The 19-gate witness is already formalized. The unresolved direction is that
every legal full word of length at most 18 is impossible.

## Historical full-kernel roadmap (cancelled; outside project scope)

1. Discharge concrete prefix lookup completeness in both orientations.
   `FullWordPath.short_word_accepted_path` now proves that every covered
   legal full realization of length at most 18 maps to an accepted labelled
   `SharedSearch` path with the correct terminal predicate, **conditional
   on this completeness condition**. Its proof uses one indexed core word
   throughout. `FullWordPathCertificates` reduces the condition to three
   concrete checks per orientation: triples into the depth-3 table,
   triples into the depth-4 table, and quadruples into the depth-4 table.
   All six large acceptance facts remain open. The exact full-row terminal
   cost transfer is now proved for sectors 234 and 359: their checked graphs
   exclude every compatible short full word under each sector's prefix-completeness
   premise. All-sector exclusion remains an additional obligation.
2. Prove the concrete prefix tables complete for every `Catalogued` set of
   up to four auxiliary forms and every observed subset. The generic list,
   tree, packed-tree and path-witness checkers are sound, but their large
   acceptance facts have not been established. The required deletion
   negative control must target a real admissible prefix in the final
   concrete certificate.
3. Establish kernel-checked exclusion for every needed sector, or prove a
   reduction to a smaller checked list with machine-checked coverage. Only
   selected sectors 284, 359 and 234 currently have graph certificates.
   Sectors 234 and 359 now have the full-word bridge conditional on concrete
   prefix completeness. The sector-284 pilot does not yet have that composition.
4. Compose exact terminal passive costs, sector coverage and the 19-gate
   witness into the theorem without an open hypothesis. Then run a clean
   build and transitive-axiom audit of that theorem, and synchronize source,
   generators, data, hashes, article and PDF.

## Cancelled full-kernel route: computation and trust boundary

An external C++ or Python program may search, deduplicate, compress and
**propose** data. Lean must prove a general soundness theorem for the
checker and prove the concrete checker returns `true` using kernel-trusted
reduction. A C++ success log or a Lean theorem conditional on an unproved
`check = true` does not establish this additional full-kernel result.
The current deliverable instead permits explicitly documented external
computational evidence, as specified above.

The current graph certificate for sector 234 illustrates a correct but
expensive boundary: C++ proposes 6668 states and 14098 transitions, while
Lean checks every `SharedSearch.next` equality. Splitting by depth kept each
process under 4 GiB. This is a selected pilot, not evidence that replaying
all 363 sectors is practical.

For the transpose prefix catalogue, a 20,125-node third-layer tree took
45 seconds to compile. A monolithic 970-parent transition theorem hit the
4 GiB limit. Twenty-five separate checks took 70 seconds; explicit path
witnesses for the same 25 took 71 seconds and added 155 KB of literals.
Straight-line extrapolation is about 45 minutes for the remaining
second-to-third checks in this orientation alone, and more than 15 hours
for 20,125 third-to-fourth parent checks at the same per-parent rate. These
are lower-confidence planning estimates: the fourth-layer checks may cost
more, and final-key checks are additional. They do not establish a
scalable full certificate. No mass generation should proceed from these
measurements alone.

## Cancelled architecture gate (do not execute)

A bounded q=2 / p=1 measurement with actual late-layer histories and critical
terminal potentials is recorded in `scale_pilot/sector-scale-feasibility-2026-09-27.md`.
The local Lean checks passed, including an independent deleted-prefix control,
but the measured literal/tree format still does not establish feasible
all-sector kernel replay. The mass-export gate remains closed.

Before exporting all sectors or catalogue states, find a certificate whose
verification work is demonstrably smaller than re-running the search:

- A symbolic exclusion or covering certificate for whole families of
  auxiliary sets, with a Lean proof that every omitted branch cannot be
  `Catalogued`, could replace per-state replay. A SAT-style proof is another
  candidate only if its encoding and proof checker are themselves proved
  faithful in Lean. Neither exists yet.
- Benchmark the proposed checker on a representative complete transpose
  prefix block and on at least one q=2 and one p=1 sector. Record generation,
  elaboration, kernel checking, import I/O, peak RAM and disk separately.
  Estimate the full two-orientation and all-sector cost from measured work,
  not from declaration count.
- If no compact certificate is found, retain the accepted partial Lean
  theory and state the computational limit explicitly. Do not report the
  fixed-matrix minimum as formally proved.
