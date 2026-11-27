module

import CasRuntime.ApplicationLogTests
import CasCatalogue.TestSuite
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.ApplicationLogTests
meta import CasCatalogue.TestSuite
meta import LeanCategories.Catalogue

namespace CasRuntime.SessionLogTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue CasCatalogue.Backend




run_cmd do
  for peer in #[true, false] do
    ApplicationLogTests.runOriginalFile peer fun completed original rows events manifest => do
      let dataOf (event : Json) : Json := (event.getObjVal? "data").toOption.getD .null
      let isEvent (name : String) (event : Json) : Bool :=
        (event.getObjValAs? String "event").toOption == some name
      let hasParent (sequence : Nat) (event : Json) : Bool :=
        ((event.getObjValAs? (Array Nat) "parents").toOption.getD #[]).contains sequence
      let .ok registrations := manifest.getObjValAs? (Array Json) "registrations"
        | throwError "the original session log control lost its actual manifest"
      unless registrations.size == (if peer then 1 else 0) do
        throwError "the original session log control changed its permitted registrations"
      let mut required : Array (Nat × Option Name × String) := #[]
      for item in original.items, ordinal in [:original.items.size] do
        match item with
        | `(cas_item| let $name:ident := $_:cas_term) =>
          if #[`A, `f, `g].contains name.getId then
            required := required.push (ordinal, some name.getId, name.getId.toString)
        | `(cas_item| test $id:ident $_:str : $_:cas_stmt) =>
          if id.getId.toString == "sets.limit.pullback.card" then
            required := required.push (ordinal, none, id.getId.toString)
        | _ => pure ()
      unless required.size == 4 do
        throwError "the unchanged original file lost A, f, g, or its pullback assertion"
      for (ordinal, definition, label) in required do
        let #[computation] := events.filter fun event =>
          isEvent "computation.started" event &&
            ((dataOf event).getObjValAs? Nat "ordinal").toOption == some ordinal
          | throwError "the original item lost its computation: {label}"
        let .ok computationSequence := computation.getObjValAs? Nat "sequence"
          | throwError "the original item lost its causal identity: {label}"
        let entered := events.filter (hasParent computationSequence)
        let #[terminal] := (entered.filter (isEvent "statement.finished")).map dataOf
          | throwError "the original item lost its completed outcome: {label}"
        unless (entered.filter (isEvent "statement.interrupted")).isEmpty &&
            (terminal.getObjValAs? Bool "attempted").toOption == some true do
          throwError "the required original item did not complete its execution boundary: {label}"
        let .ok kind := terminal.getObjValAs? String "kind"
          | throwError "the original item lost its outcome kind: {label}"
        let .ok stratum := terminal.getObjValAs? (Option String) "stratum"
          | throwError "the original item lost its classified outcome: {label}"
        unless (kind == "holds" && stratum.isNone) ||
            (kind == "gap" && stratum == some "noImplementation") do
          throwError "the original item did not reach its supported or unregistered execution: {label}: {terminal}"
        let #[reading] := (entered.filter (isEvent "statement.read")).map dataOf
          | throwError "the original item lost its one selected reading: {label}"
        let .ok conclusions := reading.getObjValAs? (Array Json) "conclusions"
          | throwError "the original item lost its native conclusions: {label}"
        unless !conclusions.isEmpty do
          throwError "the original item lost its complete typed interpretation: {label}"
        let #[timing] := (entered.filter (isEvent "computation.timing")).map dataOf
          | throwError "the original item lost its retained root report: {label}"
        let .ok result := timing.getObjVal? "result"
          | throwError "the original item lost its unchanged outcome: {label}"
        unless (result.getObjVal? "conclusions").toOption == some (toJson conclusions) do
          throwError "the reading changed before the original result was reported: {label}"
        if let some name := definition then
          unless (reading.getObjValAs? String "kind").toOption == some "definition" do
            throwError "an original definition was relabeled as another reading: {label}"
          let #[binding] := completed.source.context.entries.filter fun entry =>
            entry.role == .definition && entry.userName == name
            | throwError "the original definition lost its retained source identity: {label}"
          let .ok scope := reading.getObjVal? "scope"
            | throwError "the original definition lost its complete source context: {label}"
          let .ok context := scope.getObjValAs? (Array Json) "context"
            | throwError "the original definition lost its ordered source telescope: {label}"
          let id := ContextSnapshot.bindingJson binding.id
          let #[sourceEntry] := context.filter fun entry =>
            (entry.getObjVal? "id").toOption == some id
            | throwError "the original definition changed its source identity after reading: {label}"
          unless (sourceEntry.getObjValAs? String "name").toOption ==
              some (name.toString (escape := false)) do
            throwError "the original source binding changed its authored name: {label}"
          let .ok retained := terminal.getObjValAs? (Array Json) "retained"
            | throwError "the original definition lost its retained-binding log: {label}"
          let #[retained] := retained.filter fun entry =>
            (entry.getObjVal? "binding").toOption == some id
            | throwError "the original definition lost its actual retained binding: {label}"
          let actual := toJson ((completed.value? binding.id).map Observation.valueIdentityJson)
          unless (retained.getObjVal? "value").toOption == some actual do
            throwError "the log replaced the original definition's actual value: {label}"
          let retainedEvents := (entered.filter (isEvent "binding.retained")).map dataOf
          if kind == "holds" then
            let #[retainedEvent] := retainedEvents.filter fun entry =>
              (entry.getObjVal? "binding").toOption == some id
              | throwError "the original successful definition lost its binding event: {label}"
            unless (retainedEvent.getObjVal? "value").toOption == some actual &&
                (retainedEvent.getObjValAs? Bool "computed").isOk do
              throwError "the binding event replaced an actual value or its computation status: {label}"
          else
            unless actual == Json.null && retainedEvents.isEmpty do
              throwError "an unavailable original definition acquired a fabricated value: {label}"
            let #[unavailable] := (entered.filter (isEvent "binding.unavailable")).map dataOf
              | throwError "the original unavailable definition lost its retained failure: {label}"
            unless (unavailable.getObjVal? "binding").toOption == some id do
              throwError "the unavailable definition changed its actual source identity: {label}"
            for field in #["kind", "stratum", "detail"] do
              unless (unavailable.getObjVal? field).toOption ==
                  (terminal.getObjVal? field).toOption do
                throwError "the unavailable definition changed its original outcome {field}: {label}"
        else
          let #[row] := rows.filter (·.id == label)
            | throwError "the original pullback assertion lost its public result"
          unless row.attempted && !row.question.isEmpty && !row.conclusions.isEmpty &&
              toJson row == result do
            throwError "the original pullback assertion lost its unchanged typed report"
        for prepared in entered.filter (isEvent "request.prepared") do
          let .ok native := (dataOf prepared).getObjVal? "native"
            | throwError "an original prepared request lost its native observation: {label}"
          let .ok request := native.getObjVal? "request"
            | throwError "an original preparation lost its complete request: {label}"
          unless (native.getObjVal? "nativeExpressions").isOk do
            throwError "an original preparation lost its native expression table: {label}"
          for field in #["program", "occurrence", "action", "source", "scope", "outputs",
              "environment", "origin", "roles", "actualArguments"] do
            unless (request.getObjVal? field).isOk do
              throwError "an original preparation lost {field}: {label}"
          let .ok action := request.getObjVal? "action"
            | throwError "an original preparation lost its action address: {label}"
          unless (action.getObjValAs? String "kind").isOk do
            throwError "an original preparation lost its typed action: {label}"
        for executed in entered.filter (isEvent "request.execute") do
          let .ok sequence := executed.getObjValAs? Nat "sequence"
            | throwError "an original execution lost its causal identity: {label}"
          let .ok native := (dataOf executed).getObjVal? "native"
            | throwError "an original execution lost its complete native request: {label}"
          unless events.any (fun event => isEvent "request.prepared" event &&
              ((event.getObjValAs? Nat "sequence").toOption.any (· < sequence)) &&
              ((dataOf event).getObjVal? "native").toOption == some native) do
            throwError "an original execution lost its exact prior preparation: {label}"
        for dispatch in entered.filter (isEvent "dispatch") do
          let data := dataOf dispatch
          let .ok selected := data.getObjVal? "selected"
            | throwError "an original dispatch lost its actual selection: {label}"
          if (selected.getObjValAs? String "kind").toOption == some "registration" then
            unless registrations.any (fun registration =>
                #["operation", "input", "backend"].all fun field =>
                  (registration.getObjVal? field).toOption ==
                    (selected.getObjVal? field).toOption) do
              throwError "an original dispatch used a registration absent from this manifest: {label}"
          else
            unless (selected.getObjValAs? String "kind").toOption == some "native" &&
                (selected.getObjVal? "value").isOk do
              throwError "an original dispatch lost its explicit native selection: {label}"
          unless (data.getObjVal? "operands").isOk do
            throwError "an original dispatch lost its actual operands: {label}"
          let .ok request := data.getObjVal? "request"
            | throwError "an original dispatch lost its prepared request: {label}"
          let .ok native := request.getObjVal? "native"
            | throwError "an original dispatch lost its complete native request: {label}"
          unless events.any (fun event => isEvent "request.prepared" event &&
              ((dataOf event).getObjVal? "native").toOption == some native) do
            throwError "an original dispatch replaced its actual prepared request: {label}"
          let .ok occurrence := data.getObjVal? "occurrence"
            | throwError "an original dispatch lost its actual occurrence: {label}"
          for phase in #["reply.admission.started", "reply.admitted"] do
            unless entered.any (fun event => isEvent phase event &&
                ((dataOf event).getObjVal? "occurrence").toOption == some occurrence) do
              throwError "an actual supported peer reply lost {phase}: {label}"
        let mut cause := entered
        let mut missing := cause.filter (isEvent "realization.missing")
        if stratum == some "noImplementation" then
          let mut visited : Array Json := #[]


          while missing.isEmpty do
            let #[dependency] := cause.filter (isEvent "dependency.unavailable")
              | throwError "the original failure lost its actual request or retained dependency: {label}"
            let .ok dependencySequence := dependency.getObjValAs? Nat "sequence"
              | throwError "the retained dependency lost its causal identity: {label}"
            let .ok binding := (dataOf dependency).getObjVal? "binding"
              | throwError "the retained dependency lost its exact source binding: {label}"
            unless !visited.contains binding do
              throwError "the retained dependency log contains a causal cycle: {label}"
            visited := visited.push binding
            unless ((dataOf dependency).getObjValAs? String "stratum").toOption ==
                some "noImplementation" do
              throwError "the dependency changed its original failure stratum: {label}"
            let #[unavailable] := events.filter fun event =>
              isEvent "binding.unavailable" event &&
                ((event.getObjValAs? Nat "sequence").toOption.any (· < dependencySequence)) &&
                ((dataOf event).getObjVal? "binding").toOption == some binding
              | throwError "the dependency lost its unique original unavailable binding: {label}"
            for field in #["name", "kind", "stratum", "detail"] do
              unless ((dataOf unavailable).getObjVal? field).toOption ==
                  ((dataOf dependency).getObjVal? field).toOption do
                throwError "the dependency changed its original retained {field}: {label}"
            let #[retainedCause] := completed.source.context.entries.filter fun entry =>
              ContextSnapshot.bindingJson entry.id == binding
              | throwError "the unavailable cause lost its actual retained source identity: {label}"
            unless (completed.value? retainedCause.id).isNone do
              throwError "an unavailable source cause acquired a fabricated computed value: {label}"
            let .ok parents := unavailable.getObjValAs? (Array Nat) "parents"
              | throwError "the unavailable binding lost its original statement: {label}"
            let #[origin] := events.filter fun event =>
              isEvent "statement.started" event &&
                (event.getObjValAs? Nat "sequence").toOption.any parents.contains
              | throwError "the unavailable binding lost its one original statement: {label}"
            let .ok originSequence := origin.getObjValAs? Nat "sequence"
              | throwError "the original unavailable statement lost its identity: {label}"
            cause := events.filter (hasParent originSequence)
            missing := cause.filter (isEvent "realization.missing")
          for event in missing do
            let data := dataOf event
            let .ok operation := data.getObjValAs? String "operation"
              | throwError "the original missing registration lost its operation: {label}"
            let .ok forms := data.getObjValAs? (Array String) "forms"
              | throwError "the original missing registration lost its input addresses: {label}"
            unless !operation.isEmpty && !forms.isEmpty && forms.all (!·.isEmpty) do
              throwError "the original no-implementation outcome has no exact address: {label}"
            unless !registrations.any (fun registration =>
                (registration.getObjValAs? String "operation").toOption == some operation &&
                  (registration.getObjValAs? String "input").toOption.any forms.contains) do
              throwError "a reported missing address has an actual registration: {label}"
            let .ok parents := event.getObjValAs? (Array Nat) "parents"
              | throwError "the missing address lost its causal request: {label}"
            unless cause.any (fun request => isEvent "request.execute" request &&
                (request.getObjValAs? Nat "sequence").toOption.any parents.contains) do
              throwError "the missing address is detached from its actual executed request: {label}"
        else
          unless missing.isEmpty do
            throwError "a successful original item retained a missing-registration outcome: {label}"

end CasRuntime.SessionLogTests
