import Foundation
//import Dispatch

import Utils
import Automata
import Specification
import TransitionSystem
import BoundedSynthesis

import CAiger



var options = BoSyOptions()

do {
    try options.parseCommandLine()
} catch {
    print(error)
    options.printHelp()
    exit(1)
}

let fileContents: String

let parseTimer = options.statistics?.startTimer(phase: .parsing)

var fileFormat: SupportedFileFormats = .bosy

if let specificationFile = options.specificationFile {
    Logger.default().debug("reading from file \"\(specificationFile)\"")
    guard let specficationString = try? String(contentsOfFile: specificationFile, encoding: String.Encoding.utf8) else {
        print("error: cannot read input file \(specificationFile)")
        exit(1)
    }
    fileContents = specficationString
    if specificationFile.hasSuffix(".tlsf") {
        fileFormat = .tlsf
    }
} else {
    // Read from stdin
    let standardInput = FileHandle.standardInput
    
    Logger.default().debug("reading from stdin")
    
    let input = StreamHelper.readAllAvailableData(from: standardInput)
    
    guard let specficationString = String(data: input, encoding: String.Encoding.utf8) else {
        print("error: cannot read input from stdin")
        exit(1)
    }
    fileContents = specficationString
}

var specification: SynthesisSpecification

switch fileFormat {
case .bosy:
    guard let s = SynthesisSpecification.fromJson(string: fileContents) else {
        print("error: cannot parse specification")
        exit(1)
    }
    specification = s
case .tlsf:
    guard let s = SynthesisSpecification.from(tlsf: fileContents) else {
        print("error: cannot parse specification")
        exit(1)
    }
    specification = s
}

parseTimer?.stop()

// override semantics if given as command line argument
if let semantics = options.semantics {
    specification.semantics = semantics
}

//Logger.default().info("inputs: \(specification.inputs), outputs: \(specification.outputs)")
//Logger.default().info("assumptions: \(specification.assumptions), guarantees: \(specification.guarantees)")

private func buildAutomaton(player: Player) -> CoBüchiAutomaton? {
    Logger.default().debug("start building automaton for player \(player)")
    if options.monolithic || player == .environment || specification.assumptions.count > 0 {
        let assumptionString = specification.assumptions.flatMap( { $0.ltl3ba } ).joined(separator: " && ")
        let guaranteeString = specification.guarantees.flatMap( { $0.ltl3ba } ).joined(separator: " && ")
        
        let ltlSpec: String
        if player == .system {
            ltlSpec = specification.assumptions.count == 0 ? "!(\(guaranteeString))" : "!((\(assumptionString)) -> (\(guaranteeString)))"
        } else {
            assert(player == .environment)
            ltlSpec = specification.assumptions.count == 0 ? "\(guaranteeString)" : "(\(assumptionString)) -> (\(guaranteeString))"
        }
        
        let automatonTimer = options.statistics?.startTimer(phase: .ltl2automaton)
        guard let automaton = options.converter.convert(ltl: ltlSpec) else {
            Logger.default().error("could not construct automaton")
            return nil
        }
        automatonTimer?.stop()
        Logger.default().debug("building automaton for player \(player) succeeded")
        return automaton
    } else {
        assert(specification.assumptions.count == 0)
        assert(player == .system)
        
        var automata: [CoBüchiAutomaton] = []
        for guarantee in specification.guarantees {
            let automatonTimer = options.statistics?.startTimer(phase: .ltl2automaton)
            guard let ltl3baDescription = guarantee.ltl3ba else {
                Logger.default().error("could not convert guarantees to ltl3ba format")
                return nil
            }
            guard let automaton = options.converter.convert(ltl: "!(\(ltl3baDescription))") else {
                Logger.default().error("could not construct automaton")
                return nil
            }
            automatonTimer?.stop()
            automata.append(automaton)
        }
        
        Logger.default().debug("building automaton for player \(player) succeeded")
        
        return CoBüchiAutomaton(automata: automata)
    }
}

private func getEncoding(strategy: SearchStrategy, player: Player) -> (() -> ()) {
    return {
        guard let automaton = buildAutomaton(player: player) else {
            return
        }

        Logger.default().info("automaton contains \(automaton.states.count) states")

        var search = SolutionSearch(options: options, specification: specification, automaton:
            automaton, searchStrategy: strategy, player: player, backend: options.backend,
            initialBound: options.minBound, synthesize: false)

        if let solution = search.getSolutionEncoding() {
            if player == .system {
                print(solution)
            } else {
                print("unrealizable")
            }
        }
    }
}

private func getSynthesis(search: SolutionSearch) -> () {

    guard let solution = search.getSolution() else {
        Logger.default().error("could not construct solution")
        return
    }
    switch options.target {
    case .aiger:
        guard let aiger_solution = (solution as? AigerRepresentable)?.aiger else {
            Logger.default().error("could not encode solution as AIGER")
            return
        }
        let minimized = aiger_solution.minimized
        aiger_write_to_file(minimized, aiger_ascii_mode, stdout)
    case .dot:
        guard let dot = (solution as? DotRepresentable)?.dot else {
            Logger.default().error("could not encode solution as dot")
            return
        }
        print(dot)
    case .dotTopology:
        guard let dot = (solution as? DotRepresentable)?.dotTopology else {
            Logger.default().error("could not encode solution as dot")
            return
        }
        print(dot)
    case .smv:
        guard let smv = (solution as? SmvRepresentable)?.smv else {
            Logger.default().error("could not encode solution as SMV")
            return
        }
        print(smv)
    case .verilog:
        guard let verilog = (solution as? VerilogRepresentable)?.verilog else {
            Logger.default().error("could not encode solution as Verilog")
            return
        }
        print(verilog)
    case .all:
        var result: [String:String] = [:]
        guard let dotSolution = solution as? DotRepresentable else {
            Logger.default().error("could not encode solution as dot")
            return
        }
        result["dot"] = dotSolution.dot
        result["dot-topology"] = dotSolution.dotTopology
        guard let smv = (solution as? SmvRepresentable)?.smv else {
            Logger.default().error("could not encode solution as SMV")
            return
        }
        result["smv"] = smv
        guard let verilog = (solution as? VerilogRepresentable)?.verilog else {
            Logger.default().error("could not encode solution as Verilog")
            return
        }
        result["verilog"] = verilog
        guard let jsonData = try? JSONSerialization.data(withJSONObject: result) else {
            Logger.default().error("could not encode solution JSON")
            return
        }
        guard let jsonString = String(data: jsonData, encoding: .utf8) else {
            Logger.default().error("could not encode solution JSON")
            return
        }
        print(jsonString)
    }
}

private func getRepresentation() -> (() -> ()) {

    return {
        guard let model = specification.model else {
            Logger.default().error("no model to inject")
            exit(1)
        }

        // dummy
        let automaton = CoBüchiAutomaton(initialStates: [], states: [], transitions: [:],
            safetyConditions: [:], rejectingStates: [])

        var search = SolutionSearch(options: options, specification: specification, automaton:
            automaton, backend: options.backend, initialBound: options.minBound, synthesize: false)

        do {
            try search.injectModel(model: model)
        } catch {
            Logger.default().error("could not inject model: \(error)")
            exit(1)
        }

        getSynthesis(search: search)
    }

}

func search(strategy: SearchStrategy, player: Player, synthesize: Bool, encodingOnly: Bool) -> (() -> ()) {
    Logger.default().debug("start search strategy (strategy: \"\(strategy)\", player: \"\(player)\", synthesize: \(synthesize), encodingOnly: \(encodingOnly))")
    if encodingOnly {
        return getEncoding(strategy: strategy, player: player)
    }

    if options.fromModel {
        return getRepresentation()
    }

    return {
        guard let automaton = buildAutomaton(player: player) else {
            return
        }

        Logger.default().info("automaton contains \(automaton.states.count) states")

        let synthesize = synthesize && !(player == .environment && options.syntcomp2017rules)
        
        var search = SolutionSearch(options: options, specification: specification, automaton: automaton, searchStrategy: strategy, player: player, backend: options.backend, initialBound: options.minBound, synthesize: synthesize)

        if search.hasSolution(limit: options.maxBound ?? Int.max) {
            if !synthesize {
                player == .system ? print("result: realizable") : print("result: unrealizable")
                return
            }

            getSynthesis(search: search)
            return
        }
        print("result: unknown")
    }
}

//search(strategy: options.searchStrategy, player: .system, synthesize: options.synthesize)()

let condition = NSCondition()
var finished = false


let searchSystem = search(strategy: options.searchStrategy, player: .system, synthesize:
    options.synthesize, encodingOnly: options.encodingOnly)
let searchEnvironment = search(strategy: options.searchStrategy, player: .environment, synthesize:
    options.synthesize, encodingOnly: options.encodingOnly)

let doSearchSystem = options.player.contains(.system)
let doSearchEnvironment = options.player.contains(.environment)

#if os(Linux)
let thread1 = Thread() {
    searchSystem()
    condition.lock()
    finished = true
    condition.broadcast()
    condition.unlock()
}
let thread2 = Thread() {
    searchEnvironment()
    condition.lock()
    finished = true
    condition.broadcast()
    condition.unlock()
}
if doSearchSystem {
    thread1.start()
}
if doSearchEnvironment {
    thread2.start()
}
#else
    class ThreadedExecution: Thread {
        
        let function: () -> ()
        
        init(function: @escaping (() -> ())) {
            self.function = function
        }
        
        override func main() {
            function()
            condition.lock()
            finished = true
            condition.broadcast()
            condition.unlock()
        }
    }
if doSearchSystem {
    ThreadedExecution(function: searchSystem).start()
}
if doSearchEnvironment {
    ThreadedExecution(function: searchEnvironment).start()
}
#endif

condition.lock()
if !finished {
    condition.wait()
}
condition.unlock()

if let statistics = options.statistics {
    print(statistics.description)
}


