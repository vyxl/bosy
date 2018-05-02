
import TransitionSystem

enum BoSyEncodingError: Error {
    case EncodingFailed(String)
    case SolvingFailed(String)
    case Unimplemented(String)
}

protocol BoSyEncoding {
    
    mutating func solve(forBound bound: Int) throws -> String?
    func extractSolution() -> TransitionSystem?
    func injectModel(model: String) throws -> ()
    
}
