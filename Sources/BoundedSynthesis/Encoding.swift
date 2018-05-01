
import TransitionSystem

enum BoSyEncodingError: Error {
    case EncodingFailed(String)
    case SolvingFailed(String)
}

protocol BoSyEncoding {
    
    mutating func solve(forBound bound: Int) throws -> String?
    func extractSolution() -> TransitionSystem?
    
}
