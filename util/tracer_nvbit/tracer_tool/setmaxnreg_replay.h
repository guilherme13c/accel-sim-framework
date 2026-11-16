#ifndef SETMAXNREG_REPLAY_H
#define SETMAXNREG_REPLAY_H

#include <cstdio>
#include <fstream>
#include <map>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

// Header extension v1. PCs are function-relative, hexadecimal. The descriptor
// certifies a straight-line retry body that is safe to repeat; its branch
// retries on allocation failure. It does not prescribe instruction positions or
// size.
namespace setmaxnreg_replay {
struct instruction {
  unsigned pc;
  std::string sass;
};
struct region {
  unsigned entry, allocation, branch, exit;
  std::string header() const {
    char line[160];
    std::snprintf(line, sizeof(line), "-setmaxnreg replay = 1 %x %x %x %x",
                  entry, allocation, branch, exit);
    return line;
  }
};

inline std::vector<std::string> tokens(std::string sass) {
  for (char &c : sass)
    if (c == ',' || c == ';') c = ' ';
  std::istringstream in(sass);
  std::vector<std::string> out;
  std::string word;
  while (in >> word) out.push_back(word);
  return out;
}

inline unsigned number(const std::string &s) {
  size_t end = 0;
  unsigned long n = std::stoul(s, &end, 0);
  if (end != s.size() || n > 0xffffffffUL)
    throw std::runtime_error("invalid SASS address or immediate");
  return static_cast<unsigned>(n);
}

inline std::vector<region> analyze(const std::vector<instruction> &code) {
  std::vector<region> regions;
  bool has_allocation = false;
  for (const auto &ins : code)
    has_allocation |=
        ins.sass.find("USETMAXREG.TRY_ALLOC") != std::string::npos;
  if (!has_allocation) return regions;
  std::map<unsigned, size_t> by_pc;
  for (size_t i = 0; i < code.size(); ++i)
    if (!by_pc.emplace(code[i].pc, i).second)
      throw std::runtime_error("duplicate function PCs in allocation SASS");
  for (size_t b = 0; b < code.size(); ++b) {
    auto branch = tokens(code[b].sass);
    if (branch.size() != 3 || branch[0].compare(0, 3, "@!P") != 0 ||
        branch[1] != "BRA")
      continue;
    unsigned target = number(branch[2]);
    auto found = by_pc.find(target);
    if (found == by_pc.end() || found->second >= b) continue;
    size_t entry = found->second;
    size_t alloc = code.size();
    for (size_t i = entry; i < b; ++i)
      if (code[i].sass.find("USETMAXREG.TRY_ALLOC.CTAPOOL") !=
          std::string::npos) {
        if (alloc != code.size())
          throw std::runtime_error("multiple allocations in retry region");
        alloc = i;
      }
    if (alloc == code.size()) continue;  // unrelated loop
    if (b + 1 == code.size())
      throw std::runtime_error("allocation loop has no exit");
    auto attempt = tokens(code[alloc].sass);
    if (attempt.size() != 3 || attempt[0] != "USETMAXREG.TRY_ALLOC.CTAPOOL" ||
        !std::regex_match(attempt[1], std::regex("UP[0-9]+")))
      throw std::runtime_error("unsupported allocation predicate producer");
    unsigned limit = number(attempt[2]);
    if (limit < 24 || limit > 256 || limit % 8)
      throw std::runtime_error("invalid allocation target");
    std::string result_predicate;
    bool synchronized = false;
    for (size_t i = entry; i < b; ++i) {
      auto t = tokens(code[i].sass);
      if (t.empty()) throw std::runtime_error("empty allocation instruction");
      if (i == alloc) continue;
      // These operations neither change data values nor add side effects that
      // would be duplicated when the simulator executes additional attempts.
      if (t[0] == "NOP" || t[0] == "DEPBAR.LE") continue;
      if (t[0] == "WARPSYNC.ALL") {
        if (i < alloc) synchronized = true;
        continue;
      }
      // Verify the dataflow and truth table: P = allocation success. This is
      // a semantic constraint, independent of intervening synchronization ops.
      if (i > alloc && t.size() == 8 && t[0] == "PLOP3.LUT" &&
          std::regex_match(t[1], std::regex("P[0-9]+")) && t[2] == "PT" &&
          t[3] == "PT" && t[4] == "PT" && t[5] == attempt[1] &&
          number(t[6]) == 0x80 && number(t[7]) == 0 &&
          result_predicate.empty()) {
        result_predicate = t[1];
        continue;
      }
      throw std::runtime_error(
          "unsupported side effect or predicate dataflow in allocation loop");
    }
    if (!synchronized || result_predicate.empty() ||
        branch[0] != "@!" + result_predicate)
      throw std::runtime_error(
          "allocation retry branch is not failure-controlled");
    region r{target, code[alloc].pc, code[b].pc, code[b + 1].pc};
    for (const auto &prior : regions)
      if (r.entry <= prior.branch && prior.entry <= r.branch)
        throw std::runtime_error("overlapping allocation regions");
    // Reject branches into the interior; the header describes one entry.
    for (const auto &ins : code) {
      auto t = tokens(ins.sass);
      size_t op = !t.empty() && t[0][0] == '@' ? 1 : 0;
      if (t.size() == op + 2 && t[op] == "BRA") {
        unsigned dest = number(t[op + 1]);
        if (dest > r.entry && dest <= r.branch)
          throw std::runtime_error("branch into allocation region interior");
      }
    }
    regions.push_back(r);
  }
  // Never silently record an allocation for which replay cannot be described.
  for (const auto &ins : code)
    if (ins.sass.find("USETMAXREG.TRY_ALLOC") != std::string::npos) {
      bool covered = false;
      for (const auto &r : regions) covered |= r.allocation == ins.pc;
      if (!covered)
        throw std::runtime_error(
            "TRY_ALLOC has no supported failure-controlled retry region");
    }
  return regions;
}

// cuobjdump --dump-sass output; instruction encoding-only lines are ignored.
inline std::map<std::string, std::vector<region>> read_sass(
    const std::string &path) {
  std::ifstream in(path);
  if (!in) throw std::runtime_error("cannot open SASS file: " + path);
  std::map<std::string, std::vector<instruction>> functions;
  std::string line, name;
  const std::regex function("Function : ([^[:space:]]+)");
  const std::regex inst("/\\*([0-9a-fA-F]+)\\*/[[:space:]]+([^;]+);");
  std::smatch match;
  while (std::getline(in, line)) {
    if (std::regex_search(line, match, function))
      name = match[1];
    else if (!name.empty() && std::regex_search(line, match, inst))
      functions[name].push_back(
          {static_cast<unsigned>(std::stoul(match[1], nullptr, 16)), match[2]});
  }
  std::map<std::string, std::vector<region>> result;
  for (const auto &f : functions) result.emplace(f.first, analyze(f.second));
  if (result.empty())
    throw std::runtime_error("no functions found in SASS file");
  return result;
}
}  // namespace setmaxnreg_replay
#endif
