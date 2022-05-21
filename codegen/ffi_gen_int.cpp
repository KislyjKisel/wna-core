#include <iostream>
#include <cstring>
#include <fstream>
#include <filesystem>
#include <functional>
#include "ffi_gen.h"

struct F {
    const char* const name;
    const char* const qhsname;
    const char* const type; // use {0} as T: T -> T  =>  {0} -> {0}

    void declare(AgdaModule& m, const std::string_view domain) const {
        if(name[0] == '\0') {
            m.blank();
            if(type[0] != '\0') m.comment(type);
            return;
        }
        m.declare(name, fmt::format(type, domain));
    }

    void define(AgdaModule& m) const {
        if(name[0] == '\0') {
            m.blank();
            if(type[0] != '\0') m.comment(type);
            return;
        }
        if(qhsname[0] == '\0') {
            // only decl
            return;
        }
        m.ffi_hs_define(name, qhsname);
    }
};

constexpr const char* ftT       = "{0}";
constexpr const char* ftT_T     = "{0} -> {0}";
constexpr const char* ftT_T_T   = "{0} -> {0} -> {0}";
constexpr const char* ftT_T_TxT = "{0} -> {0} -> Pair {0} {0}";
constexpr const char* ftT_T_B   = "{0} -> {0} -> Bool";
constexpr const char* ftT_T_O   = "{0} -> {0} -> Ordering";
constexpr const char* ftT_I     = "{0} -> ℤ";
constexpr const char* ftI_T     = "ℤ -> {0}";
constexpr const char* ftT_i     = "{0} -> Int";
constexpr const char* ftT_F     = "{0} -> Float";
constexpr const char* ftT_i_T   = "{0} -> Int -> {0}";

constexpr F fs_base[] = {
    { "", "", "Num" },
    { "show", "Prelude.show", "{0} -> List Char" },
    
    { "", "", "Num" },
    { "_+_", "(Prelude.+)", ftT_T_T },
    { "_-_", "(Prelude.-)", ftT_T_T },
    { "_*_", "(Prelude.*)", ftT_T_T },
    { "_^_", "(Prelude.^)", ftT_T_T },
    { "negate", "Prelude.negate", ftT_T },
    { "abs",    "Prelude.abs",    ftT_T },
    { "fromℤ", "Prelude.fromInteger", ftI_T },

    { "", "", "Enum" },
    { "succ", "Prelude.succ", ftT_T },
    { "pred", "Prelude.pred", ftT_T },


    { "", "", "Eq" },
    { "_==_", "(Prelude.==)", ftT_T_B },
    { "_/=_", "(Prelude./=)", ftT_T_B },

    { "", "", "Ord" },
    { "compare", "Prelude.compare", ftT_T_O },
    { "_<_",  "(Prelude.<)",  ftT_T_B },
    { "_≤_", "(Prelude.<=)", ftT_T_B },
    { "_>_",  "(Prelude.>)",  ftT_T_B },
    { "_≥_", "(Prelude.>=)", ftT_T_B },
    { "_⊓_",  "Prelude.min",  ftT_T_T },
    { "_⊔_",  "Prelude.max",  ftT_T_T },

    { "", "", "Bounded" },
    { "minBound", "Prelude.minBound", ftT },
    { "maxBound", "Prelude.maxBound", ftT },

    { "", "", "Integral" },
    { "_quot_", "Prelude.quot", ftT_T_T },
    { "_rem_",  "Prelude.rem",  ftT_T_T },
    { "_div_",  "Prelude.div",  ftT_T_T },
    { "_mod_",  "Prelude.mod",  ftT_T_T },
    { "_quotRem_", "Prelude.quotRem", ftT_T_TxT },
    { "_divMod_",  "Prelude.divMod",  ftT_T_TxT },
    { "toℤ", "Prelude.toInteger", ftT_I },
    { "toFloat", "Prelude.fromIntegral", ftT_F },

    { "", "", "Bits" },
    { "_xor_", "Data.Bits.xor",    ftT_T_T },
    { "_∙∣∙_", "(Data.Bits..|.)",  ftT_T_T },
    { "_∙&∙_", "(Data.Bits..&.)",  ftT_T_T },
    { "complement", "Data.Bits.complement", ftT_T },
    { "popCount", "Data.Bits.popCount", ftT_i },
    { "shift", "Data.Bits.shift", ftT_i_T },
    { "rotate", "Data.Bits.rotate", ftT_i_T },

    { "", "", "FiniteBits"},
    { "bitSize", "Data.Bits.finiteBitSize", ftT_i },
    { "countLeadingZeros", "Data.Bits.countLeadingZeros", ftT_i },
    { "countTrailingZeros", "Data.Bits.countTrailingZeros", ftT_i },

    { "", "", "" },
    { "fromℕ", "Prelude.fromInteger", "ℕ -> {0}" },
};

struct TypeInfo {
    const char* name;
    const char* hs_module;
    std::function<void(AgdaModule&)> extra_imports = [](auto&){};
    std::function<void(AgdaModule&, const char*)> extra_defs = [](auto&, auto){};

    void declare(AgdaModule& m) const {
        m.declare(name, "Type");
    }
    void define(AgdaModule& m) const {
        m.ffi_hs_define(name, fmt::format("type {0}.{1}", hs_module, name));
    }
};

auto extra_nothing = [](auto&){};

auto extra_IntN_imports = [](AgdaModule& m) {
    m.import("Wna.Foreign.Haskell.Base.Data.Int.Base").open().use("Int; ℕ⇒+Int; ℕ⇒-Int");
};

auto extra_IntN_defs = [](AgdaModule& m, const char* tname) {
    m.blank();
    m.declare("shiftL", fmt::format("{0} -> ℕ -> {0}", tname));
    m.define("shiftL x n", "shift x (ℕ⇒+Int n)");

    m.blank();
    m.declare("rotateL", fmt::format("{0} -> ℕ -> {0}", tname));
    m.define("rotateL x n", "rotate x (ℕ⇒+Int n)");

    m.blank();
    m.declare("shiftR", fmt::format("{0} -> ℕ -> {0}", tname));
    m.define("shiftR x n", "shift x (ℕ⇒-Int n)");

    m.blank();
    m.declare("rotateR", fmt::format("{0} -> ℕ -> {0}", tname));
    m.define("rotateR x n", "rotate x (ℕ⇒-Int n)");
};

auto extra_Int_defs = [](AgdaModule& m, const char* tname) {
    m.blank();
    m.declare("ℕ⇒+Int", "ℕ → Int");
    m.define("ℕ⇒+Int n", "fromℤ (+ n)");

    m.blank();
    m.declare("ℕ⇒-Int", "ℕ → Int");
    m.define("ℕ⇒-Int n", "fromℤ (- (+ n))");

    extra_IntN_defs(m, tname);
};

auto extra_Word_imports = [](AgdaModule& m) {
    extra_IntN_imports(m);
};
auto extra_Word_defs = [](AgdaModule& m, const char* tname) {
    extra_IntN_defs(m, tname);

    m.blank();
    m.block(Block::Postulate, [tname](AgdaModule& mb){ 
        mb.declare("toℕ", fmt::format("{} -> ℕ", tname));
    });
    m.blank();
    m.ffi_hs_define("toℕ", "Prelude.toInteger");
};
auto extra_WordN_imports = [](AgdaModule& m) {
    extra_IntN_imports(m);
};
auto extra_WordN_defs = [](AgdaModule& m, const char* tname) {
    extra_Word_defs(m, tname);
};

TypeInfo ts_int[] = {
    { "Int",   "Data.Int", extra_nothing, extra_Int_defs },
    { "Int8",  "Data.Int", extra_IntN_imports, extra_IntN_defs },
    { "Int16", "Data.Int", extra_IntN_imports, extra_IntN_defs },
    { "Int32", "Data.Int", extra_IntN_imports, extra_IntN_defs },
    { "Int64", "Data.Int", extra_IntN_imports, extra_IntN_defs },

    { "Word",   "Data.Word", extra_Word_imports, extra_Word_defs },
    { "Word8",  "Data.Word", extra_WordN_imports, extra_WordN_defs },
    { "Word16", "Data.Word", extra_WordN_imports, extra_WordN_defs },
    { "Word32", "Data.Word", extra_WordN_imports, extra_WordN_defs },
    { "Word64", "Data.Word", extra_WordN_imports, extra_WordN_defs },
};

template<std::ranges::range T> requires std::same_as<F, std::decay_t<std::ranges::range_value_t<T>>>
void decldeffs(AgdaModule& m, std::string_view domain, T&& fr) {
    m.block(Block::Postulate, [&, domain](AgdaModule& mb){
        for(auto& f : fr) {
            f.declare(m, domain);
        }
    });
    m.blank();
    for(auto& f : fr) {
        f.define(m);
    }
}

int main() {
    std::cout << "FFI Integers\n";
    constexpr const char* prefix = "Wna.Foreign.Haskell.Base.Data.";
    const auto dir = std::filesystem::path("../src");

    for(const auto& t : ts_int) {
        AgdaModule m{ dir, fmt::format("{0}{1}.Base", prefix, t.name), "--without-K" };
        
        m.import("Data.Bool.Base").open().use("Bool");
        m.import("Data.Float.Base").open().use("Float");
        m.import("Data.Integer.Base").open().use("ℤ").use("+_").use("-_");
        m.import("Data.Nat.Base").open().use("ℕ");
        m.import("Foreign.Haskell.Pair").open().use("Pair");
        m.import("Wna.Foreign.Haskell.Base.Data.Ordering.Base").open().use("Ordering");
        m.import("Wna.Primitive").open();
        m.import("Data.List.Base").open().use("List");
        m.import("Data.Char.Base").open().use("Char");
        t.extra_imports(m);
        m.blank(1);
        m.ffi_hs_import(t.hs_module);
        //m.ffi_hs("\n    import qualified Prelude\n   import Prelude (Integer)\n");
        m.ffi_hs_import("Data.Bits");
        
        m.blank(2);
        m.block(Block::Postulate, [&t](AgdaModule& mb){
            t.declare(mb);
        });
        m.blank();
        t.define(m);

        m.blank(2);
        decldeffs(m, t.name, fs_base);

        m.blank(1);
        t.extra_defs(m, t.name);
    }

    return 0;
}
