#include <fstream>
#include <string>
#include <string_view>
#include <filesystem>
#include <ranges>
#include <map>
#include <concepts>
#include <iostream>
#include <optional>

#define FMT_HEADER_ONLY
#include <fmt/format.h>   

enum class Block {
    Private, Instance, Postulate, Module
};

const std::map<Block, const char*> blockNames = {
    { Block::Private,   "private"   },
    { Block::Instance,  "instance"  },
    { Block::Postulate, "postulate" },
    { Block::Module,    "module"    },
};

class AgdaModule {
public:
    AgdaModule(const std::filesystem::path& srcDir, std::string_view moduleName, std::string_view opts = {}) {
        auto mpath = modulePath(srcDir, std::string{moduleName});
        std::filesystem::create_directory(std::filesystem::path{mpath}.remove_filename());
        std::cout << mpath << '\n';
        m_file.open(mpath);
        m_file << "-- ! this module is generated automatically\n\n";

        if(opts.size() > 0) {
            m_file << "{-# OPTIONS " << opts << " #-}\n\n";
        }
        m_file << fmt::format("module {} where\n\n", moduleName);
    }

    auto import(std::string_view module) {
        indentation();
        return Import(m_file, module);
    }

    template<std::invocable<AgdaModule&> F>
    void block(Block b, F&& inBlock) {
        m_file << blockNames.at(b) << '\n';
        indent();
        inBlock(*this);
        unindent();
    }

    void declare(std::string_view identifier, std::string_view type) {
        indentation();
        m_file << identifier << " : " << type << '\n';
    }
    void define(std::string_view lhs, std::string_view rhs) {
        indentation();
        m_file << lhs << " = " << rhs << '\n';
    }

    void ffi_hs(std::string_view hscode) {
        m_file << fmt::format("{{-# FOREIGN GHC {} #-}}\n", hscode);
    }

    void ffi_hs_import_q(std::string_view hsmodule) {
        m_file << fmt::format("{{-# FOREIGN GHC import qualified {} #-}}\n", hsmodule);
    }

    void ffi_hs_import(std::string_view hsmodule) {
        m_file << fmt::format("{{-# FOREIGN GHC import {} #-}}\n", hsmodule);
    }

    void ffi_hs_define(std::string_view lhs, std::string_view rhs) {
        indentation();
        m_file << fmt::format("{{-# COMPILE GHC {0} = {1} #-}}\n", lhs, rhs);
    }

    void blank(int lines = 1) {
        while(lines --> 0) {
            m_file << '\n';
        }
    }

    void comment(std::string_view text) {
        indentation();
        m_file << "-- " << text << '\n';
    }

private:
    std::ofstream m_file;

    constexpr static int m_indentationStep = 2;
    int m_indentation = 0;

    void indent() {
        m_indentation += m_indentationStep;
    }
    void unindent() {
        m_indentation = std::min(0, m_indentation - m_indentationStep);
    }

    void indentation() {
        for(int i = 0; i < m_indentation; ++i) {
            m_file << ' ';
        }
    }

    static std::filesystem::path modulePath(const std::filesystem::path& dir, std::string moduleName) {
        std::ranges::transform(moduleName, moduleName.begin(), [](char c){ return c == '.' ? std::filesystem::path::preferred_separator : c; });
        return dir / (moduleName + ".agda");
    }


    struct Import {
        Import(const Import&) = delete;
        Import(Import&&)      = delete;
        Import& operator=(const Import&) = delete;
        Import& operator=(Import&&)      = delete;

        Import(std::ofstream& file, std::string_view module) : m_file(file), m_module(module) {}

        Import& as(std::string_view qname) {
            m_qualified = std::string{qname};
            return *this;
        }

        Import& use(std::string_view s) {
            if(!m_opened) throw std::exception{};
            m_usings.emplace_back(s);
            return *this;
        }
        
        Import& rename(std::string_view from, std::string_view to) {
            if(!m_opened) throw std::exception{};
            m_renames.emplace_back(fmt::format("{0} to {1}", from, to));
            return *this;
        }

        Import& open() {
            m_opened = true;
            return *this;
        }

        Import& pub() {
            if(!m_opened) throw std::exception{};
            m_public = true;
            return *this;
        }

        ~Import() {
            if(m_opened) m_file << "open ";
            m_file << "import " << m_module;
            if(m_qualified.has_value()) {
                m_file << " as " << m_qualified.value();
            }
            moded("using", m_usings);
            moded("renaming", m_renames);
            if(m_public) {
                m_file << " public";
            }
            m_file << '\n';
        }

    private:
        std::ofstream& m_file;
        std::string m_module;
        std::vector<std::string> m_usings;
        std::vector<std::string> m_renames;
        std::optional<std::string> m_qualified;
        bool m_opened = false;
        bool m_public = false;

        template<std::ranges::range R, std::same_as<std::ranges::range_value_t<R>> T = std::ranges::range_value_t<R>>
        void moded(const char* mod, const R& defs) {
            for(int i = 0; i < defs.size(); ++i) {
                if(i == 0) {
                    m_file << ' ' << mod << " (";
                }
                m_file << defs[i];
                if(i + 1 < defs.size()) {
                    m_file << "; ";
                }
                else {
                    m_file << ")";
                }
            }
        }
    };
};