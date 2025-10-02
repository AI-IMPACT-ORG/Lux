# Modular Generator Architecture

## Overview

The generator has been refactored into a clean, modular architecture with clear separation between generic and language-specific components.

## Architecture

### Core Files

1. **`main-generator.rkt`** - Single entry point with command-line interface
2. **`generic-generator.rkt`** - Generic generation logic shared across languages
3. **`language-configs.rkt`** - Language-specific configurations and settings
4. **`language-extensions.rkt`** - Advanced language-specific features and deployments
5. **`generate.rkt`** - Simple wrapper script for easy execution

### Key Features

- **Single Entry Point**: One command to generate all or specific languages
- **Modular Design**: Clear separation between generic and language-specific code
- **Flexible Deployment**: Language-specific build scripts and project files
- **Command Line Interface**: Easy-to-use CLI with multiple options
- **Extensible**: Easy to add new languages or customize existing ones

## Usage

### Basic Usage

```bash
# Generate all languages
racket generate.rkt

# Generate specific language
racket generate.rkt -t coq

# Generate with verbose output
racket generate.rkt -t lean -v

# Generate with deployment files
racket generate.rkt -t coq --deploy

# Test compilation after generation
racket generate.rkt -t all --test
```

### Command Line Options

- `-t, --target <LANG>`: Target language (coq|agda|lean|isabelle|all)
- `-o, --output <DIR>`: Output directory (default: "formal")
- `-v, --verbose`: Verbose output
- `--test`: Test compilation after generation
- `--deploy`: Create deployment files (Makefiles, project files)
- `--help`: Show help

### Examples

```bash
# Generate Coq library with deployment files
racket generate.rkt -t coq -o my-coq-lib --deploy -v

# Generate all languages and test compilation
racket generate.rkt -t all --test -v

# Generate Lean library to specific directory
racket generate.rkt -t lean -o ../my-lean-lib
```

## Architecture Details

### Generic Components

- **Module Generation**: Core, Observers, Kernels, NormalForms, Main
- **Code Generation**: Functions, axioms, inductive types, comments
- **File Management**: Output directory structure, file naming
- **Project Files**: Basic project file generation

### Language-Specific Components

- **Syntax**: Language-specific syntax for functions, types, imports
- **Naming**: Identifier cleaning and constructor naming rules
- **Module Headers**: Language-specific import and module declarations
- **File Extensions**: Language-specific file extensions and prefixes
- **Deployment**: Build scripts, Makefiles, project configurations

### Extension Points

- **Custom Modules**: Add language-specific modules
- **Deployment Configs**: Customize build and test commands
- **Project Files**: Add language-specific project files
- **Build Scripts**: Generate custom build scripts

## File Structure

```
codegen/
├── main-generator.rkt      # Main entry point
├── generic-generator.rkt    # Generic generation logic
├── language-configs.rkt    # Language configurations
├── language-extensions.rkt  # Language-specific extensions
├── generate.rkt           # Wrapper script
└── unified-library-generator.rkt  # Legacy (deprecated)
```

## Generated Output

Each language generates:
- **Core Module**: Basic types and operations
- **Observers Module**: Observer functions
- **Kernels Module**: Kernel operations
- **NormalForms Module**: Normal form operations
- **Main Module**: Unified interface
- **Project Files**: Language-specific project files (when using --deploy)

## Benefits

1. **Maintainability**: Clear separation of concerns
2. **Extensibility**: Easy to add new languages or features
3. **Flexibility**: Language-specific customizations
4. **Usability**: Simple command-line interface
5. **Deployment**: Ready-to-use build scripts and project files
