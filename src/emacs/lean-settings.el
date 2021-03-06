;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)

(defgroup lean nil
  "Lean Theorem Prover"
  :prefix "lean-"
  :group 'languages
  :link '(url-link :tag "Website" "http://leanprover.github.io")
  :link '(url-link :tag "Github"  "https://github.com/leanprover/lean"))

(defgroup lean-keybinding nil
  "Keybindings for lean-mode."
  :prefix "lean-"
  :group 'lean)

(defvar-local lean-default-executable-name
  (cl-case system-type
    ('gnu          "lean")
    ('gnu/linux    "lean")
    ('gnu/kfreebsd "lean")
    ('darwin       "lean")
    ('ms-dos       "lean")
    ('windows-nt   "lean.exe")
    ('cygwin       "lean.exe"))
  "Default executable name of Lean")

(defcustom lean-rootdir nil
  "Full pathname of lean root directory. It should be defined by user."
  :group 'lean
  :type 'string)

(defcustom lean-executable-name lean-default-executable-name
  "Name of lean executable"
  :group 'lean
  :type 'string)

(defcustom lean-company-use t
  "Use company mode for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean-company-type-foreground (face-foreground 'font-lock-keyword-face)
  "Color of type parameter in auto-complete candidates"
  :group 'lean
  :type 'color)

(defcustom lean-eldoc-use t
  "Use eldoc mode for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean-eldoc-nay-retry-time 0.3
  "When eldoc-function had nay, try again after this amount of time."
  :group 'lean
  :type 'number)

(defcustom lean-show-only-type-in-parens t
  "Show only types of expression in parens if non-nil. Otherwise,
show both of expressions and types."
  :group 'lean
  :type 'boolean)

(defcustom lean-server-retry-time 0.1
  "Retry interval for event-handler"
  :group 'lean
  :type 'number)

(defcustom lean-server-options nil
  "Additional command line options for the Lean background
   process used to perform tasks such as type information and
   perform auto-completion"
  :group 'lean)

(defcustom lean-flycheck-use t
  "Use flycheck for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean-flycheck-checker-name "linja"
  "lean-flychecker checker name"
  :group 'lean
  :type 'string)

(defcustom lean-flycheck-max-messages-to-display 100
  "Maximum number of flycheck messages to displaylean-flychecker checker name
   (Restart required to be effective)"
  :group 'lean
  :type 'number)

(defcustom lean-default-pp-width 120
  "Width of Lean error/warning messages"
  :group 'lean
  :type 'number)

(defcustom lean-flycheck-msg-width nil
  "Width of Lean error/warning messages"
  :group 'lean
  :type '(choice (const   :tag "Let lean-mode automatically detect this" nil)
                 (integer :tag "Specify the value and force lean-mode to use")))

(defcustom lean-flycheck-checker-options
  `("--keep-going" ,(format "%d" 999)
    "--flycheck"
    "--flycheck-max-messages" ,(format "%d" lean-flycheck-max-messages-to-display))
  "lean-flychecker checker option"
  :group 'lean)

(defcustom lean-delete-trailing-whitespace nil
  "Set this variable to true to automatically delete trailing
whitespace when a buffer is loaded from a file or when it is
written."
  :group 'lean
  :type 'boolean)

(defcustom lean-rule-column 100
  "Specify rule-column."
  :group 'lean
  :type '(choice (integer :tag "Columns")
                 (const :tag "Unlimited" nil)))

(defcustom lean-rule-color "#cccccc"
  "Color used to draw the fill-column rule"
  :group 'fill-column-indicator
  :tag "Fill-column rule color"
  :type 'color)

(defcustom lean-show-rule-column-method nil
  "If enabled, it highlights column"
  :group 'lean
  :type '(choice (const :tag "Disabled" nil)
                 (const :tag "Vertical Line" vline)
                 ;;(const :tag "Whole Lines" lines)
                 ;;(const :tag "Only Beyond lean-rule-column" lines-tail)
                 ))

(defcustom lean-debug-mode-line '(:eval (lean-debug-mode-line-status-text))
  "Mode line lighter for Lean debug mode."
  :group 'lean
  :type 'sexp
  :risky t)

(defcustom lean-show-type-add-to-kill-ring nil
  "If it is non-nil, add the type information to the kill-ring so
that user can yank(paste) it later. By default, it's
false (nil)."
  :group 'lean
  :type 'boolean)

(defcustom lean-show-proofstate-in-minibuffer nil
  "Set this variable to true to show proof state at minibuffer."
  :group 'lean
  :type 'boolean)

(defcustom lean-proofstate-display-style 'show-first-and-other-conclusions
  "Choose how to display proof state in *lean-info* buffer."
  :group 'lean
  :type '(choice (const :tag "Show all goals" show-all)
                 (const :tag "Show only the first" show-first)
                 (const :tag "Show the first goal, and the conclusions of all other goals" show-first-and-other-conclusions)))

(defcustom lean-follow-changes t
  "If it's nil, we don't set up after-change-functions and
  before-change-functions to update the changes to lean-server.
  A usage is to batch-process .org files to .html files"
  :group 'lean
  :type 'boolean)

(defcustom lean-time-to-restart-server 1
  "After lean-time-to-kill-server passed, we restart lean-server if
  the all jobs in the queue are not process."
  :group 'lean
  :type 'number)

(defcustom lean-company-import-timeout 1
  "After lean-company-import-timeout (seconds) passed,
   company-lean--import stops collecting files.
   See the body of company-lean--import-candidates-main"
  :group 'lean
  :type 'number)

(defcustom lean-exec-at-pos-wait-time 0.1
  "When flycheck process is running, wait for
  lean-exec-at-pos-wait-time (seconds) and try to run
  lean-exec-at-pos-with-timer again.
  See the body of lean-exec-at-pos-with-timer"
  :group 'lean
  :type 'number)

(defcustom lean-keybinding-std-exe1 (kbd "C-c C-x")
  "Lean Keybinding for std-exe #1"
  :group 'lean-keybinding :type 'key-sequence)
(defcustom lean-keybinding-std-exe2 (kbd "C-c C-l")
  "Lean Keybinding for std-exe #2"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-show-key (kbd "C-c C-k")
  "Lean Keybinding for show-key"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-set-option (kbd "C-c C-o")
  "Lean Keybinding for set-option"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-eval-cmd (kbd "C-c C-e")
  "Lean Keybinding for eval-cmd"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-show-type (kbd "C-c C-t")
  "Lean Keybinding for show-type"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-fill-placeholder (kbd "C-c C-f")
  "Lean Keybinding for fill-placeholder"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-server-restart-process (kbd "C-c C-r")
  "Lean Keybinding for server-restart-process"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-find-tag (kbd "M-.")
  "Lean Keybinding for find-tag"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-tab-indent-or-complete (kbd "TAB")
  "Lean Keybinding for tab-indent-or-complete"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-lean-show-goal-at-pos (kbd "C-c C-g")
  "Lean Keybinding for show-goal-at-pos"
  :group 'lean-keybinding  :type 'key-sequence)
(defcustom lean-keybinding-lean-show-id-keyword-info (kbd "C-c C-p")
  "Lean Keybinding for show-id-keyword-info"
  :group 'lean-keybinding  :type 'key-sequence)
(provide 'lean-settings)
