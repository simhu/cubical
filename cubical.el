;; define several class of keywords
(setq cub-keywords '("data" "import" "mutual" "let" "in" "split" "hsplit"
		     "with" "module" "where" "U") )
(setq cub-special '("undefined" "primitive"))

;; create regex strings
(setq cub-keywords-regexp (regexp-opt cub-keywords 'words))
(setq cub-operators-regexp (regexp-opt '(":" "->" "=" "\\" "|" "\\" "*" "_") t))
(setq cub-special-regexp (regexp-opt cub-special 'words))
(setq cub-def-regexp "^[[:word:]]+")

;; clear memory
(setq cub-keywords nil)
(setq cub-special nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq cub-font-lock-keywords
  `(
    (,cub-keywords-regexp . font-lock-type-face)
    (,cub-operators-regexp . font-lock-variable-name-face)
    (,cub-special-regexp . font-lock-warning-face)
    (,cub-def-regexp . font-lock-function-name-face)
))

;; command to comment/uncomment text
(defun cub-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way. For detail, see `comment-dwim'."
  (interactive "*P")
  (require 'newcomment)
  (let ((comment-start "--") (comment-end ""))
    (comment-dwim arg)))


;; syntax table for comments, same as for haskell-mode
(defvar cub-syntax-table
  (let ((st (make-syntax-table)))
       (modify-syntax-entry ?\{  "(}1nb" st)
       (modify-syntax-entry ?\}  "){4nb" st)
       (modify-syntax-entry ?-  "_ 123" st)
       (modify-syntax-entry ?\n ">" st)
   st))

;; define the mode
(define-derived-mode cub-mode fundamental-mode
  "cubical mode"
  "Major mode for editing cubical files…"

  :syntax-table cub-syntax-table

  ;; code for syntax highlighting
  (setq font-lock-defaults '(cub-font-lock-keywords))
  (setq mode-name "cub")

  ;; modify the keymap
  (define-key cub-mode-map [remap comment-dwim] 'cub-comment-dwim)

  ;; clear memory
  (setq cub-keywords-regexp nil)
  (setq cub-operators-regexp nil)
  (setq cub-special-regexp nil)
)

(provide 'cub-mode)
