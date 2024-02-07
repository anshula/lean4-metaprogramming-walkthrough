import Verso.Genre.Blog
import Walkthrough

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do

    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " — Verso "</title>
          {{← builtinHeader }}
          <link rel="stylesheet" href="/static/style.css"/>
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            <a class="logo" href="/">"Hands-on Lean 4 Tactic Writing"</a>
            {{ ← topNav }}
            </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

-- with CSS and images
-- def demoSite : Site := site Walkthrough.Blog / static "static" ← "website/static_files"  -- copy from static 'website/static_files' to '_out/walkthroughsite/static'

/-- with links -/
def demoSite : Site := site Walkthrough.Blog with --/ static "static" ← "website/static_files"  -- copy from static 'website/static_files' to '_out/walkthroughsite/static'
  Walkthrough.Blog.Introduction
  Walkthrough.Blog.FirstPost
  Walkthrough.Blog.Conditionals

def main := blogMain theme demoSite
