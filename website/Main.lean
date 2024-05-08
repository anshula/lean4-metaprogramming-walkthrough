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
          <title>{{ (← param (α := String) "title") }} " — Hands-on Lean 4 Tactic Writing"</title>
          {{← builtinHeader }}
          <link rel="icon" type="image/x-icon" href="/static/img/favicon.ico"/>
          <link rel="stylesheet" href="/static/style.css"/>
          <link rel="stylesheet" href="/static/navbar.css"/>
          <link rel="stylesheet" href="/static/navbar-colors.css"/>
          <script crossorigin="anonymous" src="https://code.jquery.com/jquery-2.2.4.js"></script>
          <script src="/static/build-nav.js"></script>
          <script>"window.onload=function(){buildNav();}"</script>
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
def demoSite : Site := site Walkthrough.Blog._1_Introduction /
  static "static" ← "website/static_files"
  "Introduction" Walkthrough.Blog._1_Introduction
  "Reading-and-Changing-the-Goal" Walkthrough.Blog.ReadingAndChangingTheGoal
  "Reading-and-Changing-the-Hypotheses" Walkthrough.Blog.ReadingAndChangingTheHypotheses
  "Adding-Goals-and-Hypotheses" Walkthrough.Blog.AddingGoalsAndHypotheses


def main := blogMain theme demoSite
