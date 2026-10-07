-- Keep the bibliography together without adding layout commands to Markdown.
function Header(h)
  if FORMAT:match('latex') and h.identifier == 'references-and-provenance' then
    return {pandoc.RawBlock('latex', '\\clearpage'), h}
  end
end
