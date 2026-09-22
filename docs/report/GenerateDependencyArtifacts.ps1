param(
  [string]$InputPath = "rate_distortion_dependencies.json",
  [string]$OutputPath = "rate_distortion_dependency_data.js"
)

$ErrorActionPreference = "Stop"

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$inputFile = Join-Path $scriptRoot $InputPath
$outputFile = Join-Path $scriptRoot $OutputPath
$graph = Get-Content -Raw -Encoding UTF8 -LiteralPath $inputFile | ConvertFrom-Json

# Merge statement/proof duplicates while retaining how each edge arose.
$edgeMap = [System.Collections.Specialized.OrderedDictionary]::new()
foreach ($edge in $graph.edges) {
  $key = "$($edge.source)|$($edge.target)"
  if ($edgeMap.Contains($key)) {
    if ($edgeMap[$key].kind -ne $edge.kind) {
      $edgeMap[$key].kind = "both"
    }
  } else {
    $edgeMap.Add($key, [pscustomobject]@{
      source = [string]$edge.source
      target = [string]$edge.target
      kind = [string]$edge.kind
    })
  }
}

$uniqueEdges = @($edgeMap.Values)

function Test-AlternatePath {
  param(
    [string]$Source,
    [string]$Target,
    [int]$SkippedEdge
  )

  $queue = [System.Collections.Generic.Queue[string]]::new()
  $seen = [System.Collections.Generic.HashSet[string]]::new()
  $queue.Enqueue($Source)
  [void]$seen.Add($Source)

  while ($queue.Count -gt 0) {
    $current = $queue.Dequeue()
    for ($index = 0; $index -lt $uniqueEdges.Count; $index++) {
      if ($index -eq $SkippedEdge) {
        continue
      }
      $candidate = $uniqueEdges[$index]
      if ($candidate.source -eq $current -and $seen.Add([string]$candidate.target)) {
        if ($candidate.target -eq $Target) {
          return $true
        }
        $queue.Enqueue([string]$candidate.target)
      }
    }
  }
  return $false
}

# Compute the transitive reduction of the selected-declaration DAG. This removes
# an edge A -> C when the displayed graph already contains a path A -> ... -> C.
$reducedEdges = [System.Collections.Generic.List[object]]::new()
for ($index = 0; $index -lt $uniqueEdges.Count; $index++) {
  $edge = $uniqueEdges[$index]
  if (-not (Test-AlternatePath -Source $edge.source -Target $edge.target -SkippedEdge $index)) {
    $reducedEdges.Add($edge)
  }
}

$graph.edges = @($reducedEdges)
$graph | Add-Member -NotePropertyName rawEdgeCount -NotePropertyValue $uniqueEdges.Count -Force
$graph | Add-Member -NotePropertyName reducedEdgeCount -NotePropertyValue $reducedEdges.Count -Force
$graph | Add-Member -NotePropertyName reduction -NotePropertyValue "transitive reduction of selected declarations" -Force

$json = $graph | ConvertTo-Json -Depth 8 -Compress
$content = "window.RATE_DISTORTION_GRAPH = $json;`n"
Set-Content -Encoding UTF8 -LiteralPath $outputFile -Value $content

Write-Host "Generated $outputFile"
Write-Host "Nodes: $($graph.nodes.Count); unique edges: $($uniqueEdges.Count); reduced edges: $($reducedEdges.Count)"
