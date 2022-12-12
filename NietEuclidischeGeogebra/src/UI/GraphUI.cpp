#include "GraphUI.h"

#include "Renderer.h"
#include "Application.h"
#include "Util.h"

constexpr int horizontalLineDiff{100};

GraphUI::GraphUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "GraphUI")
{
	equation P2pointDef{ {"p"}, "x = p0 & y = p1 & p0^2 + p1^2 < 1" };
	equation P2lineDef{ {"l"}, "(x-l0)^2 + (y-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2 & l0^2 + l1^2 > 1 & x^2 + y^2 < 1" };
	equation P2incidence{ {"p", "l"}, "(p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	equation P2betweenness{ {"p", "q", "r"}, "((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)" };

	m_Models.push_back(std::make_shared<Model>(2, P2pointDef, 2, P2lineDef, P2incidence, P2betweenness));
	std::shared_ptr<NELine> l1 = std::make_shared<NELine>(std::vector<float>{ 1.25f, 0 }, m_Models[0]);
	std::shared_ptr<NELine> l2 = std::make_shared<NELine>(std::vector<float>{ 0, 1.25f }, m_Models[0]);
	std::shared_ptr<NEPoint> p1 = std::make_shared<NEPoint>(std::vector<float>{ 0.625f,  0.4145780988f }, m_Models[0], RGBColour(255,0,0,255));
	std::shared_ptr<NEPoint> p2 = std::make_shared<NEPoint>(std::vector<float>{ 0.5f, 0 }, m_Models[0], RGBColour(255, 0, 0, 255));
	std::shared_ptr<NEPoint> p3 = std::make_shared<NEPoint>(std::vector<float>{ 0.625f, -0.4145780988f }, m_Models[0], RGBColour(255, 0, 0, 255));


	UpdateLines();
	UpdateGraphs();
}

GraphUI::~GraphUI()
{
}

void GraphUI::RenderPass(Renderer* r)
{
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	for (std::shared_ptr<Graph>& graph : m_Graphs)
	{
		r->AddToRenderQueue(graph);
	}
	UIElement::RenderPass(r);
}

void GraphUI::ResizeWindow(int width, int height)
{
	UpdateLines();
	UpdateGraphs();
	UIElement::ResizeWindow(width, height);
}

void GraphUI::UpdateLines()
{
	m_Lines.clear();
	m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, m_TopY), Point(m_LeftX, m_BottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, m_TopY), Point(m_RightX, m_TopY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(m_RightX, m_BottomY), Point(m_RightX, m_TopY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(m_RightX, m_BottomY), Point(m_LeftX, m_BottomY))); // bottom

	float pixelTopY = Util::ConvertToPixelCoordinate(m_TopY, false);
	float pixelBottomY = Util::ConvertToPixelCoordinate(m_BottomY, false);
	float pixelLeftX = Util::ConvertToPixelCoordinate(m_LeftX, true);
	float pixelRightX = Util::ConvertToPixelCoordinate(m_RightX, true);

	int numHorizontalLines{ (int)((pixelTopY - pixelBottomY) / horizontalLineDiff) };
	for (int i = 0; i < numHorizontalLines; i++)
	{
		float y = m_TopY - i * ((m_TopY - m_BottomY) / numHorizontalLines);
		m_Lines.push_back(std::make_shared<Line>(Point(m_LeftX, y), Point(m_RightX, y), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}

	int numVerticalLines{ (int)((pixelRightX - pixelLeftX) / horizontalLineDiff) };
	for (int i = 0; i < numVerticalLines; i++)
	{
		float x = m_RightX - i * ((m_RightX - m_LeftX) / numVerticalLines);
		m_Lines.push_back(std::make_shared<Line>(Point(x, m_TopY), Point(x, m_BottomY), std::array<float, 4>{0.0f, 0.0f, 0.0f, 1.0f}));
	}
}

void GraphUI::UpdateGraphs()
{
	GraphRenderer* rendPtr = Application::Get()->GetRenderer()->GetGraphRenderer();
	for (std::shared_ptr<Model> m : m_Models) {
		// Add new graphs
		for (NEElement& el : m->getElements()) {
			bool found = false;
			for (std::shared_ptr<Graph> graph: m_Graphs) {
				if (el == graph) { found = true; break; }
			}
			if (!found) {
				m_Graphs.push_back(std::make_shared<Graph>(el, m_LeftX, m_RightX, m_TopY, m_BottomY, -2, 2, 2, -2, el.getColour()));
			}
		}

		// Remove old graphs that no longer exist
		// Go backwards through vector to avoid index shifting when removing element
		for (int i = m_Graphs.size() - 1; i >= 0; --i) {
			std::shared_ptr<Graph> graph = m_Graphs[i];
			bool found = false;
			for (NEElement& el : m->getElements()) {
				if (el == graph) {
					found = true;
					if (el.getColour() != graph->getColour()) {
						graph->setColour(el.getColour());
					}
					break;
				}
			}
			if (!found) {
				m_Graphs.erase(m_Graphs.begin() + i);
			}
			else {
				//Need to regenerate texture because graph moved
				graph->GenTexture(m_LeftX, m_RightX, m_TopY, m_BottomY, -2, 2, 2, -2, rendPtr);
			}
		}
	}
}
