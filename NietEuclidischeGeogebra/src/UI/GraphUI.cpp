#include "GraphUI.h"

#include "Renderer.h"
#include "Application.h"
#include "Util.h"

constexpr int horizontalLineDiff{100};

GraphUI::GraphUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "GraphUI")
{
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
	equation P2pointDef{ {"p"}, "x = p0 & y = p1 & p0^2 + p1^2 < 1" };
	equation P2lineDef{ {"l"}, "(x-l0)^2 + (y-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2 & l0^2 + l1^2 > 1 & x^2 + y^2 < 1" };
	equation P2incidence{ {"p", "l"}, "(p0-l0)^2 + (p1-l1)^2 = (1 / (-2*(2~(l0^2+l1^2))-2*2~((2~(l0^2+l1^2))^2-1)) + 0.5*(2~(l0^2+l1^2)) + 0.5* 2~((2~(l0^2+l1^2))^2-1))^2" };
	equation P2betweenness{ {"p", "q", "r"}, "((p0 - r0)^2 + (p1 - r1)^2 > (p0 - q0)^2 + (p1 - q1)^2) & ((p0 - r0)^2 + (p1 - r1)^2 > (r0 - q0)^2 + (r1 - q1)^2)" };

	Model P2m(2, P2pointDef, 2, P2lineDef, P2incidence, P2betweenness);
	NELine l1({ 1.25, 0 }, &P2m);
	NELine l2({0, 1.25}, &P2m);
	NEPoint p1({ 0.625,  0.4145780988 }, &P2m, Colour(255,0,0,255));
	NEPoint p2({ 0.5, 0 }, &P2m, Colour(255, 0, 0, 255));
	NEPoint p3({ 0.625, -0.4145780988 }, &P2m, Colour(255, 0, 0, 255));

	std::vector<Model*> m_Models = { &P2m };

	m_Graphs.clear();
	for (Model* m : m_Models) {
		for (NEElement el : m->getElements()) {
			Colour colour = el.getColour();
			m_Graphs.push_back(std::make_shared<Graph>(el, m_LeftX, m_RightX, m_TopY, m_BottomY, -2, 2, 2, -2, std::array<float, 4>{colour.norm_r, colour.norm_g, colour.norm_b, colour.norm_a}));
		}
	}

	Renderer* r = Application::Get()->GetRenderer();
	for (std::shared_ptr<Graph>& graph : m_Graphs)
	{
		r->GenTexture(graph);
	}
}
