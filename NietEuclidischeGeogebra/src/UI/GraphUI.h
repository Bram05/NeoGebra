// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "GraphRenderer.h"
#include "Model.h"

class GraphUI : public UIElement
{
public:
	GraphUI(float leftX, float rightX, float topY, float bottomY);
	~GraphUI();

protected:
	void RenderPass(Renderer* r) override;
	void ResizeWindow(int width, int height) override;

	virtual void WasClicked(float x, float y) override;
	virtual void DraggedUpdate(float x, float y) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::vector<std::shared_ptr<Graph>> m_Graphs;
	std::vector<std::shared_ptr<Model>> m_Models;

	float m_MidCoordX, m_MidCoordY, m_UnitLengthPixels;
	float m_MidCoordXBeforeDrag, m_MidCoordYBeforeDrag;
	float m_XBeforeDrag, m_YBeforeDrag;

	void UpdateLines();
	void UpdateGraphs();
};